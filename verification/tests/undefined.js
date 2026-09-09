"use strict";
// Fresh producer claims, independent consumers, exact profile mirroring, and
// negative candidates. Runtime checks distinguish null, undefined and false.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const vm = require("node:vm");
const { spawnSync } = require("node:child_process");
const { performance } = require("node:perf_hooks");
const ts = require("../tools/node_modules/typescript");
const { fromSourceClaims } = require("../tools/annotate-source");
const profile = require("../tools/source-profile");
const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath));
const claims = JSON.parse(fs.readFileSync(claimsPath));
const source = fs.readFileSync(file, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "undefined-tests-"));
const evidence = path.join(tmp, "evidence.json");
const normalized = path.join(tmp, "claims.json");
let passed = 0;
const run = (exe, args, cwd) => {
  const r = spawnSync(exe, args, {
    cwd,
    encoding: "utf8",
    timeout: 60000,
    maxBuffer: 32 * 1024 * 1024,
  });
  assert(!r.error, String(r.error));
  return r;
};
const accepted = (r) => assert.equal(r.status, 0, r.stderr);
const test = (name, f) => {
  f();
  passed++;
  console.log(`  ${name}: OK`);
};
const produce = (ap = astPath, cp = claimsPath, mode = "stateful-source") =>
  run(verifier, [`--produce-${mode}`, ap, cp, file, evidence, "10"]);
const check = (mode, cp) =>
  run(verifier, [`--check-${mode}`, astPath, cp, file, evidence]);
try {
  test("display table equals all 532 maintained Lean labels", () => {
    const r = run(
      "lake",
      ["env", "lean", "--run", path.resolve(__dirname, "source-profile.lean")],
      path.resolve(__dirname, "../lean"),
    );
    accepted(r);
    assert.deepEqual(JSON.parse(r.stdout), profile.types);
    assert.equal(profile.types.length, 532);
    assert.equal(profile.typeText([75]), "undefined");
  });
  test("all undefined functions have complete normal-mode producer claims", () => {
    const functions = claims.find((c) => c.file === file).functions;
    assert.equal(functions.length, ast.functions.length);
    assert(
      functions.every(
        (f) =>
          f.collection.completion === "complete" &&
          f.collection.mode === "normal",
      ),
    );
  });
  const start = performance.now();
  test("references, arrows, guards and coalescing produce checked evidence", () =>
    accepted(produce()));
  const produceMs = performance.now() - start;
  const checkedAt = performance.now();
  test("independent raw consumer accepts", () =>
    accepted(check("stateful-source", claimsPath)));
  const checkMs = performance.now() - checkedAt;
  test("undefined exports and round-trips through the neutral profile", () => {
    const r = run(process.execPath, [
      path.resolve(__dirname, "../tools/export-source-claims.js"),
      file,
      "--claims",
      claimsPath,
      "--out",
      normalized,
      "--verifier",
      verifier,
    ]);
    accepted(r);
    const doc = JSON.parse(fs.readFileSync(normalized));
    assert.equal(doc.profile, profile.name);
    const identity = doc.functions.find((f) => f.name === "undefinedIdentity");
    assert.deepEqual(identity.params[0].type, [75]);
    assert.deepEqual(identity.result, [75]);
    const shown = fromSourceClaims(source, file, doc, "candidate");
    assert.equal(
      shown.functions.find((f) => f.name === identity.name).signature.retType,
      "undefined",
    );
    accepted(check("source-claims", normalized));
    accepted(produce(astPath, normalized, "source-claims"));
    accepted(check("stateful-source", claimsPath));
  });
  function candidate(name, edit) {
    const doc = JSON.parse(fs.readFileSync(normalized));
    doc.functions = doc.functions.filter((f) => f.name === name);
    const a = {
      ...ast,
      functions: ast.functions.filter((f) => f.name === name),
    };
    edit(doc.functions[0], a.functions[0]);
    const ap = path.join(tmp, "candidate.ast.json"),
      cp = path.join(tmp, "candidate.claims.json");
    fs.writeFileSync(ap, JSON.stringify(a));
    fs.writeFileSync(cp, JSON.stringify(doc));
    return { doc, ap, cp };
  }
  function rejects(c) {
    const r = produce(c.ap, c.cp, "source-claims");
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /evidence search failed/);
  }
  test("a claim cannot erase undefined from a live input union", () =>
    rejects(
      candidate("undefinedUnion", (f, a) => {
        f.entries.find((e) => e.start === a.body[0].pos[0]).bindings[0].type = [
          0, 1, 2,
        ];
      }),
    ));
  test("null testing does not justify an undefined branch claim", () =>
    rejects(
      candidate("nullIsDifferent", (f, a) => {
        const ret = a.body.at(-1);
        f.entries.find((e) => e.start === ret.pos[0]).bindings[0].type = [0];
      }),
    ));
  test("a precise undefined read requires a supplied current observation", () => {
    const c = candidate("undefinedCurrent", (f, a) => {
      const ret = a.body.at(-1);
      f.expressions.find((e) => String(e.pos) === String(ret.e.pos)).type = [
        75,
      ];
    });
    rejects(c);
    const f = c.doc.functions[0],
      ret = ast.functions
        .find((f) => f.name === "undefinedCurrent")
        .body.at(-1);
    f.entries
      .find((e) => e.start === ret.pos[0])
      .bindings.find((b) => b.name === "cell").current = [75];
    fs.writeFileSync(c.cp, JSON.stringify(c.doc));
    accepted(produce(c.ap, c.cp, "source-claims"));
    f.entries
      .find((e) => e.start === ret.pos[0])
      .bindings.find((b) => b.name === "cell").current = [1];
    fs.writeFileSync(c.cp, JSON.stringify(c.doc));
    rejects(c);
  });
  test("an undefined-bearing observation survives raw-to-neutral conversion", () => {
    const raw = structuredClone(claims);
    const f = raw
      .find((f) => f.file === file)
      .functions.find((f) => f.name === "undefinedCurrent");
    const ret = ast.functions
      .find((f) => f.name === "undefinedCurrent")
      .body.at(-1);
    f.envs
      .find((e) => e.pos[0] === ret.pos[0])
      .vars.find((b) => b.name === "cell").type.atoms[0].fields[0].read = {
      top: false,
      atoms: [{ a: "undefined" }],
    };
    const cp = path.join(tmp, "observed.raw.json"),
      out = path.join(tmp, "observed.json");
    fs.writeFileSync(cp, JSON.stringify(raw));
    accepted(
      run(process.execPath, [
        path.resolve(__dirname, "../tools/export-source-claims.js"),
        file,
        "--claims",
        cp,
        "--out",
        out,
        "--verifier",
        verifier,
      ]),
    );
    const doc = JSON.parse(fs.readFileSync(out));
    const b = doc.functions
      .find((f) => f.name === "undefinedCurrent")
      .entries.find((e) => e.start === ret.pos[0])
      .bindings.find((b) => b.name === "cell");
    assert.deepEqual(b.current, [75]);
    assert.deepEqual(profile.types[b.type[0]], [
      { refs: { first: [1, 2, 75], rest: [] } },
    ]);
    accepted(produce(astPath, cp));
    accepted(check("source-claims", out));
  });
  test("runtime distinguishes null and undefined, preserves false, and evaluates the fallback only when needed", () => {
    const context = vm.createContext({});
    vm.runInContext(
      ts.transpileModule(source, {
        compilerOptions: { target: ts.ScriptTarget.ES2022 },
      }).outputText,
      context,
    );
    for (const v of [null, undefined, false, true]) {
      assert.equal(context.undefinedUnion(v), v);
      assert.equal(context.undefinedCoalesce(v), v ?? false);
    }
    for (const v of [undefined, false, true]) {
      assert.equal(context.undefinedAlias(v), undefined);
      assert.equal(context.undefinedCallback(v), v);
      assert.equal(context.undefinedBranch(v), v ?? false);
      assert.equal(context.reversedUndefined(v), v ?? false);
      assert.equal(context.undefinedClosure(v), v ?? false);
      assert.equal(context.undefinedFallback(v), v !== undefined);
    }
    assert.equal(context.nullIsDifferent(null), undefined);
    assert.equal(context.nullIsDifferent(undefined), undefined);
  });
  test("shadowed undefined and adjacent unsupported syntax fail explicitly", () => {
    for (const text of [
      "function f(undefined: boolean): undefined { return undefined; }",
      "function undefined(): undefined { return undefined; }",
      "function f(): undefined { const undefined: boolean = true; return undefined; }",
      "function f(): undefined { const g = (undefined: boolean): undefined => undefined; return g(true); }",
      "function f(): void { return; }",
      "function f(x: { value?: boolean }): boolean { return true; }",
      "function f(): boolean { return; }",
    ]) {
      const input = path.join(tmp, "boundary.ts");
      fs.writeFileSync(input, text);
      const result = run(process.execPath, [
        path.resolve(__dirname, "../tools/parse-source.js"),
        input,
      ]);
      assert.notEqual(result.status, 0, text);
      if (text.includes("undefined"))
        assert.match(result.stderr, /shadowing undefined/);
    }
  });
  test("the fixture also passes strict TypeScript checking", () => {
    const program = ts.createProgram([file], {
      strict: true,
      noEmit: true,
      target: ts.ScriptTarget.ES2022,
    });
    assert.deepEqual(
      ts
        .getPreEmitDiagnostics(program)
        .map((d) => ts.flattenDiagnosticMessageText(d.messageText, "\n")),
      [],
    );
  });
  console.log(
    `Undefined: ${passed} passed; ${ast.functions.length} functions, production ${Math.round(produceMs)}ms, independent check ${Math.round(checkMs)}ms`,
  );
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
