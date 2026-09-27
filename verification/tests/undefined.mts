import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { performance } from "node:perf_hooks";
import { stripTypes } from "../tools/strip-types.mts";
import { typeErrors } from "../tools/type-errors.mts";
import { fromSourceClaims } from "../tools/annotate-source.mts";
import type { Ast, FunctionAst } from "../tools/fragment.mts";
import type { Labels } from "../tools/type-graph.mts";
import type { FunctionClaims, SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import {
  atom,
  claimType,
  fn as functionIn,
  last,
  must,
  stmt,
} from "./edits.mts";
const __dirname = path.dirname(import.meta.filename);
// Fresh producer claims, independent consumers, exact format mirroring, and
// negative candidates. Runtime checks distinguish null, undefined and false.










const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const source = fs.readFileSync(file, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "undefined-tests-"));
const evidence = path.join(tmp, "evidence.json");
const normalized = path.join(tmp, "claims.json");
let passed = 0;
/** One normalized function, one of its entries, one binding of that entry. */
const stated = (d: SourceClaims, name: string) =>
  must(d.functions.find((f) => f.name === name), `claims for ${name}`);
const entryOf = (f: FunctionClaims, start: number) =>
  must(f.entries.find((e) => e.start === start), `an entry at ${start}`);
const bindingOf = (f: FunctionClaims, start: number, name: string) =>
  must(entryOf(f, start).bindings.find((b) => b.name === name), `a claim for ${name}`);
const run = (exe: string, args: string[], cwd?: string) => {
  const r = spawnSync(exe, args, {
    cwd,
    encoding: "utf8",
    timeout: 60000,
    maxBuffer: 32 * 1024 * 1024,
  });
  assert(!r.error, String(r.error));
  return r;
};
const accepted = (r: { status: number | null; stderr: string }) =>
  assert.equal(r.status, 0, r.stderr);
const test = (name: string, f: () => void) => {
  f();
  passed++;
  console.log(`  ${name}: OK`);
};
const produce = (ap = astPath, cp = claimsPath, mode = "stateful-source") =>
  run(verifier, [`--produce-${mode}`, ap, cp, file, evidence, "10"]);
const check = (mode: string, cp: string) =>
  run(verifier, [`--check-${mode}`, astPath, cp, file, evidence]);
try {
  test("all undefined functions have complete normal-mode producer claims", () => {
    const functions = fileOf(claims, file).functions;
    assert.equal(functions.length, ast.functions.length);
    assert(
      functions.every(
        (f) =>
          f.collection?.completion === "complete" &&
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
  test("undefined exports and round-trips through the neutral sidecar", () => {
    const r = run(process.execPath, [
      path.resolve(__dirname, "../tools/export-source-claims.mts"),
      file,
      "--claims",
      claimsPath,
      "--out",
      normalized,
      "--verifier",
      verifier,
    ]);
    accepted(r);
    const doc: SourceClaims = JSON.parse(fs.readFileSync(normalized, "utf8"));
    // The table starts with the primitives and holds one row per compound
    // type the fixture mentions, each a single clause over earlier labels.
    assert.deepEqual(doc.types.slice(0, 4), [
      ["nul"],
      [{ boolLit: { value: true } }],
      [{ boolLit: { value: false } }],
      ["undef"],
    ]);
    assert(doc.types.length > 4 && doc.types.length < 20, String(doc.types.length));
    for (const [i, row] of doc.types.entries()) {
      assert.equal(row.length, 1);
      const clause = must(row[0], "a clause");
      const operands: Labels[] =
        typeof clause === "string"
          ? []
          : "refs" in clause
            ? [clause.refs.first, ...clause.refs.rest].flatMap((fs) => fs.map(([, ls]) => ls))
            : "arrs" in clause
              ? clause.arrs.arrows.flatMap((s) => [s.receiver, ...s.arguments, s.result])
              : [];
      assert(
        operands.every((A) => A.every((j) => j < i)),
        JSON.stringify(row),
      );
    }
    assert.equal(
      new Set(doc.types.map((row) => JSON.stringify(row))).size,
      doc.types.length,
    );
    const identity = stated(doc, "undefinedIdentity");
    assert.deepEqual(must(identity.params[0], "a parameter").type, [3]);
    assert.deepEqual(identity.result, [3]);
    const shown = fromSourceClaims(source, file, doc, "candidate");
    assert.equal(
      must(
        shown.functions.find((f) => f.name === identity.name),
        "the shown function",
      ).signature?.retType,
      "undefined",
    );
    accepted(check("source-claims", normalized));
    accepted(produce(astPath, normalized, "source-claims"));
    accepted(check("stateful-source", claimsPath));
  });
  function candidate(
    name: string,
    edit: (f: FunctionClaims, a: FunctionAst) => void,
  ) {
    const doc: SourceClaims = JSON.parse(fs.readFileSync(normalized, "utf8"));
    doc.functions = doc.functions.filter((f) => f.name === name);
    const a = {
      ...ast,
      functions: ast.functions.filter((f) => f.name === name),
    };
    edit(must(doc.functions[0], "the candidate"), functionIn(a, name));
    const ap = path.join(tmp, "candidate.ast.json"),
      cp = path.join(tmp, "candidate.claims.json");
    fs.writeFileSync(ap, JSON.stringify(a));
    fs.writeFileSync(cp, JSON.stringify(doc));
    return { doc, ap, cp };
  }
  function rejects(c: { ap: string; cp: string }) {
    const r = produce(c.ap, c.cp, "source-claims");
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /evidence search failed/);
  }
  test("a claim cannot erase undefined from a live input union", () =>
    rejects(
      candidate("undefinedUnion", (f, a) => {
        must(entryOf(f, must(a.body[0], "a statement").pos[0]).bindings.find((b) => b.name === "value"), "the value binding")
          .type = [0, 1, 2];
      }),
    ));
  test("null testing does not justify an undefined branch claim", () =>
    rejects(
      candidate("nullIsDifferent", (f, a) => {
        must(entryOf(f, last(a.body).pos[0]).bindings.find((b) => b.name === "value"), "the value binding").type = [0];
      }),
    ));
  test("a precise undefined read requires a supplied current observation", () => {
    const c = candidate("undefinedCurrent", (f, a) => {
      const ret = stmt(last(a.body), "return");
      must(
        f.expressions.find((e) => String(e.pos) === String(ret.e.pos)),
        "a claim at the return",
      ).type = [3];
    });
    rejects(c);
    const f = must(c.doc.functions[0], "the candidate");
    const ret = last(functionIn(ast, "undefinedCurrent").body);
    bindingOf(f, ret.pos[0], "cell").current = [["value", [3]]];
    fs.writeFileSync(c.cp, JSON.stringify(c.doc));
    accepted(produce(c.ap, c.cp, "source-claims"));
    bindingOf(f, ret.pos[0], "cell").current = [["value", [1]]];
    fs.writeFileSync(c.cp, JSON.stringify(c.doc));
    rejects(c);
  });
  test("an undefined-bearing observation survives raw-to-neutral conversion", () => {
    const raw = structuredClone(claims);
    const f = functionOf(raw, file, "undefinedCurrent");
    const ret = last(functionIn(ast, "undefinedCurrent").body);
    const held = must(
      must(f.envs.find((e) => e.pos[0] === ret.pos[0]), "an entry")
        .vars.find((b) => b.name === "cell"),
      "the cell's claim",
    );
    must(atom(claimType(held).atoms[0], "record").fields[0], "a field").read = {
      top: false,
      atoms: [{ a: "undefined" }],
    };
    const cp = path.join(tmp, "observed.raw.json"),
      out = path.join(tmp, "observed.json");
    fs.writeFileSync(cp, JSON.stringify(raw));
    accepted(
      run(process.execPath, [
        path.resolve(__dirname, "../tools/export-source-claims.mts"),
        file,
        "--claims",
        cp,
        "--out",
        out,
        "--verifier",
        verifier,
      ]),
    );
    const doc: SourceClaims = JSON.parse(fs.readFileSync(out, "utf8"));
    const b = bindingOf(stated(doc, "undefinedCurrent"), ret.pos[0], "cell");
    assert.deepEqual(b.current, [["value", [3]]]);
    const labels = b.type;
    assert(Array.isArray(labels));
    assert.deepEqual(doc.types[must(labels[0], "a label")], [
      { refs: { first: [["value", [1, 2, 3]]], rest: [], views: [] } },
    ]);
    accepted(produce(astPath, cp));
    accepted(check("source-claims", out));
  });
  test("runtime distinguishes null and undefined, preserves false, and evaluates the fallback only when needed", () => {
    const context = vm.createContext({});
    vm.runInContext(
      stripTypes(source),
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
      "function f(): boolean { return; }",
    ]) {
      const input = path.join(tmp, "boundary.ts");
      fs.writeFileSync(input, text);
      const result = run(process.execPath, [
        path.resolve(__dirname, "../tools/fragment-parse.mts"),
        input,
      ]);
      assert.notEqual(result.status, 0, text);
      if (text.includes("undefined"))
        assert.match(result.stderr, /shadowing undefined/);
    }
  });
  test("the fixture also passes strict TypeScript checking", () => {
    assert.deepEqual(
      typeErrors(file).map((d) => d.text),
      [],
    );
  });
  console.log(
    `Undefined: ${passed} passed; ${ast.functions.length} functions, production ${Math.round(produceMs)}ms, independent check ${Math.round(checkMs)}ms`,
  );
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
