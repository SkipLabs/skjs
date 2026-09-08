#!/usr/bin/env node
"use strict";
// Classify the two producer witnesses independently of verifier acceptance.
// The complete safe body also has a Lean proof in WriteRefinedRead.lean; the
// source checker also consumes the generated heap-aware graph certificate.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const vm = require("node:vm");
const ts = require("../tools/node_modules/typescript");
const { fromSkjs, verifySkjs } = require("../tools/annotate-source.js");
const [
  safeAstPath,
  safeClaimsPath,
  safeFile,
  badAstPath,
  badClaimsPath,
  badFile,
  verifier,
] = process.argv.slice(2);
const load = (p) => JSON.parse(fs.readFileSync(p));
const safeAst = load(safeAstPath),
  safeClaims = load(safeClaimsPath);
const badAst = load(badAstPath),
  badClaims = load(badClaimsPath);
const claim = (cs, file, name = "writeRefinedRead") =>
  cs.find((c) => c.file === file).functions.find((f) => f.name === name);
const at = (f, pos) =>
  f.exprs.find((e) => JSON.stringify(e.pos) === JSON.stringify(pos));
const bool = { top: false, atoms: [{ a: "boolean" }] };
const lit = (v) => ({ top: false, atoms: [{ a: "booleanlit", v: String(v) }] });
let passed = 0;
function test(name, f) {
  f();
  passed++;
  console.log(`  ${name}: OK`);
}
function runtime(file) {
  const context = vm.createContext({});
  vm.runInContext(
    ts.transpileModule(fs.readFileSync(file, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022 },
    }).outputText,
    context,
  );
  return context;
}
function check(file, claims, name = "writeRefinedRead") {
  const source = fs.readFileSync(file, "utf8");
  const results = verifySkjs(
    file,
    source,
    claims,
    file,
    fromSkjs(source, file, claims, "skjs"),
    verifier,
    10,
  ).results;
  return results[
    claims
      .find((f) => f.file === file)
      .functions.findIndex((f) => f.name === name)
  ];
}
function stripPositions(x) {
  if (Array.isArray(x)) return x.map(stripPositions);
  if (x && typeof x === "object")
    return Object.fromEntries(
      Object.entries(x)
        .filter(([key]) => !["pos", "namePos"].includes(key))
        .map(([k, v]) => [k, stripPositions(v)]),
    );
  return x;
}

test("safe source matches the allocate/write/read body proved in Lean", () => {
  const f = safeAst.functions[0],
    cell = f.body[0];
  assert.equal(f.name, "writeRefinedRead");
  assert.deepEqual(f.params, []);
  assert.deepEqual(f.retType, lit(true));
  assert.deepEqual(cell.annot.atoms[0].fields, [
    { name: "value", optional: false, read: bool, write: bool },
  ]);
  assert.deepEqual(stripPositions(f.body), [
    {
      k: "const",
      name: "cell",
      annot: cell.annot,
      init: {
        k: "alloc",
        e: { k: "lit", lit: { a: "booleanlit", v: "false" } },
      },
    },
    {
      k: "effect",
      e: {
        k: "write",
        receiver: { k: "id", name: "cell" },
        rhs: { k: "lit", lit: { a: "booleanlit", v: "true" } },
      },
    },
    { k: "return", e: { k: "read", e: { k: "id", name: "cell" } } },
  ]);
});
test("normal first-error export contains the imprecise Boolean read", () => {
  const f = claim(safeClaims, safeFile);
  assert.equal(f.collection.completion, "aborted");
  assert.equal(f.collection.mode, "normal");
  assert.equal(f.collection.quality, "unverified");
  assert.deepEqual(at(f, safeAst.functions[0].body[2].e.pos).type, bool);
});
test("runtime results establish the two classifications", () => {
  assert.equal(runtime(safeFile).writeRefinedRead(), true);
  const bad = runtime(badFile);
  assert.equal(bad.staleFlip(null), false);
  assert.equal(bad.staleFlip(true), true);
  assert.equal(bad.staleFlip(false), true);
});
test("TypeScript accepts the safe function and rejects the stale false return", () => {
  const program = ts.createProgram([safeFile, badFile], {
    strict: true,
    noEmit: true,
    target: ts.ScriptTarget.ES2022,
  });
  const errors = ts
    .getPreEmitDiagnostics(program)
    .filter((d) => d.category === ts.DiagnosticCategory.Error);
  assert.equal(
    errors.length,
    2,
    ts.formatDiagnostics(errors, {
      getCanonicalFileName: (x) => x,
      getCurrentDirectory: () => process.cwd(),
      getNewLine: () => "\n",
    }),
  );
  assert(errors.every((e) => e.file.fileName === badFile && e.code === 2322));
  const flipped = errors.find((e) =>
    ts
      .flattenDiagnosticMessageText(e.messageText, "\n")
      .includes("Type 'true'"),
  );
  assert(flipped);
  assert.match(
    ts.flattenDiagnosticMessageText(flipped.messageText, "\n"),
    /Type 'true' is not assignable to type 'false'/,
  );
});
test("accepted negated-guard export retains a false read after a true write", () => {
  const f = claim(badClaims, badFile, "staleFlip"),
    loop = badAst.functions.find((f) => f.name === "staleFlip").body[1];
  assert.equal(f.collection.completion, "complete");
  assert.equal(f.collection.mode, "normal");
  assert.deepEqual(f.retType, lit(false));
  assert.deepEqual(loop.body[0].e.rhs.lit, { a: "booleanlit", v: "true" });
  assert.deepEqual(at(f, loop.body[1].e.pos).type, lit(false));
  const exit = f.envs.at(-1).vars.find((v) => v.name === "cell").type;
  assert.equal(exit.atoms.length, 2);
  assert(exit.atoms.every((a) => a.a === "record"));
});
test("negated witness reaches a checked obligation with its original observations", () => {
  const r = check(badFile, badClaims, "staleFlip");
  assert.equal(r.status, "not-established");
  assert.equal(r.obligation.phase, "proof-search");
});
test("original and precise read claims verify through checked write postconditions", () => {
  const candidate = structuredClone(safeClaims);
  at(claim(candidate, safeFile), safeAst.functions[0].body[2].e.pos).type =
    lit(true);
  for (const cs of [safeClaims, candidate]) {
    const r = check(safeFile, cs);
    assert.equal(r.status, "verified", r.detail);
  }
});
test("a false read claim cannot override the actual written value", () => {
  const candidate = structuredClone(safeClaims);
  at(claim(candidate, safeFile), safeAst.functions[0].body[2].e.pos).type =
    lit(false);
  const r = check(safeFile, candidate);
  assert.equal(r.status, "not-established");
  assert.equal(r.obligation.phase, "proof-search");
});

console.log(`Write observations: ${passed} passed, 0 failed`);
