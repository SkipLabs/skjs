#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import { typeErrors } from "../tools/type-errors.mts";
import { fromSkjs, verifySkjs } from "../tools/annotate-source.mts";
import path from "node:path";
// Classify the two producer witnesses independently of verifier acceptance.
// The complete safe body also has a Lean proof in WriteRefinedRead.lean; the
// source checker also consumes the generated heap-aware graph certificate.






const [
  safeAstPath,
  safeClaimsPath,
  safeFile,
  badAstPath,
  badClaimsPath,
  badFile,
  verifier,
] = process.argv.slice(2);
const load = (p) => JSON.parse(fs.readFileSync(p, "utf8"));
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
    stripTypes(fs.readFileSync(file, "utf8")),
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
  const errors = [...typeErrors(safeFile), ...typeErrors(badFile)];
  assert.equal(
    errors.length,
    2,
    errors.map((e) => `${e.file}:${e.pos} TS${e.code}: ${e.text}`).join("\n"),
  );
  const bad = path.resolve(badFile);
  assert(errors.every((e) => e.file === bad && e.code === 2322));
  const flipped = errors.find((e) => e.text.includes("Type 'true'"));
  assert(flipped);
  assert.match(flipped.text, /Type 'true' is not assignable to type 'false'/);
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
test("the original broad entry claim cannot retain a prior write fact", () => {
  const r = check(safeFile, safeClaims);
  assert.equal(r.status, "not-established");
  assert.equal(r.obligation.phase, "proof-search");
});
function observedCandidate(value) {
  const candidate = structuredClone(safeClaims);
  const f = claim(candidate, safeFile);
  const ret = safeAst.functions[0].body[2];
  const cell = f.envs
    .find((e) => e.pos[0] === ret.pos[0])
    .vars.find((v) => v.name === "cell");
  cell.type.atoms[0].fields[0].read = lit(value);
  return candidate;
}
test("an explicit true observation makes the return locally provable", () => {
  const candidate = observedCandidate(true);
  // The expression's Boolean claim is a local obligation, not a state cut.
  assert.deepEqual(
    at(claim(candidate, safeFile), safeAst.functions[0].body[2].e.pos).type,
    bool,
  );
  assert.equal(check(safeFile, candidate).status, "verified");
  at(claim(candidate, safeFile), safeAst.functions[0].body[2].e.pos).type =
    lit(true);
  assert.equal(check(safeFile, candidate).status, "verified");
});
test("a false entry observation fails on the incoming write edge", () => {
  const r = check(safeFile, observedCandidate(false));
  assert.equal(r.status, "not-established");
  assert.equal(r.obligation.phase, "proof-search");
});
test("a false read claim cannot override the actual written value", () => {
  const candidate = observedCandidate(true);
  at(claim(candidate, safeFile), safeAst.functions[0].body[2].e.pos).type =
    lit(false);
  const r = check(safeFile, candidate);
  assert.equal(r.status, "not-established");
  assert.equal(r.obligation.phase, "proof-search");
});

console.log(`Write observations: ${passed} passed, 0 failed`);
