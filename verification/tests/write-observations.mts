#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import { typeErrors } from "../tools/type-errors.mts";
import { fromSkjs, verifySkjs } from "../tools/annotate-source.mts";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { Span } from "../tools/span.mts";
import { claimOfTerm } from "../tools/term-claim.mts";
import {
  fileOf,
  functionOf,
  type SkjsClaims,
  type SkjsFunction,
} from "../tools/skjs-claims.mts";
import {
  at as nth,
  atom,
  binding,
  claimType,
  expr,
  fn as functionIn,
  must,
  sole,
  stmt,
} from "./edits.mts";
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
const load = <T,>(p: string | undefined): T =>
  JSON.parse(fs.readFileSync(must(p, "a path"), "utf8"));
const safeAst: Ast = load(safeAstPath),
  safeClaims: SkjsClaims = load(safeClaimsPath);
const badAst: Ast = load(badAstPath),
  badClaims: SkjsClaims = load(badClaimsPath);
const claim = (cs: SkjsClaims, file: string, name = "writeRefinedRead") =>
  functionOf(cs, file, name);
const at = (f: SkjsFunction, pos: Span) =>
  must(
    f.exprs.find((e) => JSON.stringify(e.pos) === JSON.stringify(pos)),
    `a claim at ${pos.join(":")}`,
  );
const bool: ClaimType = { top: false, atoms: [{ a: "boolean" }] };
const lit = (v: boolean): ClaimType =>
  ({ top: false, atoms: [{ a: "booleanlit", v: String(v) }] });
let passed = 0;
/** The statement the safe fixture returns from, which every observation is
 * stated at. */
const returned = () =>
  stmt(nth(must(safeAst.functions[0], "the safe function").body, 2), "return");
function test(name: string, f: () => void) {
  f();
  passed++;
  console.log(`  ${name}: OK`);
}
function runtime(file: string) {
  const context = vm.createContext({});
  vm.runInContext(
    stripTypes(fs.readFileSync(file, "utf8")),
    context,
  );
  return context;
}
function check(file: string, claims: SkjsClaims, name = "writeRefinedRead") {
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
  return must(
    results[fileOf(claims, file).functions.findIndex((f) => f.name === name)],
    `a result for ${name}`,
  );
}
// `Result.obligation` is explanatory metadata a verifier need not record, so
// the wire type leaves it `unknown`. A test that reads its phase says so first.
function phaseOf(obligation: unknown) {
  assert(
    obligation && typeof obligation === "object" && "phase" in obligation,
    "a not-established result records an obligation",
  );
  return obligation.phase;
}
function stripPositions(x: unknown): unknown {
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
  const f = must(safeAst.functions[0], "the safe function"),
    cell = sole(stmt(nth(f.body, 0), "const"));
  assert.equal(f.name, "writeRefinedRead");
  assert.deepEqual(f.params, []);
  assert.deepEqual(claimOfTerm(f.retType), lit(true));
  assert.deepEqual(atom(claimOfTerm(must(cell.annot, "the annotation")).atoms[0], "record").fields, [
    { name: "value", optional: false, read: bool, write: bool },
  ]);
  assert.deepEqual(stripPositions(f.body), [
    {
      k: "const",
      bindings: [
        {
          name: "cell",
          annot: cell.annot,
          init: {
            k: "alloc",
            fields: [{name: "value", e: { k: "lit", lit: { a: "booleanlit", v: "false" } }}],
          },
        },
      ],
    },
    {
      k: "effect",
      e: {
        k: "write",
        field: "value",
        receiver: { k: "id", name: "cell" },
        rhs: { k: "lit", lit: { a: "booleanlit", v: "true" } },
      },
    },
    { k: "return", e: { k: "read", field: "value", e: { k: "id", name: "cell" } } },
  ]);
});
test("normal first-error export contains the imprecise Boolean read", () => {
  const f = claim(safeClaims, must(safeFile, "the safe file"));
  assert.equal(f.collection?.completion, "aborted");
  assert.equal(f.collection?.mode, "normal");
  assert.equal(f.collection?.quality, "unverified");
  assert.deepEqual(at(f, returned().e.pos).type, bool);
});
test("runtime results establish the two classifications", () => {
  assert.equal(runtime(must(safeFile, "the safe file")).writeRefinedRead(), true);
  const bad = runtime(must(badFile, "the unsound file"));
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
test("rejected negated guard exports a broad read instead of stale false", () => {
  const f = claim(badClaims, must(badFile, "the unsound file"), "staleFlip"),
    loop = stmt(nth(functionIn(badAst, "staleFlip").body, 1), "while");
  assert.equal(f.collection?.completion, "aborted");
  assert.equal(f.collection?.mode, "normal");
  assert.deepEqual(f.retType, lit(false));
  assert.deepEqual(
    expr(expr(stmt(nth(loop.body, 0), "effect").e, "write").rhs, "lit").lit,
    { a: "booleanlit", v: "true" },
  );
  assert.deepEqual(at(f, stmt(nth(loop.body, 1), "return").e.pos).type, bool);
});
test("rejected negated witness cannot certify its partial export", () => {
  const r = check(must(badFile, "the unsound file"), badClaims, "staleFlip");
  assert.equal(r.status, "not-established");
  // `location` is optional: a result need not say where checking stopped.
  assert(r.location, "the result records where checking stopped");
  assert.equal(must(r.location, "where checking stopped").kind, "missing-environment-claim");
  assert.equal(r.obligation, undefined);
});
test("the original broad entry claim cannot retain a prior write fact", () => {
  const r = check(must(safeFile, "the safe file"), safeClaims);
  assert.equal(r.status, "not-established");
  assert.equal(phaseOf(r.obligation), "proof-search");
});
function observedCandidate(value: boolean) {
  const candidate = structuredClone(safeClaims);
  const f = claim(candidate, must(safeFile, "the safe file"));
  const cell = binding(f, returned().pos[0], "cell");
  must(atom(claimType(cell).atoms[0], "record").fields[0], "a field").read = lit(value);
  return candidate;
}
test("an explicit true observation makes the return locally provable", () => {
  const candidate = observedCandidate(true);
  // The expression's Boolean claim is a local obligation, not a state cut.
  assert.deepEqual(
    at(claim(candidate, must(safeFile, "the safe file")), returned().e.pos).type,
    bool,
  );
  assert.equal(check(must(safeFile, "the safe file"), candidate).status, "verified");
  at(claim(candidate, must(safeFile, "the safe file")), returned().e.pos).type =
    lit(true);
  assert.equal(check(must(safeFile, "the safe file"), candidate).status, "verified");
});
test("a false entry observation fails on the incoming write edge", () => {
  const r = check(must(safeFile, "the safe file"), observedCandidate(false));
  assert.equal(r.status, "not-established");
  assert.equal(phaseOf(r.obligation), "proof-search");
});
test("a false read claim cannot override the actual written value", () => {
  const candidate = observedCandidate(true);
  at(claim(candidate, must(safeFile, "the safe file")), returned().e.pos).type =
    lit(false);
  const r = check(must(safeFile, "the safe file"), candidate);
  assert.equal(r.status, "not-established");
  assert.equal(phaseOf(r.obligation), "proof-search");
});

console.log(`Write observations: ${passed} passed, 0 failed`);
