#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { at, claimAt, expr, fn, must, sole, stmt } from "./edits.mts";
// Type assertions: the operand's value, retyped at the assertion's own claim,
// which must follow from the operand. Both producers verify the fixture; the
// edits show that an assertion never establishes what a guard would, that
// its claim is checked, and that its annotation binds the operand.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "casts-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown) {
  const ap = path.join(tmp, "ast.json"),
    cp = path.join(tmp, "claims.json"),
    ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, fileKey, ep, "10"], {
    encoding: "utf8",
    timeout: 60000,
  });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, fileKey, ep], {
      encoding: "utf8",
      timeout: 60000,
    });
    if (checked.status !== 0)
      throw Error(`certificate rejected: ${checked.stderr}`);
  }
  return r;
}
function expect(name: string, r: ReturnType<typeof run>, accept: boolean, message = "") {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || (message && !output.includes(message)))
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  passed++;
  console.log(`  ${name}: OK`);
}
const only = (a: Ast, name: string): Ast => ({ ...clone(a), functions: [fn(clone(a), name)] });
const skjsFor = (c: SkjsClaims, name: string): SkjsClaims => [
  { ...clone(fileOf(c, fileKey)), functions: [clone(functionOf(c, fileKey, name))] },
];
const numberLit = (v: string): ClaimType => ({ top: false, atoms: [{ a: "numberlit", v }] });
/** The assertion a function's second statement binds. */
const assertionOf = (a: Ast, name: string, index: number) =>
  expr(sole(stmt(at(fn(a, name).body, index), "const")).init, "cast");

try {
  expect("both producers verify the whole fixture · SKJS", run("stateful-source", ast, claims), true);
  expect("both producers verify the whole fixture · tsc", run("source-claims", ast, tsc), true);

  // Without the guard the operand may be null, and the assertion does not
  // make it a number: the claim at the assertion has nothing to follow from.
  const unguarded = only(ast, "assertedSnapshot");
  unguarded.functions[0].body.splice(0, 1);
  expect(
    "an assertion does not establish what a guard would",
    run("stateful-source", unguarded, skjsFor(claims, "assertedSnapshot")),
    false,
  );

  // The claim at the assertion is checked like any other: a singleton the
  // operand does not have is refused.
  const forged = skjsFor(claims, "wideningAssertion");
  claimAt(functionOf(forged, fileKey, "wideningAssertion"), assertionOf(ast, "wideningAssertion", 0).pos).type = numberLit("2");
  expect(
    "the assertion's claim follows from the operand",
    run("stateful-source", only(ast, "wideningAssertion"), forged),
    false,
  );

  // The annotation binds the operand: `satisfies boolean` on a number fails.
  const mistyped = only(ast, "satisfiedSnapshot");
  assertionOf(mistyped, "satisfiedSnapshot", 1).annot = { top: false, atoms: [{ a: "boolean" }] };
  expect(
    "the annotation is an obligation on the operand",
    run("stateful-source", mistyped, skjsFor(claims, "satisfiedSnapshot")),
    false,
    "cast-annotation",
  );

  // A non-null assertion with nothing known is refused, not believed.
  const believed = only(ast, "nonNullSnapshot");
  believed.functions[0].body.splice(0, 1);
  expect(
    "a non-null assertion is not evidence",
    run("stateful-source", believed, skjsFor(claims, "nonNullSnapshot")),
    false,
  );

  // Angle-bracket assertions stay outside the fragment.
  const file = path.join(tmp, "gated.ts");
  fs.writeFileSync(file, "function gated(seed: 1): number { const value = <number>seed; return value; }\n");
  const r = spawnSync(process.execPath, [path.resolve(import.meta.dirname, "../tools/fragment-parse.mts"), file], {
    encoding: "utf8",
  });
  assert.notEqual(r.status, 0);
  assert(r.stderr.startsWith("gate:") && r.stderr.includes("TypeAssertionExpression"), r.stderr);
  passed++;
  console.log("  angle-bracket assertion: gated");

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("assertedSnapshot({ value: 3 })", context), 3);
  assert.equal(vm.runInContext("assertedSnapshot({ value: null })", context), 0);
  assert.equal(vm.runInContext("satisfiedSnapshot({ value: 4 })", context), 4);
  assert.equal(vm.runInContext("nonNullSnapshot({ value: 5 })", context), 5);
  assert.equal(vm.runInContext("wideningAssertion(1)", context), 1);
  passed++;
  console.log("  source executions agree with the verified contracts: OK");
  console.log(`Casts: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
