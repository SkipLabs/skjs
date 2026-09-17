#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { claimAt, fn, must } from "./edits.mts";
// Arithmetic: the double operation on two numbers, yielding the number family.
// Both producers verify the fixture. An operand claimed as possibly null, a
// result claimed as a singleton, and string concatenation are refused.

const [astPath, claimsPath, tscPath, fileKey, strAstPath, strClaimsPath, strKey, verifier] =
  process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const strAst: Ast = JSON.parse(fs.readFileSync(strAstPath, "utf8"));
const strClaims: SkjsClaims = JSON.parse(fs.readFileSync(strClaimsPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "arithmetic-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown, key = fileKey) {
  const ap = path.join(tmp, "ast.json"), cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, key, ep, "10"], { encoding: "utf8", timeout: 60000 });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, key, ep], { encoding: "utf8", timeout: 60000 });
    if (checked.status !== 0) throw Error(`certificate rejected: ${checked.stderr}`);
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
const tscFor = (d: SourceClaims, name: string): SourceClaims => ({
  ...clone(d), functions: [clone(must(d.functions.find((f) => f.name === name), `claims for ${name}`))],
});
const spanOf = (name: string, text: string): [number, number] => {
  const start = source.indexOf(text, source.indexOf(`function ${name}(`));
  assert(start >= 0, `fixture text ${JSON.stringify(text)}`);
  return [start, start + text.length];
};
const names = ["sum", "plusLocal", "plusField", "increment", "annotatedCompoundKey", "computedUpdate"];

try {
  expect("SKJS verifies the whole fixture", run("stateful-source", ast, claims), true);
  for (const name of names)
    expect(`tsc verifies ${name}`, run("source-claims", only(ast, name), tscFor(tsc, name)), true);

  // An operand the number test does not answer for is refused.
  const nullable = skjsFor(claims, "sum");
  const [aStart] = spanOf("sum", "a + b");
  claimAt(functionOf(nullable, fileKey, "sum"), [aStart, aStart + 1]).type =
    { top: false, atoms: [{ a: "null" }, { a: "number" }] };
  expect("an operand claimed as possibly null is refused",
    run("stateful-source", only(ast, "sum"), nullable), false);

  // The result is the number family: no singleton is derived for it.
  const exact = skjsFor(claims, "sum");
  claimAt(functionOf(exact, fileKey, "sum"), spanOf("sum", "c - 1")).type =
    { top: false, atoms: [{ a: "numberlit", v: "1" }] };
  expect("a singleton result claim is refused",
    run("stateful-source", only(ast, "sum"), exact), false);

  // String concatenation is outside the calculus.
  expect("concatenation is refused", run("stateful-source", strAst, strClaims, strKey), false);

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("sum(2, 3)", context), 4);
  assert.equal(vm.runInContext("plusLocal(1)", context), 2);
  assert.equal(vm.runInContext("plusField({ value: 4 })", context), 8);
  // The postfix increment is the old value: 0 + 1.
  assert.equal(vm.runInContext("increment()", context), 1);
  // The key's effect happens once: count is 1, not 2.
  assert.equal(vm.runInContext("annotatedCompoundKey()", context), 1);
  assert.equal(vm.runInContext("computedUpdate()", context), 0);
  passed++;
  console.log("  source executions agree: OK");
  console.log(`Arithmetic: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
