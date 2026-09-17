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
// Logical assignment to a field or an element: the target's parts once, its
// value read, the right side written only when the test on that value says
// so. Both producers verify the fixture. The kept arm is the value read, so a
// claim naming the right side's singleton on `??=` is refused; `||= true`
// and `&&= false` do establish their singletons; a number target is refused.

const [astPath, claimsPath, tscPath, fileKey, numAstPath, numTscPath, numKey, verifier] =
  process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const numAst: Ast = JSON.parse(fs.readFileSync(numAstPath, "utf8"));
const numTsc: SourceClaims = JSON.parse(fs.readFileSync(numTscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "logical-assignments-"));
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
const names = ["selectedReceiver", "computedAnd", "computedFallback", "fieldFallback"];
const withResult = (name: string, text: string, atoms: unknown[]): SkjsClaims => {
  const forged = skjsFor(claims, name);
  claimAt(functionOf(forged, fileKey, name), spanOf(name, text)).type = { top: false, atoms };
  return forged;
};

try {
  expect("SKJS verifies the whole fixture", run("stateful-source", ast, claims), true);
  for (const name of names)
    expect(`tsc verifies ${name}`, run("source-claims", only(ast, name), tscFor(tsc, name)), true);

  // The kept arm is the value read: a present number is not the right side's 0.
  expect("the kept arm of ??= is the value read, not the right side",
    run("stateful-source", only(ast, "fieldFallback"),
      withResult("fieldFallback", "(box.value ??= 0)", [{ a: "numberlit", v: "0" }])), false);
  // `&&= false` is false on both arms; `true` holds on neither.
  const and = '(box[(count += 1) === 1 ? "value" : "value"] &&= false)';
  expect("&&= false establishes false",
    run("stateful-source", only(ast, "computedAnd"),
      withResult("computedAnd", and, [{ a: "booleanlit", v: "false" }])), true);
  expect("&&= false does not establish true",
    run("stateful-source", only(ast, "computedAnd"),
      withResult("computedAnd", and, [{ a: "booleanlit", v: "true" }])), false);
  // A number target has no truthiness in the calculus.
  expect("a number target is refused", run("source-claims", numAst, numTsc, numKey), false, "Boolean target");

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  const left = vm.runInContext("(() => { const l = { value: false }, r = { value: false }; selectedReceiver(true, l, r); return [l.value, r.value]; })()", context);
  assert.deepEqual([...left], [true, false]);
  assert.equal(vm.runInContext("computedAnd(true)", context), false);
  assert.equal(vm.runInContext("computedFallback()", context), 1);
  assert.equal(vm.runInContext("fieldFallback({ value: 5 })", context), 5);
  assert.equal(vm.runInContext("fieldFallback({ value: null })", context), 0);
  passed++;
  console.log("  source executions agree: OK");
  console.log(`Logical assignments: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
