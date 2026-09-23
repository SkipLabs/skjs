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
// Computed keys: the receiver, then the key, then the field the key's claimed
// string singleton names. Both producers verify the fixture. A key claimed as
// a broader string cannot read a fixed record without a dictionary contract;
// one claimed as a different singleton is refused by the key's own obligation;
// and a ternary's effect in the key is a
// graph node, so a claim contradicting the value it wrote is refused.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "computed-keys-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown) {
  const ap = path.join(tmp, "ast.json"), cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, fileKey, ep, "10"], { encoding: "utf8", timeout: 60000 });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, fileKey, ep], { encoding: "utf8", timeout: 60000 });
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
const names = ["literalKey", "keyInitializesRhs", "computedRead", "twoFields"];

try {
  expect("SKJS verifies the whole fixture", run("stateful-source", ast, claims), true);
  for (const name of names)
    expect(`tsc verifies ${name}`, run("source-claims", only(ast, name), tscFor(tsc, name)), true);

  // A broad string key needs a dictionary receiver; this is only a fixed record.
  const broad = skjsFor(claims, "twoFields");
  claimAt(functionOf(broad, fileKey, "twoFields"), spanOf("twoFields", '"a"')).type =
    { top: false, atoms: [{ a: "string" }] };
  expect("a key claimed as a broad string is refused",
    run("stateful-source", only(ast, "twoFields"), broad), false, "source expression obligation");

  // Claiming the other field's name for the literal "a" selects `b`, and the
  // literal's own obligation to that claim fails.
  const swapped = skjsFor(claims, "twoFields");
  claimAt(functionOf(swapped, fileKey, "twoFields"), spanOf("twoFields", '"a"')).type =
    { top: false, atoms: [{ a: "stringlit", v: "b" }] };
  expect("a key claimed as another singleton is refused",
    run("stateful-source", only(ast, "twoFields"), swapped), false);

  // The assignment inside the key's ternary is a graph write: the right side
  // reads the value it wrote, and a claim of a different singleton is refused.
  const contradicted = skjsFor(claims, "keyInitializesRhs");
  const rhs = spanOf("keyInitializesRhs", "] = x");
  claimAt(functionOf(contradicted, fileKey, "keyInitializesRhs"), [rhs[1] - 1, rhs[1]]).type =
    { top: false, atoms: [{ a: "numberlit", v: "2" }] };
  expect("the key's effect is seen by the right side",
    run("stateful-source", only(ast, "keyInitializesRhs"), contradicted), false);

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("literalKey({ value: 4 })", context), 4);
  assert.equal(vm.runInContext("literalKey({ value: null })", context), 0);
  assert.equal(vm.runInContext("keyInitializesRhs()", context), 1);
  assert.equal(vm.runInContext("computedRead({ slot: 7 })", context), 7);
  assert.equal(vm.runInContext("twoFields({ a: 3, b: 1 })", context), 3);
  passed++;
  console.log("  source executions agree: OK");
  console.log(`Computed keys: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
