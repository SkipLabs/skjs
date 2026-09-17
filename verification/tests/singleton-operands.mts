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
import { atom, binding, claimAt, claimType, fn, must } from "./edits.mts";
// Singleton operands: a strict comparison refines the tested read when the
// other operand's claimed type is a singleton and the operand is effect-free,
// a literal, a name or a field read. Both producers verify the fixture. The
// wrong arm's refinement and a broadened operand claim are refused, and so is
// TypeScript's claim on a second file whose operand is a call.

const [astPath, claimsPath, tscPath, fileKey, callAstPath, callTscPath, callKey, verifier] =
  process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const callAst: Ast = JSON.parse(fs.readFileSync(callAstPath, "utf8"));
const callTsc: SourceClaims = JSON.parse(fs.readFileSync(callTscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const callSource = fs.readFileSync(callKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "singleton-operands-"));
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
const startOf = (name: string, text: string): number => {
  const start = source.indexOf(text, source.indexOf(`function ${name}(`));
  assert(start >= 0, `fixture text ${JSON.stringify(text)}`);
  return start;
};
const names = ["inferredFieldComparison", "comparedToParameter", "reversedOperands", "equalBranch", "localCellCompared"];

try {
  expect("SKJS verifies the whole fixture", run("stateful-source", ast, claims), true);
  for (const name of names)
    expect(`tsc verifies ${name}`, run("source-claims", only(ast, name), tscFor(tsc, name)), true);

  // The inequality's right arm holds the other singleton: claiming the
  // compared one there is refused.
  const swapped = skjsFor(claims, "inferredFieldComparison");
  const x = binding(functionOf(swapped, fileKey, "inferredFieldComparison"),
    startOf("inferredFieldComparison", "return x.value"), "x");
  atom(claimType(x).atoms[0], "record").fields[0].read = { top: false, atoms: [{ a: "numberlit", v: "0" }] };
  x.type = claimType(x);
  expect("the wrong arm's refinement is refused",
    run("stateful-source", only(ast, "inferredFieldComparison"), swapped), false);

  // The singleton is the operand's claimed type: broadened to a number, the
  // comparison no longer selects a tag test.
  const broad = skjsFor(claims, "inferredFieldComparison");
  const zeroStart = startOf("inferredFieldComparison", "other.zero)");
  const zero = claimAt(functionOf(broad, fileKey, "inferredFieldComparison"), [zeroStart, zeroStart + "other.zero".length]);
  zero.type = { top: false, atoms: [{ a: "number" }] };
  expect("a broadened operand claim is refused",
    run("stateful-source", only(ast, "inferredFieldComparison"), broad), false, "singleton operand");

  // A call may write the tested cell between the read and the branch, so the
  // read is not saved across it and TypeScript's narrowing is refused.
  expect("a call operand does not refine the read",
    run("source-claims", callAst, callTsc, callKey), false, "incoming edge obligation");

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  vm.runInContext(stripTypes(callSource), context);
  assert.equal(vm.runInContext("inferredFieldComparison({ value: 1 }, 0)", context), 1);
  assert.equal(vm.runInContext("inferredFieldComparison({ value: 0 }, 0)", context), 1);
  assert.equal(vm.runInContext("comparedToParameter({ value: 1 }, 0)", context), 1);
  assert.equal(vm.runInContext("reversedOperands({ value: 1 }, 0)", context), 1);
  assert.equal(vm.runInContext("equalBranch({ value: 0 }, 0)", context), 0);
  assert.equal(vm.runInContext("equalBranch({ value: 1 }, 0)", context), 0);
  assert.equal(vm.runInContext("localCellCompared(1, 0)", context), 1);
  // The rejected program returns 0 as a 1 when the call writes the cell.
  const written = vm.runInContext(
    "(() => { const o = { value: 1 }; return callOperand(o, () => { o.value = 0; return 0; }); })()", context);
  assert.equal(written, 0);
  passed++;
  console.log("  source executions agree, including the writing call: OK");
  console.log(`Singleton operands: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
