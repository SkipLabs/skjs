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
import { atom, claimAt, claimType, fn, must } from "./edits.mts";
// Semantic top. `unknown` admits every value and permits no operation; a
// `void` result forgets its guarantee into the same top while staying its own
// source atom. SKJS verifies the fixture. A void result claimed as a number,
// and an unknown value claimed as a number, are refused. TypeScript verifies
// the functions whose statement entries it states precisely.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "void-results-"));
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

try {
  expect("SKJS verifies the whole fixture", run("stateful-source", ast, claims), true);
  for (const name of ["guardedLoopRead", "passUnknown"])
    expect(`tsc verifies ${name}`, run("source-claims", only(ast, name), tscFor(tsc, name)), true);

  // The two source types stay distinct in the claims: `void` is an atom of the
  // callback's result, `unknown` is the top flag.
  const scalar = functionOf(claims, fileKey, "privateScalar");
  const action = must(scalar.params.find((p) => p.name === "action"), "the callback parameter");
  assert.deepEqual(atom(claimType(action).atoms[0], "function").result, { top: false, atoms: [{ a: "void" }] });
  const pass = functionOf(claims, fileKey, "passUnknown");
  assert.deepEqual(claimType(must(pass.params.find((p) => p.name === "x"), "the unknown parameter")), { top: true, atoms: [] });
  passed++;
  console.log("  void and unknown are distinct source types: OK");

  // A void result gives no usable guarantee: claiming a number for it is refused.
  const number = skjsFor(claims, "privateScalar");
  claimAt(functionOf(number, fileKey, "privateScalar"), spanOf("privateScalar", "action()")).type =
    { top: false, atoms: [{ a: "number" }] };
  expect("a void result claimed as a number is refused",
    run("stateful-source", only(ast, "privateScalar"), number), false);
  // An unknown value permits nothing: it is not a number either.
  const narrowed = skjsFor(claims, "passUnknown");
  const [yStart] = spanOf("passUnknown", "return y");
  claimAt(functionOf(narrowed, fileKey, "passUnknown"), [yStart + 7, yStart + 8]).type =
    { top: false, atoms: [{ a: "number" }] };
  expect("an unknown value claimed as a number is refused",
    run("stateful-source", only(ast, "passUnknown"), narrowed), false);

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  // The callback runs for its effects, and the private scalar is unchanged.
  const ran = vm.runInContext("(() => { let n = 0; const r = privateScalar(4, () => { n += 1; }); return [r, n]; })()", context);
  assert.deepEqual([...ran], [4, 1]);
  assert.equal(vm.runInContext("guardedLoopRead('a', true)", context), undefined);
  assert.equal(vm.runInContext("unchangedLoopRead('a', false)", context), undefined);
  assert.equal(vm.runInContext("passUnknown(7)", context), 7);
  passed++;
  console.log("  source executions agree: OK");
  console.log(`Void results: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
