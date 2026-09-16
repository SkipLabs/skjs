#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { claimAt, expr, fn, last, must, only, stmt } from "./edits.mts";
// Exact callback contracts, real SKJS exports, and a captured-refinement witness.






const [
  astPath,
  claimsPath,
  file,
  verifier,
  badAstPath,
  badClaimsPath,
  badFile,
] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(os.tmpdir() + "/primitive-callbacks-");
const clone = structuredClone;
const nul: ClaimType = { top: false, atoms: [{ a: "null" }] };
let passed = 0;
function run(mode: string, a: Ast, c: unknown, key = file, evidence?: unknown) {
  fs.writeFileSync(tmp + "/ast.json", JSON.stringify(a));
  fs.writeFileSync(tmp + "/claims.json", JSON.stringify(c));
  if (evidence)
    fs.writeFileSync(tmp + "/evidence.json", JSON.stringify(evidence));
  const args = [
    mode,
    tmp + "/ast.json",
    tmp + "/claims.json",
    key,
    tmp + "/evidence.json",
  ];
  if (mode.startsWith("--produce")) args.push("10");
  const r = spawnSync(verifier, args, { encoding: "utf8", timeout: 30000 });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
}
function expect(
  name: string,
  r: { status: number | null; stdout: string; stderr: string },
  accept: boolean,
  reason = "",
) {
  assert.equal(r.status === 0, accept, name + ": " + r.stderr);
  assert((r.stdout + r.stderr).includes(reason), name + ": " + r.stderr);
  console.log("  " + name + ": OK");
  passed++;
}
function runtime(path: string) {
  const context = vm.createContext({});
  vm.runInContext(
    stripTypes(fs.readFileSync(path, "utf8")),
    context,
    { timeout: 1000 },
  );
  return context;
}
try {
  expect(
    "primitive callback source production",
    run("--produce-stateful-source", ast, claims),
    true,
  );
  const evidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json", "utf8"));
  expect(
    "primitive callback independent consumption",
    run("--check-stateful-source", ast, claims, file, evidence),
    true,
  );
  const exported = spawnSync(
    verifier,
    ["--export-source-claims", astPath, claimsPath, file],
    { encoding: "utf8", timeout: 30000 },
  );
  assert.equal(exported.status, 0, exported.stderr);
  const normalized = JSON.parse(exported.stdout).claims;
  expect(
    "normalized primitive domains round-trip",
    run("--produce-source-claims", ast, normalized),
    true,
  );
  const normalizedEvidence = JSON.parse(
    fs.readFileSync(tmp + "/evidence.json", "utf8"),
  );
  expect(
    "normalized independent consumption",
    run("--check-source-claims", ast, normalized, file, normalizedEvidence),
    true,
  );
  const a = clone(ast),
    c = clone(claims);
  const call = expr(stmt(last(fn(a, "booleanIdentity").body), "return").e, "apply");
  const pos = must(call.args[0], "an argument").pos;
  call.args[0] = { k: "lit", pos, lit: { a: "null" } };
  claimAt(functionOf(c, file, "booleanIdentity"), pos).type = nul;
  expect(
    "null does not satisfy Boolean callback domain",
    run("--produce-stateful-source", a, c),
    false,
    "evidence search failed",
  );
  expect(
    "old certificate cannot justify changed call",
    run("--check-stateful-source", a, c, file, evidence),
    false,
  );
  const bad: SkjsClaims = JSON.parse(fs.readFileSync(badClaimsPath, "utf8")),
    ba: Ast = JSON.parse(fs.readFileSync(badAstPath, "utf8"));
  assert.equal(only(bad, badFile).collection?.completion, "aborted");
  const rejected = run("--produce-stateful-source", ba, bad, badFile);
  expect("rejected singleton return is not certified", rejected, false);
  const goodRuntime = runtime(file),
    badRuntime = runtime(badFile);
  assert.equal(badRuntime.staleCapturedCell(true), false);
  assert.equal(badRuntime.staleCapturedCell(false), true);
  for (const seed of [true, false]) {
    assert.equal(goodRuntime.capturedWriter(seed), false);
    assert.equal(goodRuntime.stableSnapshot(seed), true);
    assert.equal(goodRuntime.booleanIdentity(seed), seed);
  }
  for (const value of [null, true, false])
    assert.equal(goodRuntime.unionIdentity(value), value);
  assert.equal(goodRuntime.returnedWriter()(false), false);
  assert.equal(goodRuntime.narrowerCallContract(), true);
  console.log("  runtime witness and stable-snapshot counterpart: OK");
  console.log(`Primitive callbacks: ${passed + 1} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
