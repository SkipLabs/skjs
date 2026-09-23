#!/usr/bin/env node
/*
 * One quantified ordinary function at several receiver contracts:
 * tests/callables/generic-receivers.ts. The OCaml and the TypeScript producers
 * each state the scheme, its receiver binder and each call's instantiation,
 * independently; the verifier checks the body once under the binder and each
 * call against its own substitution. SKJS does not parse the strict directive.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { check as ocamlCheck } from "../ocaml-producer/check.mts";

const [verifier] = process.argv.slice(2);
const file = "verification/tests/callables/generic-receivers.ts";
const source = fs.readFileSync(file, "utf8");
const work = fs.mkdtempSync(path.join(os.tmpdir(), "generic-receivers-"));
let passed = 0;
const ok = (what: string) => {
  passed++;
  console.log(`  ${what}: OK`);
};
const execute = (text: string, expression: string) => {
  const context = vm.createContext({});
  vm.runInContext(stripTypes(text), context, { timeout: 1000 });
  return vm.runInContext(expression, context, { timeout: 1000 });
};
const replaced = (text: string, from: string, to: string) => {
  assert(text.includes(from), `the fixture has ${from}`);
  return text.replace(from, to);
};
const run = (cmd: string, args: string[]) => {
  const r = spawnSync(cmd, args, { encoding: "utf8", timeout: 120000 });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  return r;
};
let snapshots = 0;
function snapshot(text: string): string {
  const at = path.join(work, `s${snapshots++}.ts`);
  fs.writeFileSync(at, text);
  return at;
}

try {
  for (const seed of [false, true]) {
    assert.equal(execute(source, `genericSelf(${seed})`), seed);
    assert.equal(execute(source, `genericCapture(${seed})`), true);
    // Each call returns the receiver it passed: swapping them changes both.
    assert.equal(execute(replaced(source, "const first = self.call(a) as", "const first = self.call(b) as")
      .replace("const second = self.call(b) as", "const second = self.call(a) as")
      .replace("return first.value ? !second.flag : seed;", "return (first as unknown as { flag: boolean }).flag ? !(second as unknown as { value: boolean }).value : seed;"),
      `genericSelf(${seed})`), true);
  }
  ok("runtime: each instantiation returns its own receiver; the captured cell is live");

  const verified = ocamlCheck(file);
  assert.equal(verified.status, "verified", JSON.stringify(verified));
  if (verified.status === "verified")
    assert.deepEqual(verified.functions, ["genericSelf", "genericCapture"]);
  const artifacts = verified.artifacts;
  const claims: SourceClaims = JSON.parse(fs.readFileSync(path.join(artifacts, "claims.json"), "utf8"));
  const text = JSON.stringify(claims);
  assert(text.includes('"this":{"param":"R"}'), "the scheme states its receiver binder");
  const instantiations = claims.functions.flatMap((f) =>
    f.expressions.flatMap((e) => (e.instantiate ? [e.instantiate] : [])));
  assert.equal(instantiations.length, 4, "each call names its receiver instantiation");
  ok("OCaml producer: one scheme, four instantiations at two receiver contracts, verified");

  // A forged instantiation: the second call claimed at the first receiver's
  // type. The call's receiver premise then fails where the call is written.
  {
    const forged = structuredClone(claims);
    const f = forged.functions.find((g) => g.name === "genericSelf");
    assert(f, "the fixture has genericSelf");
    const sites = f.expressions.filter((e) => e.instantiate);
    assert.equal(sites.length, 2);
    const [first, second] = sites;
    assert(first.instantiate && second.instantiate);
    second.instantiate = structuredClone(first.instantiate);
    const forgedClaims = path.join(work, "forged.json");
    fs.writeFileSync(forgedClaims, JSON.stringify(forged));
    const r = run(verifier, ["--produce-source-claims", path.join(artifacts, "fragment.json"),
      forgedClaims, path.join(artifacts, "source.ts"), path.join(work, "forged.evidence"), "12"]);
    assert.notEqual(r.status, 0);
    assert.match(r.stdout + r.stderr, /"role":"method-receiver"/);
    ok("a call instantiated at another receiver's type fails its receiver obligation");
  }
  // The universal gate: a body that returns its receiver cannot promise a
  // Boolean for every receiver, whatever the calls observe.
  {
    const bad = snapshot(replaced(source, "const self = function <R>(this: R): R {",
      "const self = function <R>(this: R): boolean {")
      .replace("const first = self.call(a) as { value: boolean };\n  const second = self.call(b) as { flag: boolean };\n  return first.value ? !second.flag : seed;",
        "return self.call(a);"));
    const o = ocamlCheck(bad);
    assert.notEqual(o.status, "verified");
    if (o.status !== "verified") assert.match(o.detail, /cannot establish R ≤ boolean for every instantiation/);
    ok("the body is checked once under the binder, not per call");
  }
  // The TypeScript producer, independently: TypeScript's `.call` forgets the
  // binder, so the producer reads each instantiation from the receiver passed.
  {
    const claimsOut = path.join(work, "tsc.json"), astOut = path.join(work, "tsc.ast.json"),
      evidenceOut = path.join(work, "tsc.evidence.json");
    const parsed = run(process.execPath, ["verification/tools/fragment-parse.mts", file]);
    assert.equal(parsed.status, 0, parsed.stderr);
    fs.writeFileSync(astOut, parsed.stdout);
    const r = run(process.execPath, ["verification/tools/tsc-claims.mts", file, "--out", claimsOut]);
    assert.equal(r.status, 0, r.stderr);
    assert.deepEqual(JSON.parse(fs.readFileSync(`${claimsOut}.omissions.json`, "utf8")), []);
    const tsc: SourceClaims = JSON.parse(fs.readFileSync(claimsOut, "utf8"));
    assert(JSON.stringify(tsc).includes('"this":{"param":"R"}'));
    assert.equal(tsc.functions.flatMap((f) => f.expressions.filter((e) => e.instantiate)).length, 4);
    const produced = run(verifier, ["--produce-source-claims", astOut, claimsOut, file, evidenceOut, "10"]);
    assert.equal(produced.status, 0, produced.stdout + produced.stderr);
    const consumed = run(verifier, ["--check-source-claims", astOut, claimsOut, file, evidenceOut]);
    assert.equal(consumed.status, 0, consumed.stdout + consumed.stderr);
    ok("TypeScript producer: one scheme, four instantiations, produced and independently consumed");
  }
  console.log(`Generic receivers: ${passed} passed`);
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
