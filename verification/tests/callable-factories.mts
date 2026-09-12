#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import { spawnSync } from "node:child_process";

const [ast, claims, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-factories-"));
try {
  const source = JSON.parse(fs.readFileSync(ast, "utf8"));
  const exported = JSON.parse(fs.readFileSync(claims, "utf8"));
  const batch = exported.find((batch: any) => batch.file === file);
  const original = fs.readFileSync(file, "utf8");
  const runtime = vm.createContext({});
  vm.runInContext(stripTypes(original), runtime, {timeout: 1000});
  for (const name of ["factoryInstances", "sharedFactoryInstances"]) {
    const fn = source.functions.find((fn: any) => fn.name === name);
    const fc = batch.functions.find((fn: any) => fn.name === name);
    assert.ok(fn && fc, name);
    const expected = name === "factoryInstances" ? [false, false, true] : [false, true, false];
    assert.equal(vm.runInContext(`${name}()`, runtime, {timeout: 1000}), name === "factoryInstances");
    // Observe locals immediately before the original outer return. Calls and
    // mutations remain the source fixture's own code; only a passive observer
    // is inserted. This is a JavaScript witness, not a Lean execution proof.
    const terminal = fn.body.at(-1);
    assert.equal(terminal.k, "return");
    const at = terminal.pos[0];
    assert.match(original.slice(at), /^return\b/);
    const observations: boolean[][] = [];
    const observed = vm.createContext({
      observe: (...values: boolean[]) => { observations.push(values); },
    });
    const instrumented = original.slice(0, at) + "observe(a, b, c); " + original.slice(at);
    vm.runInContext(stripTypes(instrumented), observed, {timeout: 1000});
    assert.equal(vm.runInContext(`${name}()`, observed, {timeout: 1000}), name === "factoryInstances");
    assert.deepEqual(observations, [expected]);
    console.log(`  ${name}: JavaScript observations ${expected.join(", ")} OK`);
    assert.ok(!fc.unavailableTypes.some((site: any) =>
      site.kind === "expression"), name);
    const input = path.join(tmp, "ast");
    const claimInput = path.join(tmp, "claims");
    fs.writeFileSync(claimInput, JSON.stringify([{...batch, functions: [fc]}]));
    fs.writeFileSync(input, JSON.stringify({...source, functions: [fn]}));
    const result = spawnSync(verifier, ["--produce-stateful-source", input, claimInput, file,
      path.join(tmp, "evidence"), "10"], {encoding: "utf8"});
    if (result.error || result.signal) throw result.error || Error(String(result.signal));
    assert.equal(result.status, 0, result.stdout + result.stderr);
    const checked = spawnSync(verifier, ["--check-stateful-source", input, claimInput, file,
      path.join(tmp, "evidence")], {encoding: "utf8"});
    assert.equal(checked.status, 0, checked.stdout + checked.stderr);
    console.log(`  ${name}: original exports and independent consumer OK`);
    // A factory's result contract must describe the returned closure's behavior.
    const forged = structuredClone(fc);
    const outer = forged.exprs.find((site: any) =>
      site.type.atoms?.some((a: any) => a.a === "function" &&
        a.result.atoms?.some((r: any) => r.a === "function")));
    assert.ok(outer, name);
    outer.type.atoms[0].result.atoms[0].result = {
      top: false, atoms: [{a: "booleanlit", v: "false"}],
    };
    fs.writeFileSync(claimInput, JSON.stringify([{...batch, functions: [forged]}]));
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
      const args = [mode, input, claimInput, file, path.join(tmp, "evidence")];
      if (mode === "--produce-stateful-source") args.push("10");
      const rejected = spawnSync(verifier, args, {encoding: "utf8"});
      if (rejected.error || rejected.signal) throw rejected.error || Error(String(rejected.signal));
      assert.notEqual(rejected.status, 0, `${name}: ${mode} accepted narrowed returned closure`);
    }
    console.log(`  ${name}: returned closure cannot promise a false-only result OK`);

  }
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
