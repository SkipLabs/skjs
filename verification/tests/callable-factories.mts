#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";

const [ast, claims, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-factories-"));
try {
  const source = JSON.parse(fs.readFileSync(ast, "utf8"));
  const exported = JSON.parse(fs.readFileSync(claims, "utf8"));
  const batch = exported.find((batch: any) => batch.file === file);
  for (const name of ["factoryInstances", "sharedFactoryInstances"]) {
    const fn = source.functions.find((fn: any) => fn.name === name);
    const fc = batch.functions.find((fn: any) => fn.name === name);
    assert.ok(fn && fc, name);
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
