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
    assert.ok(fc.unavailableTypes.some((site: any) =>
      site.kind === "expression" && site.reason === "nested-object-type"), name);
    const input = path.join(tmp, "ast");
    const claimInput = path.join(tmp, "claims");
    fs.writeFileSync(claimInput, JSON.stringify([{...batch, functions: [fc]}]));
    fs.writeFileSync(input, JSON.stringify({...source, functions: [fn]}));
    const result = spawnSync(verifier, ["--produce-stateful-source", input, claimInput, file,
      path.join(tmp, "evidence"), "10"], {encoding: "utf8"});
    if (result.error || result.signal) throw result.error || Error(String(result.signal));
    // Baseline: SKJS cannot yet export a callable-valued result contract.
    assert.notEqual(result.status, 0, result.stdout + result.stderr);
    assert.match(result.stdout + result.stderr, /source expression obligation at \[\d+,\d+\): type claim unavailable from producer/);
    console.log(`  ${name}: callable result export boundary OK`);
  }
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
