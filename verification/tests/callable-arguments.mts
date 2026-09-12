#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-arguments-"));
try {
  const source = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const exported = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const fn = source.functions.find((fn: any) => fn.name === "callableArgument");
  const ast = path.join(tmp, "ast"), claims = path.join(tmp, "claims");
  const evidence = path.join(tmp, "evidence");
  const run = (mode: string, a: any, c: any) => {
    fs.writeFileSync(ast, JSON.stringify(a));
    fs.writeFileSync(claims, JSON.stringify(c));
    const args = [mode, ast, claims, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const result = spawnSync(verifier, args, {encoding: "utf8"});
    if (result.error || result.signal) throw result.error || Error(String(result.signal));
    return result;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const result = run(mode, source, exported);
    assert.equal(result.status, 0, result.stdout + result.stderr);
  }
  console.log("  stateful callable argument: original claims and independent consumer OK");
  for (const [name, change] of [
    ["callback must accept the invoker's full Boolean domain", (fc: any) => {
      const arg = fn.body[3].init.arg;
      const site = fc.exprs.find((e: any) => e.pos[0] === arg.pos[0] && e.pos[1] === arg.pos[1]);
      site.type.atoms[0].params[0] = {top: false, atoms: [{a: "booleanlit", v: "false"}]};
    }],
    ["invoker cannot accept callbacks with incompatible results", (fc: any) => {
      const callee = fn.body[3].init.callee;
      const site = fc.exprs.find((e: any) => e.pos[0] === callee.pos[0] && e.pos[1] === callee.pos[1]);
      site.type.atoms[0].params[0].atoms[0].result = {top: false, atoms: [{a: "null"}]};
    }],
  ] as [string, (fc: any) => void][]) {
    const changed = structuredClone(exported);
    change(changed.find((b: any) => b.file === file).functions.find((f: any) => f.name === fn.name));
    // Check reuse first so a failed production cannot alter the original evidence.
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
      const result = run(mode, source, changed);
      assert.notEqual(result.status, 0, `${name}: ${mode} accepted forged contract`);
    }
    console.log(`  ${name}: OK`);
  }
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
