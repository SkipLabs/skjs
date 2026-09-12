#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";

const [ast, claims, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-arguments-"));
try {
  const source = JSON.parse(fs.readFileSync(ast, "utf8"));
  const exported = JSON.parse(fs.readFileSync(claims, "utf8"));
  const fn = source.functions.find((fn: any) => fn.name === "callableArgument");
  const fc = exported.find((batch: any) => batch.file === file).functions.find((fn: any) => fn.name === "callableArgument");
  assert.ok(fn && fc);
  const invoke = fn.body[2].init;
  assert.equal(invoke.name, "f");
  const claim = fc.exprs.find((site: any) => site.pos[0] === invoke.pos[0] && site.pos[1] === invoke.pos[1]);
  assert.deepEqual(claim?.type, {unsupported: true});
  assert(fc.unavailableTypes.some((site: any) => site.kind === "expression" &&
    site.pos[0] === invoke.pos[0] && site.pos[1] === invoke.pos[1] && site.reason === "nested-object-type"));
  const result = spawnSync(verifier, ["--produce-stateful-source", ast, claims, file,
    path.join(tmp, "evidence"), "10"], {encoding: "utf8"});
  if (result.error || result.signal) throw result.error || Error(String(result.signal));
  assert.notEqual(result.status, 0, result.stdout + result.stderr);
  assert.match(result.stdout + result.stderr, /source expression obligation at \[\d+,\d+\): type claim unavailable from producer/);
  console.log("  callable argument: original export records the unsupported parameter boundary OK");
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
