#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClosedOperation } from "../tools/skjs-operations.mts";
import { decodeClaimType } from "../tools/claim.mts";
// Independent checking of SKJS's closed subtype and expansion judgments.


const [claimsPath, fileKey, verifier] = process.argv.slice(2);
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "skjs-operations-"));
const clone = (x: any) => JSON.parse(JSON.stringify(x));
const fn = (name: string) =>
  claims.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === name);
const lit = (v: "true" | "false") => ({ top: false, atoms: [{ a: "booleanlit", v }] });
const boolean = { top: false, atoms: [{ a: "boolean" }] };
let passed = 0;
function run(c: any) {
  const p = path.join(tmp, "claims.json");
  fs.writeFileSync(p, JSON.stringify(c));
  const r = spawnSync(verifier, ["--check-skjs-operations", p], { encoding: "utf8" });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  return r;
}
function expect(name: string, r: ReturnType<typeof run>, accept: boolean, message = "") {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || (message && !output.includes(message))) {
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  }
  passed++;
  console.log(`  ${name}: OK`);
}
function isLit(t: any, v: string) {
  return t?.top === false && t.atoms?.length === 1 && t.atoms[0]?.a === "booleanlit" && t.atoms[0]?.v === v;
}
function isBoolean(t: any) {
  return t?.top === false && t.atoms?.length === 1 && t.atoms[0]?.a === "boolean";
}
try {
  const copy = fn("copyTrue");
  if (!Array.isArray(copy.operations)) throw Error("copyTrue has no operations array");
  copy.operations.forEach(decodeClosedOperation);
  const trueToBoolean = copy.operations.find(
    (op: any) => op.kind === "subtype" && isLit(op.source, "true") && isBoolean(op.target),
  );
  if (!trueToBoolean) throw Error("copyTrue did not export true ≤ boolean");
  decodeClaimType(trueToBoolean.source);
  decodeClaimType(trueToBoolean.target);
  expect("closed operations from a real export", run(claims), true, "closed operations");
  const missing = clone(claims);
  delete missing.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "copyTrue").operations;
  expect("missing operations field", run(missing), false, "operations");
  const extra = clone(claims);
  extra.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "copyTrue")
    .operations[0].hint = "ignore-me";
  expect("unknown operation field", run(extra), false, "unexpected fields");
  const unsound = clone(claims);
  unsound.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "copyTrue")
    .operations.find((op: any) => op.kind === "subtype" && isLit(op.source, "true") && isBoolean(op.target))
    .target = lit("false");
  expect("true ≤ false is unproved", run(unsound), false, "unproved closed operation");
  const invented = clone(claims);
  invented.find((f: any) => f.file === fileKey).functions.find((f: any) => f.name === "copyTrue")
    .operations.push({ kind: "subtype", source: boolean, target: lit("true") });
  expect("boolean ≤ true is unproved", run(invented), false, "unproved closed operation");
  console.log(`Closed SKJS operations: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
