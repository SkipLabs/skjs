#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClosedOperation, type ClosedOperation } from "../tools/skjs-operations.mts";
import type { ClaimType } from "../tools/claim.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { must, written } from "./edits.mts";
import { decodeClaimType } from "../tools/claim.mts";
// Independent checking of SKJS's closed subtype and expansion judgments.


const [claimsPath, fileKey, verifier] = process.argv.slice(2);
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "skjs-operations-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
const fn = (name: string, c = claims) => functionOf(c, fileKey, name);
const lit = (v: "true" | "false"): ClaimType => ({ top: false, atoms: [{ a: "booleanlit", v }] });
const boolean: ClaimType = { top: false, atoms: [{ a: "boolean" }] };
/** The judgments a function recorded, which every check here is about. */
const operations = (name: string, c = claims) =>
  must(fn(name, c).operations, `operations for ${name}`);
let passed = 0;
function run(c: SkjsClaims) {
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
function isLit(t: ClaimType, v: string) {
  const only = t.atoms.length === 1 ? t.atoms[0] : undefined;
  return t.top === false && only?.a === "booleanlit" && only.v === v;
}
function isBoolean(t: ClaimType) {
  return t.top === false && t.atoms.length === 1 && t.atoms[0]?.a === "boolean";
}
/** The widening this fixture is about: `true` is below `boolean`. */
const widening = (ops: ClosedOperation[]) =>
  ops.find((op) => op.kind === "subtype" && isLit(op.source, "true") && isBoolean(op.target));
try {
  operations("copyTrue").forEach(decodeClosedOperation);
  const trueToBoolean = widening(operations("copyTrue"));
  if (!trueToBoolean) throw Error("copyTrue did not export true ≤ boolean");
  decodeClaimType(trueToBoolean.source);
  decodeClaimType(trueToBoolean.target);
  expect("closed operations from a real export", run(claims), true, "closed operations");
  const missing = clone(claims);
  delete fn("copyTrue", missing).operations;
  expect("missing operations field", run(missing), false, "operations");
  const extra = clone(claims);
  written(must(operations("copyTrue", extra)[0], "an operation")).hint = "ignore-me";
  expect("unknown operation field", run(extra), false, "unexpected fields");
  const unsound = clone(claims);
  must(widening(operations("copyTrue", unsound)), "the widening").target = lit("false");
  expect("true ≤ false is unproved", run(unsound), false, "unproved closed operation");
  const invented = clone(claims);
  operations("copyTrue", invented)
    .push({ kind: "subtype", source: boolean, target: lit("true") });
  expect("boolean ≤ true is unproved", run(invented), false, "unproved closed operation");
  console.log(`Closed SKJS operations: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
