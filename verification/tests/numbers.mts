#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClaimType, type ClaimType } from "../tools/claim.mts";
import type { Ast } from "../tools/fragment.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { fn } from "./edits.mts";
// Numbers in the source fragment: the family, its singletons, and the one
// inclusion between them. Mutations check that nothing wider is admitted.

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "numbers-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
const number: ClaimType = { top: false, atoms: [{ a: "number" }] };
const one: ClaimType = { top: false, atoms: [{ a: "numberlit", v: "1" }] };
let passed = 0;

function run(a: Ast, c: SkjsClaims) {
  const ap = path.join(tmp, "ast.json"), cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier,
    ["--produce-stateful-source", ap, cp, fileKey, ep, "10"], { encoding: "utf8" });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  // A produced certificate that the independent consumer rejects is a defect,
  // never an acceptance.
  if (r.status === 0) {
    const checked = spawnSync(verifier,
      ["--check-stateful-source", ap, cp, fileKey, ep], { encoding: "utf8" });
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

try {
  const exported = fileOf(claims, fileKey).functions;
  const byName = (n: string) => functionOf(claims, fileKey, n);
  for (const f of exported) { decodeClaimType(f.retType); f.params.forEach((p) => decodeClaimType(p.type)); }

  if (JSON.stringify(byName("idNumber").retType) !== JSON.stringify(number))
    throw Error("SKJS should export the number family");
  if (JSON.stringify(byName("singletonNumber").retType) !== JSON.stringify(one))
    throw Error("SKJS should preserve the numeric singleton, not widen it");
  // `1.0` and `1` are one literal: the identity is the double, not the spelling.
  if (JSON.stringify(byName("spelledNumber").retType) !== JSON.stringify(one))
    throw Error("a differently spelled literal should be the same singleton");

  expect("numbers are accepted", run(ast, claims), true);

  // A singleton is below the family; the family is not below the singleton.
  const widen = clone(claims);
  functionOf(widen, fileKey, "singletonNumber").retType = number;
  expect("the family cannot stand in for a singleton result",
    run(ast, widen), false, "from the source annotation");

  const narrow = clone(ast);
  fn(narrow, "idNumber").retType = one;
  expect("a number result cannot be narrowed to a singleton",
    run(narrow, claims), false);

  // Distinct singletons are unrelated in both directions.
  const other = clone(claims);
  functionOf(other, fileKey, "spelledNumber").retType =
    { top: false, atoms: [{ a: "numberlit", v: "2" }] };
  expect("a different number is a different singleton",
    run(ast, other), false, "from the source annotation");

  // A number is not a boolean, and the guard result is not the guarded value.
  const asBool = clone(claims);
  functionOf(asBool, fileKey, "idNumber").retType =
    { top: false, atoms: [{ a: "boolean" }] };
  expect("a number is not a boolean", run(ast, asBool), false,
    "from the source annotation");

  // Dropping null from the declared parameter is not something the guard grants.
  const dropNull = clone(ast);
  fn(dropNull, "guardNumber").params[0]!.type = number;
  expect("the guarded parameter keeps its null arm", run(dropNull, claims), false);

  console.log(`Numbers: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
