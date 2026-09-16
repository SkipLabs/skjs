#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClaimType } from "../tools/claim.mts";
import type { Ast } from "../tools/fragment.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { at, fn as functionIn, stmt } from "./edits.mts";
// Source extraction of generic identity: rigid T, return the parameter.


const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "generic-source-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;
function run(a: Ast, c: SkjsClaims) {
  const ap = path.join(tmp, "ast.json");
  const cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, ["--produce-stateful-source", ap, cp, fileKey, ep, "8"], {
    encoding: "utf8",
  });
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
try {
  const fn = functionIn(ast, "id");
  if (JSON.stringify(fn.typeParams) !== JSON.stringify([{ name: "T", bound: null }]))
    throw Error("id should declare type parameter T");
  const t = { top: false, atoms: [{ a: "param", name: "T" }] };
  decodeClaimType(fn.params[0].type);
  decodeClaimType(fn.retType);
  if (JSON.stringify(fn.params[0].type) !== JSON.stringify(t))
    throw Error("parameter type should be param T");
  const exported = functionOf(claims, fileKey, "id");
  decodeClaimType(exported.params[0].type);
  decodeClaimType(exported.retType);
  if (JSON.stringify(exported.params[0].type) !== JSON.stringify(t))
    throw Error("SKJS should export param T");
  expect("generic identity is accepted", run(ast, claims), true);
  const wrongBody = clone(ast);
  const returned = stmt(at(wrongBody.functions[0].body, 0), "return");
  returned.e = {
    k: "lit",
    pos: returned.e.pos,
    lit: { a: "booleanlit", v: "true" },
  };
  expect("returning true is not identity", run(wrongBody, claims), false, "generic identity requires");
  const twoParams = clone(ast);
  twoParams.functions[0].typeParams = [
    { name: "T", bound: null },
    { name: "U", bound: null },
  ];
  expect("an unused distinct type parameter is admitted", run(twoParams, claims), true);
  console.log(`Generic source: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
