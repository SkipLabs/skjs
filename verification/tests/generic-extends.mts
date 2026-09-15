#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClaimType } from "../tools/claim.mts";
// Source extraction of T extends boolean: T ≤ boolean, not true ≤ T.

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "generic-extends-"));
const clone = (x: any) => JSON.parse(JSON.stringify(x));
const boolean = { top: false, atoms: [{ a: "boolean" }] };
const t = { top: false, atoms: [{ a: "param", name: "T" }] };
let passed = 0;
function run(a: any, c: any) {
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
  const asBoolean = ast.functions.find((f: any) => f.name === "asBoolean");
  if (!asBoolean) throw Error("missing asBoolean");
  if (JSON.stringify(asBoolean.typeParams) !== JSON.stringify([{ name: "T", bound: boolean }]))
    throw Error("asBoolean should declare T extends boolean");
  decodeClaimType(asBoolean.params[0].type);
  decodeClaimType(asBoolean.retType);
  if (JSON.stringify(asBoolean.params[0].type) !== JSON.stringify(t))
    throw Error("parameter type should be param T");
  if (JSON.stringify(asBoolean.retType) !== JSON.stringify(boolean))
    throw Error("result should be boolean");
  const exported = claims
    .find((f: any) => f.file === fileKey)
    .functions.find((f: any) => f.name === "asBoolean");
  decodeClaimType(exported.params[0].type);
  decodeClaimType(exported.retType);
  if (JSON.stringify(exported.params[0].type) !== JSON.stringify(t))
    throw Error("SKJS should export param T");
  if (JSON.stringify(exported.retType) !== JSON.stringify(boolean))
    throw Error("SKJS should export boolean result");
  expect("asBoolean and bounded identity are accepted", run(ast, claims), true);
  const trap = clone(ast);
  const idB = trap.functions.find((f: any) => f.name === "idBounded");
  idB.body[0].e = { k: "lit", pos: idB.body[0].e.pos, lit: { a: "booleanlit", v: "true" } };
  expect("true as T is not justified by extends boolean", run(trap, claims), false, "does not justify true");
  const unbounded = clone(ast);
  unbounded.functions.find((f: any) => f.name === "asBoolean").typeParams[0].bound = null;
  expect("returning T as boolean requires the bound", run(unbounded, claims), false, "requires T extends boolean");
  const notBoolean = clone(ast);
  notBoolean.functions.find((f: any) => f.name === "asBoolean").typeParams[0].bound = t;
  expect("a parameter cannot be its own bound", run(notBoolean, claims), false, "only `extends boolean`");
  console.log(`Generic extends: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
