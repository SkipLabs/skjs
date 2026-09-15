#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClaimType } from "../tools/claim.mts";
// Source extraction of first-order generic aliases: Id<T> = T and Box<T> = { value: T }.

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "generic-aliases-"));
const clone = (x: any) => JSON.parse(JSON.stringify(x));
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
  const names = ast.aliases.map((a: any) => a.name).sort();
  if (JSON.stringify(names) !== JSON.stringify(["Box", "Id"]))
    throw Error("expected Id and Box aliases");
  const id = ast.aliases.find((a: any) => a.name === "Id");
  const t = { top: false, atoms: [{ a: "param", name: "T" }] };
  decodeClaimType(id.body);
  if (JSON.stringify(id.body) !== JSON.stringify(t))
    throw Error("Id body should be param T");
  const wrap = ast.functions.find((f: any) => f.name === "wrap");
  if (!wrap) throw Error("missing wrap");
  decodeClaimType(wrap.params[0].type);
  if (wrap.params[0].type.atoms[0]?.a !== "alias" || wrap.params[0].type.atoms[0]?.name !== "Id")
    throw Error("wrap parameter should be alias Id");
  const exported = claims
    .find((f: any) => f.file === fileKey)
    .functions.find((f: any) => f.name === "wrap");
  decodeClaimType(exported.params[0].type);
  decodeClaimType(exported.retType);
  if (exported.params[0].type.atoms[0]?.a !== "alias" || exported.params[0].type.atoms[0]?.name !== "Id")
    throw Error("SKJS should export alias Id");
  expect("generic aliases are accepted", run(ast, claims), true);
  const badBody = clone(ast);
  badBody.aliases.find((a: any) => a.name === "Id").body = {
    top: false,
    atoms: [{ a: "boolean" }],
  };
  expect("Id<T> = boolean is not the identity alias", run(badBody, claims), false, "only identity");
  const unknown = clone(ast);
  unknown.functions.find((f: any) => f.name === "wrap").params[0].type = {
    top: false,
    atoms: [{ a: "alias", name: "Missing", args: [{ top: false, atoms: [{ a: "boolean" }] }] }],
  };
  expect("unknown type alias is rejected", run(unknown, claims), false, "unknown type alias");
  const twoParams = clone(ast);
  twoParams.aliases.find((a: any) => a.name === "Id").typeParams = [
    { name: "T", bound: null },
    { name: "U", bound: null },
  ];
  expect("two alias type parameters are outside the fragment", run(twoParams, claims), false, "only one type parameter");
  console.log(`Generic aliases: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
