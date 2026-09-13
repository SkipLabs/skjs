#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClaimType } from "../tools/claim-language.mts";
// Source extraction of generic bodies that copy T through const and fst.

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "generic-bodies-"));
const clone = (x: any) => JSON.parse(JSON.stringify(x));
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
  const bind = ast.functions.find((f: any) => f.name === "bind");
  const fst = ast.functions.find((f: any) => f.name === "fst");
  if (!bind || !fst) throw Error("missing bind or fst");
  decodeClaimType(bind.params[0].type);
  decodeClaimType(bind.body[0].annot);
  if (JSON.stringify(bind.body[0].annot) !== JSON.stringify(t))
    throw Error("bind const should be annotated T");
  if (fst.params.length !== 2) throw Error("fst should have two parameters");
  const exported = claims.find((f: any) => f.file === fileKey).functions;
  const bindC = exported.find((f: any) => f.name === "bind");
  const fstC = exported.find((f: any) => f.name === "fst");
  decodeClaimType(bindC.params[0].type);
  decodeClaimType(fstC.params[1].type);
  if (JSON.stringify(bindC.retType) !== JSON.stringify(t))
    throw Error("SKJS should export bind result as param T");
  expect("bind and fst are accepted", run(ast, claims), true);
  const noAnnot = clone(ast);
  noAnnot.functions.find((f: any) => f.name === "bind").body[0].annot = null;
  expect("generic const requires a T annotation", run(noAnnot, claims), false, "generic const requires");
  const badInit = clone(ast);
  badInit.functions.find((f: any) => f.name === "bind").body[0].init = {
    k: "lit",
    pos: bind.body[0].init.pos,
    lit: { a: "booleanlit", v: "true" },
  };
  expect("const cannot be initialized from true", run(badInit, claims), false, "generic body requires");
  const fstTrue = clone(ast);
  fstTrue.functions.find((f: any) => f.name === "fst").body[0].e = {
    k: "lit",
    pos: fst.body[0].e.pos,
    lit: { a: "booleanlit", v: "true" },
  };
  expect("fst returning true is not a T-copy", run(fstTrue, claims), false, "generic identity requires");
  console.log(`Generic bodies: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
