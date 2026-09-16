#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClaimType } from "../tools/claim.mts";
import type { Ast } from "../tools/fragment.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { atom, claimType, fn, must } from "./edits.mts";

/** One type alias of a parse, by name. */
const alias = (a: Ast, name: string) =>
  must(a.aliases.find((x) => x.name === name), `the alias ${name}`);
// Source extraction of first-order generic aliases: Id<T> = T and Box<T> = { value: T }.

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "generic-aliases-"));
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
  const names = ast.aliases.map((a) => a.name).sort();
  if (JSON.stringify(names) !== JSON.stringify(["Box", "Id"]))
    throw Error("expected Id and Box aliases");
  const id = alias(ast, "Id");
  const t = { top: false, atoms: [{ a: "param", name: "T" }] };
  decodeClaimType(id.body);
  if (JSON.stringify(id.body) !== JSON.stringify(t))
    throw Error("Id body should be param T");
  const wrap = fn(ast, "wrap");
  const wrapped = must(wrap.params[0], "a parameter").type;
  decodeClaimType(wrapped);
  if (atom(wrapped.atoms[0], "alias").name !== "Id")
    throw Error("wrap parameter should be alias Id");
  const exported = functionOf(claims, fileKey, "wrap");
  const claimed = claimType(must(exported.params[0], "a parameter"));
  decodeClaimType(exported.retType);
  if (atom(claimed.atoms[0], "alias").name !== "Id")
    throw Error("SKJS should export alias Id");
  expect("generic aliases are accepted", run(ast, claims), true);
  const badBody = clone(ast);
  alias(badBody, "Id").body = {
    top: false,
    atoms: [{ a: "boolean" }],
  };
  expect("Id<T> = boolean is not the identity alias", run(badBody, claims), false, "only identity");
  const unknown = clone(ast);
  must(fn(unknown, "wrap").params[0], "a parameter").type = {
    top: false,
    atoms: [{ a: "alias", name: "Missing", args: [{ top: false, atoms: [{ a: "boolean" }] }] }],
  };
  expect("unknown type alias is rejected", run(unknown, claims), false, "unknown type alias");
  const twoParams = clone(ast);
  alias(twoParams, "Id").typeParams = [
    { name: "T", bound: null },
    { name: "U", bound: null },
  ];
  expect("two alias type parameters are outside the fragment", run(twoParams, claims), false, "only one type parameter");
  console.log(`Generic aliases: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
