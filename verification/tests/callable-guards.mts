#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import type { Ast, FunctionAst } from "../tools/fragment.mts";
import type { SkjsClaims } from "../tools/skjs-claims.mts";
import { at, atom, claimFrom, claimType, expr, fn as functionIn, rows, stmt } from "./edits.mts";
import { functionOf } from "../tools/skjs-claims.mts";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "callable-guards-"));
/** The one `if` this fixture guards with. */
const guard = (f: FunctionAst) => stmt(at(f.body, 0), "if");
try {
  const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims");
  const evidence = path.join(work, "evidence");
  const run = (mode: string, a: Ast, c: SkjsClaims) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [mode, input, contract, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = run(mode, ast, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  for (const [name, edit] of rows<[string, (f: FunctionAst) => void]>([
    ["opposite polarity cannot justify invocation", (f) => {
      expr(guard(f).cond, "typeofTest").equal = false;
    }],
    ["another same-typed input cannot justify refinement", (f) => {
      expr(expr(guard(f).cond, "typeofTest").e, "id").name = "other";
    }],
  ])) {
    const changed = structuredClone(ast);
    edit(functionIn(changed, "guardedShape"));
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(run(mode, changed, claims).status, 0, name);
  }
  const forged = structuredClone(claims);
  const guarded = functionIn(ast, "guardedShape");
  const pos = expr(stmt(at(guard(guarded).then, 0), "return").e, "apply").callee.pos;
  const call = claimFrom(functionOf(forged, file, guarded.name), pos[0]);
  atom(claimType(call).atoms[0], "function").result = {
    top: false,
    atoms: [{ a: "booleanlit", v: "true" }],
  };
  for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
    assert.notEqual(run(mode, ast, forged).status, 0, "shape cannot invent a more precise callable result");
  console.log("  function guards: both polarities, captured refinement, value test, and forged evidence rejection OK");
} finally {
  fs.rmSync(work, {recursive: true, force: true});
}
