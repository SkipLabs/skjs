#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "bound-arguments-"));
try {
  const source = fs.readFileSync(file, "utf8");
  const execute = (text: string, expression: string) => {
    const context = vm.createContext({});
    vm.runInContext(stripTypes(text), context, {timeout: 1000});
    return vm.runInContext(expression, context, {timeout: 1000});
  };
  for (const seed of [false, true]) {
    assert.equal(execute(source, `boundArguments(${seed})`), !seed);
    assert.equal(execute(source, `boundFactory(${seed})()`), seed);
    const delayed = source.replace("const bound = target.bind((cell.value = !seed), cell.value);",
      "cell.value = !seed; const bound = (later: boolean): boolean => target(cell.value, later);");
    assert.notEqual(delayed, source);
    assert.equal(execute(delayed, `boundArguments(${seed})`), seed,
      "bound arguments are saved values, while the target's cell capture remains live");
  }

  const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims"), evidence = path.join(work, "evidence");
  const check = (mode: string, a: any, c: any) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [mode, input, contract, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = check(mode, ast, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  const bind = ast.functions[0].body.find((s: any) => s.name === "bound").init;
  const at = (c: any, pos: number[]) => c.find((b: any) => b.file === file).functions
    .find((f: any) => f.name === "boundArguments").exprs
    .find((e: any) => e.pos[0] === pos[0] && e.pos[1] === pos[1]);
  for (const [name, edit] of [
    ["remaining arity", (a: any, c: any) => at(c, bind.pos).type.atoms[0].params.push({top: false, atoms: [{a: "boolean"}]})],
    ["bound result", (a: any, c: any) => { at(c, bind.pos).type.atoms[0].result = {top: false, atoms: [{a: "null"}]}; }],
    ["bound argument domain", (a: any, c: any) => {
      const expr = a.functions[0].body.find((s: any) => s.name === "bound").init;
      expr.args[0] = {k: "lit", pos: expr.args[0].pos, lit: {a: "null"}};
      at(c, expr.args[0].pos).type = {top: false, atoms: [{a: "null"}]};
    }],
  ] as [string, (a: any, c: any) => void][]) {
    const a = structuredClone(ast), c = structuredClone(claims);
    edit(a, c);
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(check(mode, a, c).status, 0, name);
  }
  for (const text of [
    "function f(g: (x: boolean) => boolean): () => boolean { return g.bind(null, true); }",
    "function f(): () => boolean { const g = (): boolean => true; return g.bind(); }",
  ]) {
    const probe = path.join(work, "probe.ts");
    fs.writeFileSync(probe, text);
    const r = spawnSync(process.execPath, ["verification/tools/parse-source.mts", probe], {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /\.bind requires a known local arrow/);
  }
  console.log("  bound arrows: saved prefix versus live capture, escaping thunk, remaining signature and intrinsic gate OK");
} finally { fs.rmSync(work, {recursive: true, force: true}); }
