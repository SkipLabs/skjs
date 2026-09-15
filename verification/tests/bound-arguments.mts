#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import surface from "../tools/claim-type-text.mts";
import { stripTypes } from "../tools/strip-types.mts";

const [astPath, claimsPath, file, verifier, tscPath] = process.argv.slice(2);
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
  const original = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const claims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims"), evidence = path.join(work, "evidence");
  const check = (mode: string, a: any, c: any) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const command = Array.isArray(c) ? mode : mode.replace("stateful-source", "source-claims");
    const args = [command, input, contract, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  assert.notEqual(check("--produce-stateful-source", ast, original).status, 0,
    "preserve SKJS rejection and its insufficient original claims");
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = check(mode, ast, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  // The viewer must let a user supply the missing bind-result claim without
  // already having a function-type template from the rejecting producer.
  const factoryAst = structuredClone(ast);
  factoryAst.functions = factoryAst.functions.filter((f: any) => f.name === "boundFactory");
  const manual = structuredClone(original);
  const block = manual.find((b: any) => b.file === file);
  block.functions = block.functions.filter((f: any) => f.name === "boundFactory");
  const resultPos = factoryAst.functions[0].body.at(-1).e.pos;
  assert(!block.functions[0].exprs.some((e: any) => JSON.stringify(e.pos) === JSON.stringify(resultPos)));
  block.functions[0].exprs.push({pos: resultPos,
    type: surface.readClaimValue("expression", "() => boolean", undefined)});
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = check(mode, factoryAst, manual);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  block.functions[0].exprs.at(-1).type = surface.readClaimValue("expression", "() => null", undefined);
  assert.notEqual(check("--produce-stateful-source", factoryAst, manual).status, 0,
    "a newly entered function type remains an independently checked claim");
  assert.equal(check("--produce-stateful-source", ast, claims).status, 0);
  const bind = ast.functions[0].body.find((s: any) => s.name === "bound").init;
  const at = (c: any, pos: number[]) => c.functions
    .find((f: any) => f.name === "boundArguments").expressions
    .find((e: any) => e.pos[0] === pos[0] && e.pos[1] === pos[1]);
  const signature = (c: any) => c.types[at(c, bind.pos).type[0]][0].arrs.arrows[0];
  for (const [name, edit] of [
    ["remaining arity", (a: any, c: any) => signature(c)[0].push([1, 2])],
    ["bound result", (a: any, c: any) => { signature(c)[1] = [0]; }],
    ["bound argument domain", (a: any, c: any) => {
      const expr = a.functions[0].body.find((s: any) => s.name === "bound").init;
      expr.args[0] = {k: "lit", pos: expr.args[0].pos, lit: {a: "null"}};
      at(c, expr.args[0].pos).type = [0];
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
  console.log("  SKJS incompleteness: original claims rejected, tsc claims verified; saved prefix versus live capture, escaping thunk, remaining signature and intrinsic gate OK");
} finally { fs.rmSync(work, {recursive: true, force: true}); }
