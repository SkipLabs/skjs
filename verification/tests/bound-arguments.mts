#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import surface from "../tools/claim-text.mts";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast, Stmt } from "../tools/fragment.mts";
import type { Arrow } from "../tools/type-graph.mts";
import type { Span } from "../tools/span.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { expr, fn, last, must, rows, sole, stmt } from "./edits.mts";

const [astPath, claimsPath, file, verifier, tscPath] = process.argv.slice(2);
/** A statement that binds this name, which is how the fixture is addressed. */
const named = (name: string) => (s: Stmt) =>
  (s.k === "const" || s.k === "let") && s.bindings.some((b) => b.name === name);
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

  const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const original: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const claims: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims"), evidence = path.join(work, "evidence");
  const check = (mode: string, a: Ast, c: SkjsClaims | SourceClaims) => {
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
  factoryAst.functions = factoryAst.functions.filter((f) => f.name === "boundFactory");
  const manual = structuredClone(original);
  const block = fileOf(manual, file);
  block.functions = block.functions.filter((f) => f.name === "boundFactory");
  const factory = must(block.functions[0], "the factory's claims");
  const resultPos = stmt(last(fn(factoryAst, "boundFactory").body), "return").e.pos;
  assert(!factory.exprs.some((e) => JSON.stringify(e.pos) === JSON.stringify(resultPos)));
  factory.exprs.push({pos: resultPos,
    type: surface.readClaimValue("expression", "() => boolean", undefined)});
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = check(mode, factoryAst, manual);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  must(factory.exprs[factory.exprs.length - 1], "the claim just added").type =
    surface.readClaimValue("expression", "() => null", undefined);
  assert.notEqual(check("--produce-stateful-source", factoryAst, manual).status, 0,
    "a newly entered function type remains an independently checked claim");
  assert.equal(check("--produce-stateful-source", ast, claims).status, 0);
  /** The `.bind` call this fixture binds, wherever its statement sits. */
  const bound = (a: Ast) => expr(
    sole(stmt(must(fn(a, "boundArguments").body.find(named("bound")), "the bound local"), "const")).init,
    "bindWithReceiver",
  );
  const bind = bound(ast);
  /** The normalized claim at one span, and the arrow the type table interns
   * for the bind result. */
  const at = (c: SourceClaims, pos: Span) => must(
    must(c.functions.find((f) => f.name === "boundArguments"), "the function's claims")
      .expressions.find((e) => e.pos[0] === pos[0] && e.pos[1] === pos[1]),
    `a claim at ${pos.join(":")}`,
  );
  const signature = (c: SourceClaims): Arrow => {
    const labels = at(c, bind.pos).type;
    if (!Array.isArray(labels)) throw Error("the bind result states no labels");
    const clause = must(must(c.types[must(labels[0], "a label")], "a row")[0], "a clause");
    if (typeof clause === "string" || !("arrs" in clause))
      throw Error("the bind result is not an arrow");
    return must(clause.arrs.arrows[0], "an arrow");
  };
  for (const [name, edit] of rows<[string, (a: Ast, c: SourceClaims) => void]>([
    ["remaining arity", (a, c) => signature(c).arguments.push([1, 2])],
    ["bound result", (a, c) => { signature(c).result = [0]; }],
    ["bound argument domain", (a, c) => {
      const call = bound(a);
      const first = must(call.args[0], "a bound argument");
      call.args[0] = {k: "lit", pos: first.pos, lit: {a: "null"}};
      at(c, first.pos).type = [0];
    }],
  ])) {
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
    const r = spawnSync(process.execPath, ["verification/tools/fragment-parse.mts", probe], {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /\.bind requires a known local function/);
  }
  console.log("  SKJS incompleteness: original claims rejected, tsc claims verified; saved prefix versus live capture, escaping thunk, remaining signature and intrinsic gate OK");
} finally { fs.rmSync(work, {recursive: true, force: true}); }
