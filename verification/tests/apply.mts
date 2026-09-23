#!/usr/bin/env node
/*
 * Function.prototype.apply: tests/callables/apply.ts, certified independently
 * by the TypeScript and OCaml producers. The list is prepared as an
 * array-like — its length, then each index in order — after the target, the
 * receiver and the list are evaluated. The controls below separate that from
 * reading the list earlier and from iterating it, which is what a spread does.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast, Expr } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { check as ocamlCheck } from "../ocaml-producer/check.mts";

const [verifier] = process.argv.slice(2);
const file = "verification/tests/callables/apply.ts";
const source = fs.readFileSync(file, "utf8");
const work = fs.mkdtempSync(path.join(os.tmpdir(), "apply-"));
let passed = 0;
const ok = (what: string) => {
  passed++;
  console.log(`  ${what}: OK`);
};
const execute = (text: string, expression: string) => {
  const context = vm.createContext({});
  vm.runInContext(stripTypes(text), context, { timeout: 1000 });
  return vm.runInContext(expression, context, { timeout: 1000 });
};
const replaced = (text: string, from: string, to: string) => {
  assert(text.includes(from), `the fixture has ${from}`);
  return text.replace(from, to);
};
let snapshots = 0;
function snapshot(text: string): string {
  const dir = path.join(work, `s${snapshots++}`);
  fs.mkdirSync(dir);
  fs.writeFileSync(path.join(dir, "tsconfig.json"), JSON.stringify({
    compilerOptions: { strict: true, noEmit: true, target: "es2022" },
    files: ["source.ts"],
  }));
  const at = path.join(dir, "source.ts");
  fs.writeFileSync(at, text);
  return at;
}
const run = (cmd: string, args: string[]) => {
  const r = spawnSync(cmd, args, { encoding: "utf8", timeout: 120000 });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  return r;
};
function produced(at: string) {
  const parsed = run(process.execPath, ["verification/tools/fragment-parse.mts", at]);
  assert.equal(parsed.status, 0, parsed.stderr);
  const claims = path.join(path.dirname(at), "claims.json");
  const r = run(process.execPath, ["verification/tools/tsc-claims.mts", at, "--out", claims]);
  assert.equal(r.status, 0, r.stderr);
  return {
    ast: JSON.parse(parsed.stdout) as Ast,
    claims: JSON.parse(fs.readFileSync(claims, "utf8")) as SourceClaims,
  };
}
let documents = 0;
function verify(at: string, ast: Ast, claims: SourceClaims, evidence?: unknown) {
  const base = path.join(work, `d${documents++}`);
  fs.writeFileSync(`${base}.ast`, JSON.stringify(ast));
  fs.writeFileSync(`${base}.claims`, JSON.stringify(claims));
  const out = `${base}.evidence`;
  if (evidence === undefined)
    return { ...run(verifier, ["--produce-source-claims", `${base}.ast`, `${base}.claims`, at, out, "10"]), out };
  fs.writeFileSync(out, JSON.stringify(evidence));
  return { ...run(verifier, ["--check-source-claims", `${base}.ast`, `${base}.claims`, at, out]), out };
}

try {
  /* ---------------------------------------------------------- runtime -- */
  for (const seed of [false, true]) {
    assert.equal(execute(source, `orderedReads(${seed})`), !seed);
    assert.equal(execute(source, `applyReceiver(${seed})`), true);
    assert.equal(execute(source, `applyNothing(${seed})`), seed);
    assert.equal(execute(source, `applyAnyLength(${seed}, [true, , false])`), seed);
    // Reading the list before the receiver runs would pass the old element.
    assert.equal(execute(replaced(source, "return first.apply((list[0] = !seed), list);",
      "const a = list[0];\n  const b = list[1];\n  list[0] = !seed;\n  return first.call(null, a, b);"),
      `orderedReads(${seed})`), seed);
    // Another receiver gives another answer: `.apply` passes it.
    assert.equal(execute(replaced(source, "return read.apply(owner, list);",
      "return read.apply({ value: !seed }, list);"), `applyReceiver(${seed})`), false);
  }
  // `.apply` reads indices; a spread iterates. With an iterator of its own the
  // list gives different actuals to each, and an array-like that is not
  // iterable is a list for `.apply` only. The fragment admits neither form,
  // so no program it accepts can tell the two apart; the model is apply's.
  const control = `
    const first = (a, b) => a;
    const xs = [false, false];
    xs[Symbol.iterator] = function* () { yield true; yield true; };
    const arrayLike = { length: 2, 0: true, 1: false };
    [first.apply(null, xs), first(...xs), first.apply(null, arrayLike)];`;
  assert.deepEqual([...execute("", control)], [false, true, true]);
  assert.throws(() => execute("", "((a) => a)(...{ length: 1, 0: true })"), { name: "TypeError" });
  // An array-like literal needs keys that are not names: a gate refusal.
  const arrayLike = run(process.execPath, ["verification/tools/fragment-parse.mts", snapshot(
    '"use strict";\nfunction f(): boolean { const g = (a: boolean): boolean => a; return g.apply(null, { length: 1, 0: true }); }\n')]);
  assert.notEqual(arrayLike.status, 0);
  assert.match(arrayLike.stderr, /^gate:/);
  // Installing an iterator needs `Symbol`, which nothing in the fragment binds.
  const iterator = ocamlCheck(snapshot(
    '"use strict";\nfunction f(): boolean { const xs: [boolean] = [true]; xs[Symbol.iterator] = null; return true; }\n'));
  assert.notEqual(iterator.status, "verified");
  if (iterator.status !== "verified") assert.match(iterator.detail, /unbound name Symbol/);
  ok("runtime: reads after the receiver, the receiver passed, no list no actuals; indices, not iteration");

  /* ------------------------------------------------ both producers -- */
  const at = snapshot(source);
  const { ast, claims } = produced(at);
  const accepted = verify(at, ast, claims);
  assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
  const evidence = JSON.parse(fs.readFileSync(accepted.out, "utf8"));
  assert.equal(verify(at, ast, claims, evidence).status, 0);
  const text = JSON.stringify(evidence);
  assert(text.includes('"lenOf"') && text.includes('"elemAt"'), "the length and the elements are read");
  ok("TypeScript producer: produced and independently consumed");
  const ocaml = ocamlCheck(file);
  assert.equal(ocaml.status, "verified", JSON.stringify(ocaml));
  ok("OCaml producer: every function verified");
  // A null list gives no actuals, as a missing one does. TypeScript types
  // `null` against the empty tuple only loosely; the OCaml producer states it.
  {
    const nullList = snapshot(replaced(source, "return read.apply(owner);", "return read.apply(owner, null);"));
    const o = ocamlCheck(nullList);
    assert.equal(o.status, "verified", JSON.stringify(o));
    ok("a null list: no actuals (OCaml producer)");
  }

  /* ------------------------------------------------------ negatives -- */
  // Evidence for reading after one write does not cover another write.
  {
    const edited = structuredClone(ast);
    let changed = 0;
    const visit = (x: unknown): void => {
      if (Array.isArray(x)) return x.forEach(visit);
      if (!x || typeof x !== "object") return;
      const e = x as Expr;
      if (e.k === "applyWithReceiver" && e.receiver.k === "indexWrite") {
        e.receiver = { k: "lit", pos: e.receiver.pos, lit: { a: "booleanlit", v: "true" } };
        changed++;
      }
      Object.values(x).forEach(visit);
    };
    visit(edited.functions);
    assert.equal(changed, 1);
    const r = verify(at, edited, claims, evidence);
    assert.notEqual(r.status, 0);
    ok("evidence for one receiver expression does not cover another");
  }
  // Evidence without the length read does not match the program.
  {
    const cut = structuredClone(evidence);
    let removed = 0;
    const visit = (x: unknown): void => {
      if (Array.isArray(x)) return x.forEach(visit);
      if (!x || typeof x !== "object") return;
      const o = x as Record<string, unknown>;
      const term = (o.claim as { term?: unknown } | undefined)?.term;
      if (term && typeof term === "object" && "lenOf" in term && removed === 0) {
        (o.claim as { term: unknown }).term = "nul";
        removed++;
      }
      Object.values(o).forEach(visit);
    };
    visit(cut);
    assert.equal(removed, 1);
    assert.notEqual(verify(at, ast, claims, cut).status, 0);
    ok("evidence that skips the length read is refused");
  }
  // A list of unknown length into fixed parameters: TypeScript refuses it
  // too, and the verifier refuses it where the call is written.
  {
    const open = snapshot(replaced(source, "const list: [boolean] = [!seed];", "const list: boolean[] = [!seed];"));
    const p = produced(open);
    const r = verify(open, p.ast, p.claims);
    assert.notEqual(r.status, 0);
    assert.match(r.stdout + r.stderr, /\.apply with a list of unknown length needs a target taking only a rest parameter/);
    ok("a list of unknown length into fixed parameters is a located refusal");
  }
  // A hole reads `undefined`: an element contract without it is refused.
  {
    const holes = snapshot(replaced(source, "    ...rest: (boolean | undefined)[]\n", "    ...rest: boolean[]\n"));
    const p = produced(holes);
    const r = verify(holes, p.ast, p.claims);
    assert.notEqual(r.status, 0);
    assert.match(r.stdout + r.stderr, /may have holes passes `undefined`/);
    ok("a list that may have holes into a rest without `undefined` is refused");
  }
  // `.apply` on a value whose provenance is not a local function is not the
  // intrinsic.
  {
    const r = run(process.execPath, ["verification/tools/fragment-parse.mts", snapshot(
      '"use strict";\nfunction f(g: (a: boolean) => boolean): boolean { return g.apply(null, [true]); }\n')]);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /\.apply requires a known local function/);
    ok("`.apply` on a parameter is not assumed to be the intrinsic");
  }
  console.log(`Apply: ${passed} passed`);
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
