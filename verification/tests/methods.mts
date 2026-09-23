#!/usr/bin/env node
/*
 * Receivers: tests/callables/methods.ts, certified independently by the
 * TypeScript and OCaml producers, and the negatives that must fail at the
 * receiver's own checks. SKJS does not parse a "use strict" directive, so its
 * refusal of this file is reported by the corpus, not hidden here.
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
import { readDiagnostic } from "../tools/diagnostic.mts";

const [verifier] = process.argv.slice(2);
const file = "verification/tests/callables/methods.ts";
const source = fs.readFileSync(file, "utf8");
const work = fs.mkdtempSync(path.join(os.tmpdir(), "methods-"));
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

/** A snapshot of a source in its own directory, under a strict tsconfig, as
 * the producers require. */
let snapshots = 0;
function snapshot(text: string): string {
  const dir = path.join(work, `s${snapshots++}`);
  fs.mkdirSync(dir);
  fs.writeFileSync(
    path.join(dir, "tsconfig.json"),
    JSON.stringify({
      compilerOptions: { strict: true, noEmit: true, target: "es2022" },
      files: ["source.ts"],
    }),
  );
  const at = path.join(dir, "source.ts");
  fs.writeFileSync(at, text);
  return at;
}
const run = (cmd: string, args: string[]) => {
  const r = spawnSync(cmd, args, { encoding: "utf8", timeout: 120000 });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  return r;
};
/** The fragment and the TypeScript producer's claims for a source. */
function produced(at: string) {
  const parsed = run(process.execPath, ["verification/tools/fragment-parse.mts", at]);
  assert.equal(parsed.status, 0, parsed.stderr);
  const claims = path.join(path.dirname(at), "claims.json");
  const r = run(process.execPath, ["verification/tools/tsc-claims.mts", at, "--out", claims]);
  assert.equal(r.status, 0, r.stderr);
  const omissions = JSON.parse(fs.readFileSync(`${claims}.omissions.json`, "utf8"));
  assert.deepEqual(omissions, [], "the producer states every site");
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
    assert.equal(execute(source, `propertyCall(${seed})`), true);
    assert.equal(execute(source, `callRebinds(${seed})`), true);
    assert.equal(execute(source, `savedCallee(${seed})`), true);
    assert.equal(execute(source, `receiverFieldWrite(${seed})`), !seed);
    assert.equal(execute(source, `receiverWrite(${seed})`), !seed);
    assert.equal(execute(source, `bindRebind(${seed})`), !seed);
    assert.equal(execute(source, `boundCall(${seed})`), seed);
    assert.equal(execute(source, `variadicMethod(${seed})`), true);
    assert.equal(execute(source, `tupleSpreadMethod(${seed})`), true);
    assert.equal(execute(source, `elementMethod(${seed})`), seed);
    assert.equal(execute(source, `bindVariadic(${seed})`), false);
    assert.equal(execute(source, `declaredReceiver.call({ value: ${seed} }, true)`), !seed);
    // The bound function reads the live field, not a copy taken at `.bind`.
    assert.equal(execute(replaced(source, "  owner.value = !seed;\n  const rebound",
      "  const rebound"), `bindRebind(${seed})`), seed);
    // Binding the original function instead does take the new receiver.
    assert.equal(execute(replaced(source, "const rebound = bound.bind(other);",
      "const rebound = read.bind(other, false);"), `bindRebind(${seed})`), seed);
    // A copied method is a value: its plain call passes `undefined`, which
    // strict code does not replace.
    const extracted = replaced(source, "const direct = owner.get();",
      "const got = owner.get;\n  const direct = got();");
    assert.throws(() => execute(extracted, `propertyCall(${seed})`), { name: "TypeError" });
    // The arrow keeps its creator's receiver; rebinding with the same object
    // shows the two calls were distinguished.
    assert.equal(execute(replaced(source, "reader.call(second)", "reader.call(first)"),
      `callRebinds(${seed})`), false);
    // Reading the method after the actuals would call the replacement.
    assert.equal(execute(replaced(source, "const first = owner.pick(replace());",
      "const first = (replace() ? owner.pick : owner.pick).call(owner, true);"),
      `savedCallee(${seed})`), false);
  }
  ok("runtime: property, parenthesized and copied calls; .call rebinding; saved callee; live receiver fields; bound receivers");

  /* ------------------------------------------------ both producers -- */
  const at = snapshot(source);
  const { ast, claims } = produced(at);
  const accepted = verify(at, ast, claims);
  assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
  const evidence = JSON.parse(fs.readFileSync(accepted.out, "utf8"));
  const consumed = verify(at, ast, claims, evidence);
  assert.equal(consumed.status, 0, consumed.stdout + consumed.stderr);
  ok("TypeScript producer: produced and independently consumed");
  const ocaml = ocamlCheck(file);
  assert.equal(ocaml.status, "verified", JSON.stringify(ocaml));
  assert.equal(ocaml.phase, "check");
  if (ocaml.status === "verified")
    assert.deepEqual(ocaml.functions, [
      "propertyCall", "callRebinds", "savedCallee", "receiverFieldWrite", "receiverWrite",
      "bindRebind", "boundCall", "variadicMethod", "tupleSpreadMethod", "elementMethod",
      "bindVariadic", "declaredReceiver",
    ]);
  ok("OCaml producer: every function verified");

  /* ------------------------------------------------------ negatives -- */
  // (1) An extracted method needs its receiver: the plain call is a located
  // receiver obligation, for either producer.
  {
    const text = replaced(source, "const direct = owner.get();",
      "const got = owner.get;\n  const direct = got();");
    const bad = snapshot(text);
    const p = produced(bad);
    const r = verify(bad, p.ast, p.claims);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /"role":"method-receiver"/);
    assert.match(r.stderr, /"term":"undef"/);
    // The report reader decodes the obligation, receiver and all.
    const diagnostic = readDiagnostic(r.stderr);
    assert(diagnostic, "the receiver obligation decodes");
    const o = ocamlCheck(bad);
    if (o.status === "unverified") assert.match(o.detail, /"role":"method-receiver"/);
    else assert.fail(`OCaml: ${JSON.stringify(o)}`);
    ok("an extracted method's plain call fails its receiver obligation");
  }
  // (6) A readonly view of the receiver grants no write.
  {
    const text = replaced(source, "flip(this: { value: boolean }): boolean {",
      "flip(this: { readonly value: boolean }): boolean {");
    const bad = snapshot(text);
    const p = produced(bad);
    const r = verify(bad, p.ast, p.claims);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /write to a readonly field 'value'/);
    const o = ocamlCheck(bad);
    if (o.status !== "verified") assert.match(o.detail, /write to a readonly field 'value'/);
    else assert.fail("OCaml: readonly receiver write accepted");
    ok("a receiver write through a readonly view is refused");
  }
  // (7a) A forged receiver: claiming `get` accepts any receiver.
  {
    const forged = structuredClone(claims);
    const top = forged.types.findIndex((row) => row.length === 1 && row[0] === "top");
    const topLabel = top >= 0 ? top : forged.types.push(["top"]) - 1;
    let changed = 0;
    for (const row of forged.types)
      for (const clause of row)
        if (typeof clause !== "string" && "arrs" in clause)
          for (const arrow of clause.arrs.arrows)
            if (JSON.stringify(arrow[0]) !== JSON.stringify([topLabel])) {
              arrow[0] = [topLabel];
              changed++;
            }
    assert(changed > 0, "the fixture has a receiver-dependent signature");
    const r = verify(at, ast, forged);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /closure receiver claim is outside the source annotation/);
    ok("a forged unknown receiver differs from the source annotation");
  }
  // (7b) A dropped receiver premise. A node's checked derivation is its
  // effect proof where it has one; the expression beside it states only the
  // sequent. Every copy of one call's derivation loses its receiver premise.
  {
    const dropped = structuredClone(evidence);
    const nodes: Record<string, unknown>[] = [];
    const visit = (x: unknown): void => {
      if (Array.isArray(x)) return x.forEach(visit);
      if (!x || typeof x !== "object") return;
      const o = x as Record<string, unknown>;
      const term = (o.claim as { term?: unknown } | undefined)?.term;
      if (term && typeof term === "object" && "invoke" in term &&
          Array.isArray(o.premises) && o.premises.length > 1)
        nodes.push(o);
      Object.values(o).forEach(visit);
    };
    visit(dropped);
    const first = nodes[0];
    assert(first, "the evidence has a receiver premise");
    const call = JSON.stringify(first.claim);
    let removed = 0;
    for (const node of nodes)
      if (JSON.stringify(node.claim) === call) {
        (node.premises as unknown[]).splice(1, 1);
        removed++;
      }
    const r = verify(at, ast, claims, dropped);
    assert.notEqual(r.status, 0, "evidence without its receiver premise");
    ok(`one call's receiver premise dropped (${removed} copies) is refused`);
  }
  // (7c) Reused evidence after substituting the receiver.
  {
    const edited = structuredClone(ast);
    const f = edited.functions.find((g) => g.name === "callRebinds");
    assert(f, "the fixture has callRebinds");
    let swapped = 0;
    const visit = (x: unknown): void => {
      if (Array.isArray(x)) return x.forEach(visit);
      if (!x || typeof x !== "object") return;
      const e = x as Expr;
      if (e.k === "callWithReceiver" && e.receiver.k === "id" && e.receiver.name === "second") {
        e.receiver = { ...e.receiver, name: "first" };
        swapped++;
      }
      Object.values(x).forEach(visit);
    };
    visit(f.body);
    assert.equal(swapped, 1);
    const r = verify(at, edited, claims, evidence);
    assert.notEqual(r.status, 0, "evidence for another receiver");
    ok("evidence reused after a receiver substitution is refused");
  }
  // Sloppy code substitutes the global object for `undefined`; the fragment
  // refuses a function that reads `this` there, where it is written.
  {
    const sloppy = snapshot(source.replace('"use strict";\n', ""));
    const parsed = run(process.execPath, ["verification/tools/fragment-parse.mts", sloppy]);
    assert.notEqual(parsed.status, 0);
    assert.match(parsed.stderr, /a function that reads `this` must be strict code/);
    ok("a receiver-dependent function in sloppy code is refused at its span");
  }
  // The independent decoder must still reject a closure whose recorded mode
  // is sloppy, even when supplied with evidence produced for strict code.
  {
    const edited = structuredClone(ast);
    let changed = 0;
    const visit = (x: unknown): void => {
      if (Array.isArray(x)) return x.forEach(visit);
      if (!x || typeof x !== "object") return;
      if ("k" in x && x.k === "lambda" && "receiver" in x) {
        const receiver = x.receiver;
        if (receiver && typeof receiver === "object" && "strict" in receiver) {
          receiver.strict = false;
          changed++;
        }
      }
      Object.values(x).forEach(visit);
    };
    visit(edited);
    assert(changed > 0);
    for (const reused of [undefined, evidence]) {
      const r = verify(at, edited, claims, reused);
      assert.notEqual(r.status, 0);
      assert.match(r.stderr, /a function that reads `this` must be strict code/);
    }
    ok("both evidence entry points reject a sloppy closure mode");
  }
  // Declaration entry points obey the same rule as expressions. In sloppy
  // JavaScript a supplied undefined becomes the global object before the body.
  {
    const text = "function sloppyEntry(this: undefined): undefined { return this; }";
    assert.equal(execute(text, "typeof sloppyEntry.call(undefined)"), "object");
    const bad = snapshot(text);
    const r = run(process.execPath, ["verification/tools/fragment-parse.mts", bad]);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /a function that reads `this` must be strict code/);
    assert.equal(ocamlCheck(bad).status, "unsupported");
    const good = snapshot(text.replace("{ return", '{ "use strict"; return'));
    const p = produced(good);
    const v = verify(good, p.ast, p.claims);
    assert.equal(v.status, 0, v.stderr);
    assert.equal(verify(good, p.ast, p.claims, JSON.parse(fs.readFileSync(v.out, "utf8"))).status, 0);
    assert.equal(ocamlCheck(good).status, "verified");
    ok("declaration receivers require strict code, including a body directive");
  }
  // Arrow bodies have directive prologues too. The nested ordinary function
  // inherits strictness even though the arrow inherits its receiver lexically.
  {
    const text = `function nestedStrict(): boolean {
      const outer = (): boolean => {
        "use strict";
        const f = function(this: undefined): undefined { return this; };
        return f() === undefined;
      };
      return outer();
    }`;
    assert.equal(execute(text, "nestedStrict()"), true);
    const good = snapshot(text);
    const p = produced(good);
    const v = verify(good, p.ast, p.claims);
    assert.equal(v.status, 0, v.stderr);
    assert.equal(verify(good, p.ast, p.claims, JSON.parse(fs.readFileSync(v.out, "utf8"))).status, 0);
    assert.equal(ocamlCheck(good).status, "verified");
    const bad = snapshot(text.replace('"use strict";', '"use sloppy";'));
    const r = run(process.execPath, ["verification/tools/fragment-parse.mts", bad]);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /a function that reads `this` must be strict code/);
    ok("arrow directive prologues establish inherited strictness");
  }
  {
    const text = `function capturedSloppy(this: undefined): undefined {
      const read = (): undefined => { "use strict"; return this; };
      return read();
    }`;
    assert.equal(execute(text, "typeof capturedSloppy.call(undefined)"), "object");
    const bad = snapshot(text);
    const r = run(process.execPath, ["verification/tools/fragment-parse.mts", bad]);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /a function that reads `this` must be strict code/);
    ok("a strict arrow cannot undo its creator's sloppy receiver conversion");
  }
  // `this` in a function declaration names nothing the fragment binds.
  {
    const bad = snapshot('"use strict";\nfunction f(): boolean { return this === undefined; }\n');
    const r = run(process.execPath, ["verification/tools/fragment-parse.mts", bad]);
    assert.notEqual(r.status, 0);
    assert.match(r.stderr, /`this` where no receiver is bound/);
    ok("`this` where no receiver is bound is a gate refusal");
  }
  console.log(`Receivers: ${passed} passed`);
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
