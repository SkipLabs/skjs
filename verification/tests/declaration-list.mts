#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { at, binding, fn, must, stmt } from "./edits.mts";
// Several bindings in one `const` or `let`: one statement entry, initializers
// evaluated left to right in the scope the earlier bindings extend. Both
// producers verify the fixture; edits to the source and to each producer's
// claims show which order, visibility and effects the lowering commits to.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "declaration-list-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown) {
  const ap = path.join(tmp, "ast.json"),
    cp = path.join(tmp, "claims.json"),
    ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, fileKey, ep, "10"], {
    encoding: "utf8",
    timeout: 60000,
  });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    // What was produced is consumed independently, or the acceptance is not one.
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, fileKey, ep], {
      encoding: "utf8",
      timeout: 60000,
    });
    if (checked.status !== 0)
      throw Error(`certificate rejected: ${checked.stderr}`);
  }
  return r;
}
function expect(name: string, r: ReturnType<typeof run>, accept: boolean, message = "") {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || (message && !output.includes(message)))
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  passed++;
  console.log(`  ${name}: OK`);
}
/** The fixture cut down to one function, which each edit is about, and each
 * producer's claims cut down to the same one. */
const only = (a: Ast, name: string): Ast => ({ ...clone(a), functions: [fn(clone(a), name)] });
const skjsFor = (c: SkjsClaims, name: string): SkjsClaims => [
  { ...clone(fileOf(c, fileKey)), functions: [clone(functionOf(c, fileKey, name))] },
];
const tscFor = (d: SourceClaims, name: string): SourceClaims => ({
  ...clone(d),
  functions: [clone(must(d.functions.find((f) => f.name === name), `claims for ${name}`))],
});
const numberLit = (v: string): ClaimType => ({ top: false, atoms: [{ a: "numberlit", v }] });
/** The entry of a statement in the TS document, by the statement's text
 * within the named function. */
const tscEntry = (doc: SourceClaims, name: string, text: string) => {
  const start = source.indexOf(text, source.indexOf(`function ${name}(`));
  assert(start >= 0, `fixture text ${JSON.stringify(text)}`);
  const f = must(doc.functions.find((f) => f.name === name), `claims for ${name}`);
  return must(f.entries.find((e) => e.start === start), `entry at ${JSON.stringify(text)}`);
};

try {
  expect("both producers verify the whole fixture · SKJS", run("stateful-source", ast, claims), true);
  expect("both producers verify the whole fixture · tsc", run("source-claims", ast, tsc), true);

  // Order and visibility: the second initializer reads the first binding.
  // Declared the other way round, that read has nothing to name, and the claim
  // the producer made for `seed` is not consulted to fill it in.
  const reversed = only(ast, "earlierBinding");
  const declaration = stmt(at(reversed.functions[0].body, 0), "const");
  declaration.bindings.reverse();
  expect(
    "a later binding is not visible to an earlier initializer",
    run("stateful-source", reversed, skjsFor(claims, "earlierBinding")),
    false,
    "unbound or uninitialized source variable 'seed'",
  );

  // The one entry is a cut: a forged environment after the list is refused.
  const forgedEntry = skjsFor(claims, "earlierBinding");
  const f = functionOf(forgedEntry, fileKey, "earlierBinding");
  binding(f, source.indexOf("return second"), "second").type = numberLit("3");
  expect(
    "the entry after the list checks every binding",
    run("stateful-source", only(ast, "earlierBinding"), forgedEntry),
    false,
  );

  // The first cell is written by the second declarator's initializer, before
  // the statement completes. A TS entry that says the write did not happen is
  // refused, and so is a source in which it does not.
  const staleContents = tscFor(tsc, "effectInLaterInitializer");
  const returned = tscEntry(staleContents, "effectInLaterInitializer", "return first");
  must(returned.bindings.find((b) => b.name === "first"), "first").type = [6];
  expect(
    "a later initializer's write is observed at the next entry",
    run("source-claims", only(ast, "effectInLaterInitializer"), staleContents),
    false,
  );
  const dropped = only(ast, "effectInLaterInitializer");
  const bindings = stmt(at(dropped.functions[0].body, 0), "let").bindings;
  const second = must(bindings[1], "the second binding");
  second.init = { k: "lit", pos: second.init.pos, lit: { a: "null" } };
  expect(
    "without that write the null result is not established",
    run("stateful-source", dropped, skjsFor(claims, "effectInLaterInitializer")),
    false,
  );

  // The cells are separate: after `first = null`, `second` still holds what it
  // copied, and a claim that `first` kept its Boolean is refused.
  const separate = tscFor(tsc, "laterWriteStaysSeparate");
  const guarded = tscEntry(separate, "laterWriteStaysSeparate", "return second");
  must(guarded.bindings.find((b) => b.name === "first"), "first").type = [1, 2];
  expect(
    "a write to the first cell does not reach the second",
    run("source-claims", only(ast, "laterWriteStaysSeparate"), separate),
    false,
  );

  // The parser admits only what the lowering states: every declarator needs a
  // plain initialized name, and a list inside a closure body has no entries
  // for its later bindings.
  for (const [name, text, message] of [
    ["uninitialized later declarator", "let a = 1, b; return a;", "a `let` needs an initializer"],
    ["destructured later declarator", "const a = 1, { b } = { b: 1 }; return a;", "destructuring is outside the fragment"],
    [
      "declaration list in a closure body",
      "const f = (): number => { const a = 1, b = a; return b; }; return f();",
      "one binding per `const` in a closure body",
    ],
  ] as const) {
    const file = path.join(tmp, "gated.ts");
    fs.writeFileSync(file, `function gated(): number { ${text} }\n`);
    const r = spawnSync(process.execPath, [path.resolve(import.meta.dirname, "../tools/fragment-parse.mts"), file], {
      encoding: "utf8",
    });
    assert.notEqual(r.status, 0, name);
    assert(r.stderr.startsWith("gate:") && r.stderr.includes(message), `${name}: ${r.stderr}`);
    passed++;
    console.log(`  ${name}: gated`);
  }

  // The source means what the claims say it means.
  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("earlierBinding()", context), 2);
  assert.equal(vm.runInContext("laterWriteStaysSeparate(true)", context), true);
  assert.equal(vm.runInContext("laterWriteStaysSeparate(false)", context), false);
  assert.equal(vm.runInContext("laterWriteStaysSeparate(null)", context), false);
  assert.equal(vm.runInContext("effectInLaterInitializer()", context), null);
  assert.equal(vm.runInContext("inferredContracts()", context), 1);
  passed++;
  console.log("  source executions agree with the verified contracts: OK");
  console.log(`Declaration lists: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
