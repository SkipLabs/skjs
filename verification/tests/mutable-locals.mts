#!/usr/bin/env node
import fs from "node:fs";
import assert from "node:assert/strict";
import vm from "node:vm";
import {
  produce as tscProduce,
  close as closeTsc,
} from "../tools/tsc-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import { fileOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { at, claimAt, claimType, expr, fn, only as only_, stmt } from "./edits.mts";
// Private-cell lowering: source execution witnesses complement checked
// certificates, while claim mutations exercise the trusted lowering boundary.

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "mutable-locals-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
const tru: ClaimType = { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
let passed = 0;

function run(a: Ast, c: SkjsClaims) {
  const ap = path.join(tmp, "ast.json"),
    cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(
    verifier,
    ["--produce-stateful-source", ap, cp, fileKey, ep, "10"],
    { encoding: "utf8" },
  );
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(
      verifier,
      ["--check-stateful-source", ap, cp, fileKey, ep],
      { encoding: "utf8" },
    );
    if (checked.status !== 0)
      throw Error(`certificate rejected: ${checked.stderr}`);
  }
  return r;
}
function expect(
  name: string,
  r: ReturnType<typeof run>,
  accept: boolean,
  message = "",
) {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || (message && !output.includes(message)))
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  passed++;
  console.log(`  ${name}: OK`);
}
/** The fixture cut down to one function, which each check is about. */
const only = (a: Ast, name: string): Ast => ({
  ...clone(a),
  functions: [fn(clone(a), name)],
});
const claimsFor = (name: string) => {
  const c = clone(claims);
  const file = fileOf(c, fileKey);
  file.functions = file.functions.filter((f) => f.name === name);
  return c;
};

try {
  for (const name of [
    "capturedReaderObservesWrite",
    "snapshotSurvivesWrite",
    "assignmentYieldsValue",
    "capturedWriterThenRead",
    "mutableTag",
    "mutableFallback",
    "mutableBranch",
  ])
    expect(`${name} verifies`, run(only(ast, name), claimsFor(name)), true);

  // The storage contract is the annotation. Narrow it to `true` and the
  // assignment of `false` no longer meets it: the write is the check.
  const narrowed = only(ast, "capturedReaderObservesWrite");
  stmt(at(narrowed.functions[0]!.body, 0), "let").annot = tru;
  expect(
    "a value outside the storage contract is refused",
    run(narrowed, claimsFor("capturedReaderObservesWrite")),
    false,
  );

  // A read through the cell yields the contract, never a narrowing the
  // producer asserted before a write it did not see.
  const stale = claimsFor("capturedReaderObservesWrite");
  const f = only_(stale, fileKey);
  for (const x of f.exprs)
    if (
      JSON.stringify(claimType(x).atoms) === JSON.stringify([{ a: "boolean" }]) &&
      x.pos[1] - x.pos[0] === 5
    )
      x.type = tru;
  expect(
    "a stale narrowing through the cell is not established",
    run(only(ast, "capturedReaderObservesWrite"), stale),
    false,
  );

  // Assigning to a `const` has no cell to write.
  const toConst = only(ast, "snapshotSurvivesWrite");
  const effect = fn(toConst, "snapshotSurvivesWrite").body.find(
    (s) => s.k === "effect",
  );
  expr(stmt(effect, "effect").e, "assign").name = "saved";
  expect(
    "assignment to an immutable binding is refused",
    run(toConst, claimsFor("snapshotSurvivesWrite")),
    false,
    "not a mutable local",
  );

  // A verifier must check the claims at unused entries as well as expressions.
  for (const missing of [false, true]) {
    const changed = claimsFor("capturedReaderObservesWrite");
    const f = only_(changed, fileKey);
    for (const e of f.envs) {
      if (missing) e.vars = e.vars.filter((v) => v.name !== "value");
      else
        for (const v of e.vars)
          if (v.name === "value") v.type = { top: false, atoms: [] };
    }
    expect(
      "original produces evidence before entry mutation",
      run(only(ast, f.name), claimsFor(f.name)),
      true,
    );
    fs.writeFileSync(path.join(tmp, "claims.json"), JSON.stringify(changed));
    expect(
      "independent consumer rejects false or missing mutable entry",
      spawnSync(
        verifier,
        [
          "--check-stateful-source",
          path.join(tmp, "ast.json"),
          path.join(tmp, "claims.json"),
          fileKey,
          path.join(tmp, "evidence.json"),
        ],
        { encoding: "utf8" },
      ),
      false,
    );
    expect(
      "producer rejects false or missing mutable entry",
      run(only(ast, f.name), changed),
      false,
    );
  }
  const wrongTag = only(ast, "mutableTag");
  wrongTag.functions[0]!.retType = tru;
  const wrongClaims = claimsFor("mutableTag");
  const tagged = only_(wrongClaims, fileKey);
  tagged.retType = tru;
  const ternary = stmt(at(wrongTag.functions[0]!.body, 1), "return").e;
  claimAt(tagged, ternary.pos).type = tru;
  expect(
    "a cell identity cannot justify the false ternary claim",
    run(wrongTag, wrongClaims),
    false,
  );
  const shadow = only(ast, "snapshotSurvivesWrite");
  stmt(at(shadow.functions[0]!.body, 0), "let").name = "seed";
  expect(
    "mutable locals cannot shadow active bindings",
    run(shadow, claimsFor("snapshotSurvivesWrite")),
    false,
    "shadowing",
  );

  // SKJS loses this initial singleton; TS states it and the neutral checker
  // must establish it from the actual allocation, without changing SKJS.
  const ts = tscProduce(fileKey);
  closeTsc();
  ts.ast.functions = ts.ast.functions.filter(
    (f) => f.name === "preciseSnapshot",
  );
  ts.doc.functions = ts.doc.functions.filter(
    (f) => f.name === "preciseSnapshot",
  );
  const ap = path.join(tmp, "snapshot.ast"),
    cp = path.join(tmp, "snapshot.claims"),
    ep = path.join(tmp, "snapshot.proof");
  fs.writeFileSync(ap, JSON.stringify(ts.ast));
  fs.writeFileSync(cp, JSON.stringify(ts.doc));
  expect(
    "TS singleton snapshot verifies",
    spawnSync(
      verifier,
      ["--produce-source-claims", ap, cp, fileKey, ep, "10"],
      { encoding: "utf8" },
    ),
    true,
  );
  expect(
    "TS singleton snapshot evidence consumes",
    spawnSync(verifier, ["--check-source-claims", ap, cp, fileKey, ep], {
      encoding: "utf8",
    }),
    true,
  );
  const context = vm.createContext({});
  vm.runInContext(stripTypes(fs.readFileSync(fileKey, "utf8")), context, {
    timeout: 1000,
  });
  const evaluate = (expression: string) =>
    vm.runInContext(expression, context, { timeout: 1000 });
  assert.equal(evaluate("capturedReaderObservesWrite(true)"), false);
  assert.equal(evaluate("snapshotSurvivesWrite(true)"), true);
  assert.equal(evaluate("preciseSnapshot(true)"), true);
  assert.equal(evaluate("capturedWriterThenRead(true)"), false);
  assert.equal(evaluate("mutableTag(null)"), false);
  assert.equal(evaluate("mutableTag(false)"), true);
  assert.equal(evaluate("mutableFallback(null)"), true);
  assert.equal(evaluate("mutableFallback(false)"), false);
  assert.equal(evaluate("mutableBranch(true)"), false);
  assert.equal(evaluate("mutableBranch(false)"), true);
  console.log(`Mutable locals: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
