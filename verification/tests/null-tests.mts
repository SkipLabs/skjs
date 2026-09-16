#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import { fromSkjs, verifySkjs } from "../tools/annotate-source.mts";
import type { Ast, Expr, FunctionAst } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { Span } from "../tools/span.mts";
import {
  fileOf,
  functionOf,
  type SkjsClaims,
  type SkjsFunction,
} from "../tools/skjs-claims.mts";
import {
  at as nth,
  binding,
  claimAt,
  claimFrom,
  entryAt,
  expr,
  claimType,
  fn as functionIn,
  last,
  must,
  only,
  record,
  stmt,
  written,
} from "./edits.mts";
// Null predicates and immutable-variable guard edges are independently checked.






const [
  astPath,
  claimsPath,
  file,
  verifier,
  guardAstPath,
  guardClaimsPath,
  guardFile,
  exitAstPath,
  exitClaimsPath,
  exitFile,
  staleAstPath,
  staleClaimsPath,
  staleFile,
] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(os.tmpdir() + "/null-tests-");
const fn = (c: SkjsClaims) => functionOf(c, file, "isNull");
/** The equality test this fixture's only function is. */
const test = (a: Ast) => expr(stmt(nth(a.functions[0]!.body, 0), "return").e, "bin");
let passed = 0;
function run(mode: string, a: Ast, c: unknown, evidence?: unknown, key = file) {
  fs.writeFileSync(tmp + "/ast.json", JSON.stringify(a));
  fs.writeFileSync(tmp + "/claims.json", JSON.stringify(c));
  if (evidence)
    fs.writeFileSync(tmp + "/evidence.json", JSON.stringify(evidence));
  const args = [
    mode,
    tmp + "/ast.json",
    tmp + "/claims.json",
    key,
    tmp + "/evidence.json",
  ];
  if (mode.startsWith("--produce")) args.push("10");
  const r = spawnSync(verifier, args, { encoding: "utf8", timeout: 30000 });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
}
function expect(
  name: string,
  r: { status: number | null; stdout: string; stderr: string },
  accept: boolean,
  reason = "",
) {
  assert.equal(r.status === 0, accept, name + ": " + r.stderr);
  assert((r.stdout + r.stderr).includes(reason), name + ": " + r.stderr);
  console.log("  " + name + ": OK");
  passed++;
}
try {
  expect(
    "null predicate production",
    run("--produce-stateful-source", ast, claims),
    true,
  );
  const evidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json", "utf8"));
  expect(
    "null predicate independent consumption",
    run("--check-stateful-source", ast, claims, evidence),
    true,
  );
  const exported = spawnSync(
    verifier,
    ["--export-source-claims", astPath, claimsPath, file],
    { encoding: "utf8", timeout: 30000 },
  );
  assert.equal(exported.status, 0, exported.stderr);
  const normalized = JSON.parse(exported.stdout).claims;
  expect(
    "normalized null predicate production",
    run("--produce-source-claims", ast, normalized),
    true,
  );
  const normalizedEvidence = JSON.parse(
    fs.readFileSync(tmp + "/evidence.json", "utf8"),
  );
  expect(
    "normalized null predicate consumption",
    run("--check-source-claims", ast, normalized, normalizedEvidence),
    true,
  );
  for (const [name, mutate, reason] of [
    [
      "null result claim cannot invent true",
      (a, c) => {
        claimFrom(fn(c), test(a).pos[0]).type =
          { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
      },
      "evidence search failed",
    ],
    [
      "null literal operand claim required",
      (a, c) => {
        const pos = test(a).r.pos;
        fn(c).exprs = fn(c).exprs.filter((e) => e.pos[0] !== pos[0]);
      },
      "no claimed type",
    ],
    [
      "non-null equality remains unsupported",
      (a) => {
        expr(test(a).r, "lit").lit = { a: "booleanlit", v: "true" };
      },
      "equality requires a null or undefined literal operand",
    ],
    [
      "loose equality remains unsupported",
      (a) => {
        test(a).op = "==";
      },
      "only strict equality",
    ],
  ] as [string, (a: Ast, c: SkjsClaims) => void, string][]) {
    const a = structuredClone(ast),
      c = structuredClone(claims);
    mutate(a, c);
    expect(name, run("--produce-stateful-source", a, c), false, reason);
  }
  const changed = structuredClone(ast);
  test(changed).op = "!==";
  expect(
    "old evidence rejects opposite equality",
    run("--check-stateful-source", changed, claims, evidence),
    false,
  );
  expect(
    "null guards produce evidence for branch and loop refinements",
    run(
      "--produce-stateful-source",
      JSON.parse(fs.readFileSync(guardAstPath, "utf8")),
      JSON.parse(fs.readFileSync(guardClaimsPath, "utf8")),
      undefined,
      guardFile,
    ),
    true,
  );
  const guardAst: Ast = JSON.parse(fs.readFileSync(guardAstPath, "utf8"));
  const guardClaims: SkjsClaims = JSON.parse(fs.readFileSync(guardClaimsPath, "utf8"));
  const guardEvidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json", "utf8"));
  expect(
    "null guard independent consumption",
    run(
      "--check-stateful-source",
      guardAst,
      guardClaims,
      guardEvidence,
      guardFile,
    ),
    true,
  );
  const exportedGuards = spawnSync(
    verifier,
    ["--export-source-claims", guardAstPath, guardClaimsPath, guardFile],
    { encoding: "utf8", timeout: 30000 },
  );
  assert.equal(exportedGuards.status, 0, exportedGuards.stderr);
  const normalizedGuards = JSON.parse(exportedGuards.stdout).claims;
  expect(
    "normalized null guards produce evidence",
    run(
      "--produce-source-claims",
      guardAst,
      normalizedGuards,
      undefined,
      guardFile,
    ),
    true,
  );
  const normalizedGuardEvidence = JSON.parse(
    fs.readFileSync(tmp + "/evidence.json", "utf8"),
  );
  expect(
    "normalized null guards independently consumed",
    run(
      "--check-source-claims",
      guardAst,
      normalizedGuards,
      normalizedGuardEvidence,
      guardFile,
    ),
    true,
  );
  const missingInner = structuredClone(guardClaims);
  const callback = functionOf(missingInner, guardFile, "callbackGuard");
  const guardText = fs.readFileSync(guardFile, "utf8");
  const inner = callback.exprs.find((e) => guardText.slice(...e.pos) === "x");
  assert(inner);
  callback.exprs = callback.exprs.filter((e) => e !== inner);
  expect(
    "closure guard still requires its operand claim",
    run(
      "--produce-stateful-source",
      guardAst,
      missingInner,
      undefined,
      guardFile,
    ),
    false,
    "no claimed type",
  );
  /** The one expression each of these fixtures is about. */
  const returned = (a: Ast, name: string) =>
    stmt(nth(functionIn(a, name).body, 0), "return").e;
  const ternary = expr(returned(guardAst, "ternaryGuard"), "conditional");
  const logical = expr(returned(guardAst, "logicalNullAnd"), "bin");
  const coalesce = expr(returned(guardAst, "coalesceBoolean"), "coalesce");
  const compound = stmt(nth(functionIn(guardAst, "compoundIf").body, 0), "if").cond;
  for (const [name, sites] of [
    [
      "ternaryGuard",
      [
        ["result", ternary.pos],
        ["arm", ternary.else_.pos],
      ],
    ],
    [
      "coalesceBoolean",
      [
        ["result", coalesce.pos],
        ["left", coalesce.left.pos],
        ["right", coalesce.right.pos],
      ],
    ],
    [
      "logicalNullAnd",
      [
        ["result", logical.pos],
        ["left", logical.l.pos],
        ["right", logical.r.pos],
      ],
    ],
    ["compoundIf", [["condition", compound.pos]]],
  ] as [string, [string, Span][]][]) {
    for (const [label, pos] of sites) {
      const missing = structuredClone(guardClaims);
      const f = functionOf(missing, guardFile, name);
      f.exprs = f.exprs.filter(
        (e) => e.pos[0] !== pos[0] || e.pos[1] !== pos[1],
      );
      for (const mode of [
        "--produce-stateful-source",
        "--check-stateful-source",
      ])
        expect(
          `${name} ${label} claim required (${mode})`,
          run(mode, guardAst, missing, guardEvidence, guardFile),
          false,
          "no claimed type",
        );
    }
  }
  const changedLogical = structuredClone(guardAst);
  expr(returned(changedLogical, "logicalNullAnd"), "bin").op = "||";
  expect(
    "old evidence rejects changing AND into OR",
    run(
      "--check-stateful-source",
      changedLogical,
      guardClaims,
      guardEvidence,
      guardFile,
    ),
    false,
  );
  const nonBooleanLogical = structuredClone(guardAst);
  const nonBooleanClaims = structuredClone(guardClaims);
  const expression = expr(
    stmt(nth(functionIn(nonBooleanLogical, "logicalAndWrite").body, 1), "const").init,
    "bin",
  );
  const leftPos = expression.l.pos;
  expression.l = { k: "lit", pos: leftPos, lit: { a: "null" } };
  claimAt(functionOf(nonBooleanClaims, guardFile, "logicalAndWrite"), leftPos).type =
    { top: false, atoms: [{ a: "null" }] };
  expect(
    "logical left operand must be Boolean",
    run(
      "--produce-stateful-source",
      nonBooleanLogical,
      nonBooleanClaims,
      undefined,
      guardFile,
    ),
    false,
  );
  for (const [name, entry] of [
    [
      "compoundIf",
      nth(functionIn(guardAst, "compoundIf").body, 1).pos[0],
    ],
    [
      "compoundOr",
      nth(stmt(nth(functionIn(guardAst, "compoundOr").body, 0), "if").then, 0).pos[0],
    ],
  ] as [string, number][]) {
    const wrong = structuredClone(guardClaims);
    binding(functionOf(wrong, guardFile, name), entry, "value").type = {
      top: false,
      atoms: [{ a: "boolean" }],
    };
    expect(
      `${name} merged alternatives cannot invent a non-null fact`,
      run("--produce-stateful-source", guardAst, wrong, undefined, guardFile),
      false,
    );
  }
  const wrongCompound = structuredClone(guardClaims);
  claimAt(functionOf(wrongCompound, guardFile, "compoundIf"), compound.pos).type =
    { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
  expect(
    "decomposed condition still checks its complete result claim",
    run(
      "--produce-stateful-source",
      guardAst,
      wrongCompound,
      undefined,
      guardFile,
    ),
    false,
  );
  const wrongCoalesce = structuredClone(guardClaims);
  claimAt(functionOf(wrongCoalesce, guardFile, "coalesceBoolean"), coalesce.pos).type =
    { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
  expect(
    "coalescing cannot discard a false left value",
    run(
      "--produce-stateful-source",
      guardAst,
      wrongCoalesce,
      undefined,
      guardFile,
    ),
    false,
  );
  const swappedCoalesce = structuredClone(guardAst);
  const swapped = expr(returned(swappedCoalesce, "coalesceBoolean"), "coalesce");
  [swapped.left, swapped.right] = [swapped.right, swapped.left];
  expect(
    "old evidence rejects swapped coalescing operands",
    run(
      "--check-stateful-source",
      swappedCoalesce,
      guardClaims,
      guardEvidence,
      guardFile,
    ),
    false,
  );
  const narrowedTernary = structuredClone(guardClaims);
  claimAt(functionOf(narrowedTernary, guardFile, "ternaryGuard"), ternary.pos).type =
    { top: false, atoms: [{ a: "null" }] };
  expect(
    "ternary result cannot invent null",
    run(
      "--produce-stateful-source",
      guardAst,
      narrowedTernary,
      undefined,
      guardFile,
    ),
    false,
  );
  const reversedGuard = structuredClone(guardAst);
  expr(stmt(nth(reversedGuard.functions[0]!.body, 0), "if").cond, "bin").op = "!==";
  expect(
    "null guard evidence rejects a changed observation",
    run(
      "--check-stateful-source",
      reversedGuard,
      guardClaims,
      guardEvidence,
      guardFile,
    ),
    false,
  );
  const guardContext = vm.createContext({});
  vm.runInContext(
    stripTypes(fs.readFileSync(guardFile, "utf8")),
    guardContext,
  );
  for (const value of [null, true, false]) {
    for (const name of [
      "nullGuard",
      "ternaryGuard",
      "capturedTernary",
      "presentGuard",
      "negatedGuard",
      "olderGuard",
      "callbackGuard",
      "capturedGuard",
      "effectfulCallbackGuard",
    ])
      assert.equal(guardContext[name](value), value === null ? false : value);
    assert.equal(guardContext.loopGuard(value), false);
    assert.equal(guardContext.coalesceBoolean(value), value ?? true);
    assert.equal(guardContext.coalesceWrite(value), value === null);
    assert.equal(guardContext.coalesceAlias(value), value);
    assert.equal(guardContext.logicalNullAnd(value), value !== null && value);
    assert.equal(guardContext.logicalNullOr(value), value === null || value);
    assert.equal(guardContext.logicalClosure(value), value !== null && !value);
    assert.equal(guardContext.compoundContinue(value), value === null);
    for (const flag of [true, false]) {
      assert.equal(
        guardContext.compoundEffect(value, flag),
        !flag && value !== null ? value : !flag,
      );
      for (const name of ["compoundIf", "rightCompound", "compoundLoop"])
        assert.equal(
          guardContext[name](value, flag),
          value !== null && flag ? value : false,
        );
      for (const name of ["compoundOr", "negatedCompound"])
        assert.equal(
          guardContext[name](value, flag),
          value !== null && !flag ? value : false,
        );
    }
    for (const right of [null, true, false])
      assert.equal(
        guardContext.coalesceNested(value, right),
        value ?? right ?? false,
      );
  }
  for (const value of [true, false]) {
    assert.equal(guardContext.nullableCellRead(value), value);
    assert.equal(guardContext.capturedNullableCell(value), value);
    assert.equal(guardContext.nullableCellWrite(value), true);
    assert.equal(guardContext.optionalCallback(value), !value);
    assert.equal(guardContext.ternaryEffects(value), !value);
    assert.equal(guardContext.coalesceOnce(value), !value);
    assert.equal(guardContext.logicalOnce(value), !value);
    assert.equal(guardContext.logicalAndWrite(value), value);
    assert.equal(guardContext.logicalOrWrite(value), !value);
    for (const present of [true, false]) {
      assert.equal(guardContext.chosenCell(present, value), present && value);
      assert.equal(guardContext.coalesceCell(present, value), present && value);
      assert.equal(guardContext.logicalCell(present, value), present && value);
      assert.equal(
        guardContext.logicalNested(present, value),
        (present && value) || !present,
      );
      assert.equal(
        guardContext.coalesceCallback(present, value),
        present ? !value : value,
      );
      assert.equal(
        guardContext.chosenCallback(present, value),
        present && !value,
      );
    }
  }
  assert.equal(guardContext.maybeCell(false), null);
  assert.equal(guardContext.maybeCell(true).value, true);
  assert.equal(guardContext.maybeCallback(false), null);
  assert.equal(guardContext.maybeCallback(true)(false), true);
  const staleAst: Ast = JSON.parse(fs.readFileSync(staleAstPath, "utf8"));
  const staleClaims: SkjsClaims = JSON.parse(fs.readFileSync(staleClaimsPath, "utf8"));
  const stale = functionOf(staleClaims, staleFile, "staleCompound");
  const staleReturn = stmt(
    nth(stmt(nth(functionIn(staleAst, "staleCompound").body, 1), "while").body, 1),
    "return",
  ).e;
  assert.equal(stale.collection?.completion, "aborted");
  assert.deepEqual(claimAt(stale, staleReturn.pos).type,
    { top: false, atoms: [{ a: "boolean" }] });
  expect(
    "rejected compound witness has a partial first-error export",
    run("--produce-stateful-source", staleAst, staleClaims, undefined, staleFile),
    false,
    "missing statement environment",
  );

  // Metadata diagnostics use a complete valid export, independent of the
  // repaired checker bug and its intentionally partial first-error snapshot.
  const metadataAst = structuredClone(guardAst);
  metadataAst.functions = metadataAst.functions.filter((f) => f.name === "compoundContinue");
  const metadataClaims = structuredClone(guardClaims);
  const metadataFile = fileOf(metadataClaims, guardFile);
  metadataFile.functions = metadataFile.functions
    .filter((f) => f.name === "compoundContinue");
  const lastEntry = last(metadataAst.functions[0]!.body).pos[0];
  const metadataEntry = entryAt(only(metadataClaims, guardFile), lastEntry);
  const missingMetadataClaims = structuredClone(metadataClaims);
  const missingMetadata = only(missingMetadataClaims, guardFile);
  binding(missingMetadata, metadataEntry.pos[0], "cell").type = { unsupported: true };
  must(missingMetadata.unavailableTypes, "the producer's own omissions").push({
    kind: "entry",
    pos: metadataEntry.pos,
    binding: "cell",
    reason: "unexpanded-type",
  });
  const actualReport = verifySkjs(
    guardFile,
    guardText,
    metadataClaims,
    guardFile,
    fromSkjs(guardText, guardFile, metadataClaims, "skjs"),
    verifier,
    10,
  ).results[0];
  assert.equal(actualReport.status, "verified");

  const originalReport = verifySkjs(
    guardFile,
    guardText,
    missingMetadataClaims,
    guardFile,
    fromSkjs(guardText, guardFile, missingMetadataClaims, "skjs"),
    verifier,
    10,
  ).results[0];
  assert.equal(originalReport.stage, "source-extraction");
  // `location` is optional: a result need not say where checking stopped.
  assert(originalReport.location, "the result records where checking stopped");
  assert.equal(originalReport.location.kind, "unavailable-type-claim");
  assert.equal(originalReport.location.binding, "cell");
  assert.equal(originalReport.location.start, lastEntry);
  assert.equal(originalReport.obligation, undefined);
  assert.equal(originalReport.location.reason, "unexpanded-type");
  for (const mode of ["absent", "unknown", "malformed"]) {
    const variant = structuredClone(missingMetadataClaims);
    for (const f of fileOf(variant, guardFile).functions) {
      if (mode === "absent") delete f.unavailableTypes;
      else if (mode === "malformed") written(f).unavailableTypes = { bad: true };
      else
        for (const d of must(f.unavailableTypes, "the producer's own omissions"))
          record(d, "an omission").reason = "future-reason";
    }
    const result = verifySkjs(
      guardFile,
      guardText,
      variant,
      guardFile,
      fromSkjs(guardText, guardFile, variant, "skjs"),
      verifier,
      10,
    ).results[0];
    const expected = structuredClone(originalReport);
    assert(expected.location, "the clone carries the location asserted above");
    if (mode === "unknown") expected.location.reason = "future-reason";
    else delete expected.location.reason;
    assert.deepEqual(result, expected);
  }
  // Successful function export follows cell refusal; no refusal may leak through.
  for (const f of fileOf(guardClaims, guardFile).functions) {
    for (const e of f.exprs.filter((e) =>
      claimType(e).atoms.some((a) => a.a === "function"),
    )) {
      assert(
        !must(f.unavailableTypes, "the producer's own omissions").some(
          (d) =>
            record(d, "an omission").kind === "expression" &&
            JSON.stringify(record(d, "an omission").pos) === JSON.stringify(e.pos),
        ),
      );
    }
  }

  console.log(
    "  unavailable entry metadata is located before proof search: OK",
  );
  passed++;
  const unavailableExpression = structuredClone(guardClaims);
  claimAt(functionOf(unavailableExpression, guardFile, "ternaryGuard"), ternary.pos)
    .type = { unsupported: true };
  const unavailableReport = fromSkjs(
    guardText,
    guardFile,
    unavailableExpression,
    "skjs",
  );
  unavailableReport.functions = unavailableReport.functions.filter(
    (f) => f.name === "ternaryGuard",
  );
  const unavailableResult = verifySkjs(
    guardFile,
    guardText,
    unavailableExpression,
    guardFile,
    unavailableReport,
    verifier,
    10,
  ).results[0];
  assert.equal(unavailableResult.stage, "source-extraction");
  assert.deepEqual(unavailableResult.location, {
    kind: "unavailable-type-claim",
    pos: ternary.pos,
  });
  assert.equal(unavailableResult.obligation, undefined);
  console.log(
    "  unavailable expression type is located before proof search: OK",
  );
  passed++;
  const staleRuntime = vm.createContext({});
  vm.runInContext(
    stripTypes(fs.readFileSync(staleFile, "utf8")),
    staleRuntime,
  );
  assert.equal(staleRuntime.staleCompound(null), true);
  assert.equal(staleRuntime.staleCompound(true), false);
  assert.equal(staleRuntime.staleCompound(false), false);
  console.log("  compound stale-refinement runtime counterexample: OK");
  passed++;
  const exitAst: Ast = JSON.parse(fs.readFileSync(exitAstPath, "utf8"));
  const exitClaims: SkjsClaims = JSON.parse(fs.readFileSync(exitClaimsPath, "utf8"));
  expect(
    "SKJS null loop-exit claims are insufficient",
    run("--produce-stateful-source", exitAst, exitClaims, undefined, exitFile),
    false,
  );
  const repaired = structuredClone(exitClaims);
  const exitFn = only(repaired, exitFile);
  const ret = stmt(nth(exitAst.functions[0]!.body, 1), "return");
  const boolean: ClaimType = { top: false, atoms: [{ a: "boolean" }] };
  binding(exitFn, ret.pos[0], "value").type = boolean;
  claimFrom(exitFn, ret.e.pos[0]).type = boolean;
  expect(
    "repaired null loop-exit claims produce evidence",
    run("--produce-stateful-source", exitAst, repaired, undefined, exitFile),
    true,
  );
  const exitEvidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json", "utf8"));
  expect(
    "null loop-exit repair is independently consumed",
    run("--check-stateful-source", exitAst, repaired, exitEvidence, exitFile),
    true,
  );
  const wrong = structuredClone(repaired);
  binding(only(wrong, exitFile), ret.pos[0], "value").type = {
    top: false,
    atoms: [{ a: "null" }],
  };
  expect(
    "null loop-exit cannot retain the opposite refinement",
    run("--produce-stateful-source", exitAst, wrong, undefined, exitFile),
    false,
  );
  vm.runInContext(
    stripTypes(fs.readFileSync(exitFile, "utf8")),
    guardContext,
  );
  for (const value of [true, false])
    assert.equal(guardContext.exitGuard(value), value);
  const context = vm.createContext({});
  vm.runInContext(
    stripTypes(fs.readFileSync(file, "utf8")),
    context,
    { timeout: 1000 },
  );
  for (const value of [null, true, false]) {
    assert.equal(context.isNull(value), value === null);
    assert.equal(context.nullFirst(value), value === null);
    assert.equal(context.isPresent(value), value !== null);
    assert.equal(context.nullNotFirst(value), value !== null);
    assert.equal(context.nullableCallback(value), value === null);
  }
  assert.equal(context.effectfulNullTest(), true);
  passed++;
  console.log(`Null predicates: ${passed} passed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
