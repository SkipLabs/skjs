#!/usr/bin/env node
// Null predicates and immutable-variable guard edges are independently checked.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const vm = require("node:vm");
const { spawnSync } = require("node:child_process");
const ts = require("../tools/node_modules/typescript");
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
const ast = JSON.parse(fs.readFileSync(astPath));
const claims = JSON.parse(fs.readFileSync(claimsPath));
const tmp = fs.mkdtempSync(os.tmpdir() + "/null-tests-");
const fn = (c) =>
  c.find((f) => f.file === file).functions.find((f) => f.name === "isNull");
let passed = 0;
function run(mode, a, c, evidence, key = file) {
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
function expect(name, r, accept, reason = "") {
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
  const evidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json"));
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
    fs.readFileSync(tmp + "/evidence.json"),
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
        fn(c).exprs.find(
          (e) => e.pos[0] === a.functions[0].body[0].e.pos[0],
        ).type = { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
      },
      "evidence search failed",
    ],
    [
      "null literal operand claim required",
      (a, c) => {
        const pos = a.functions[0].body[0].e.r.pos;
        fn(c).exprs = fn(c).exprs.filter((e) => e.pos[0] !== pos[0]);
      },
      "no claimed type",
    ],
    [
      "non-null equality remains unsupported",
      (a) => {
        a.functions[0].body[0].e.r.lit = { a: "booleanlit", v: "true" };
      },
      "equality requires a null or undefined literal operand",
    ],
    [
      "loose equality remains unsupported",
      (a) => {
        a.functions[0].body[0].e.op = "==";
      },
      "only strict equality",
    ],
  ]) {
    const a = structuredClone(ast),
      c = structuredClone(claims);
    mutate(a, c);
    expect(name, run("--produce-stateful-source", a, c), false, reason);
  }
  const changed = structuredClone(ast);
  changed.functions[0].body[0].e.op = "!==";
  expect(
    "old evidence rejects opposite equality",
    run("--check-stateful-source", changed, claims, evidence),
    false,
  );
  expect(
    "null guards produce evidence for branch and loop refinements",
    run(
      "--produce-stateful-source",
      JSON.parse(fs.readFileSync(guardAstPath)),
      JSON.parse(fs.readFileSync(guardClaimsPath)),
      undefined,
      guardFile,
      exitAstPath,
      exitClaimsPath,
      exitFile,
    ),
    true,
  );
  const guardAst = JSON.parse(fs.readFileSync(guardAstPath));
  const guardClaims = JSON.parse(fs.readFileSync(guardClaimsPath));
  const guardEvidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json"));
  expect(
    "null guard independent consumption",
    run(
      "--check-stateful-source",
      guardAst,
      guardClaims,
      guardEvidence,
      guardFile,
      exitAstPath,
      exitClaimsPath,
      exitFile,
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
    fs.readFileSync(tmp + "/evidence.json"),
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
  const callback = missingInner
    .find((f) => f.file === guardFile)
    .functions.find((f) => f.name === "callbackGuard");
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
  const ternary = guardAst.functions.find((f) => f.name === "ternaryGuard")
    .body[0].e;
  const logical = guardAst.functions.find((f) => f.name === "logicalNullAnd")
    .body[0].e;
  const coalesce = guardAst.functions.find((f) => f.name === "coalesceBoolean")
    .body[0].e;
  const compound = guardAst.functions.find((f) => f.name === "compoundIf")
    .body[0].cond;
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
  ]) {
    for (const [label, pos] of sites) {
      const missing = structuredClone(guardClaims);
      const f = missing
        .find((f) => f.file === guardFile)
        .functions.find((f) => f.name === name);
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
  changedLogical.functions.find(
    (f) => f.name === "logicalNullAnd",
  ).body[0].e.op = "||";
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
  const expression = nonBooleanLogical.functions.find(
    (f) => f.name === "logicalAndWrite",
  ).body[1].init;
  const leftPos = expression.l.pos;
  expression.l = { k: "lit", pos: leftPos, lit: { a: "null" } };
  const logicalClaims = nonBooleanClaims
    .find((f) => f.file === guardFile)
    .functions.find((f) => f.name === "logicalAndWrite");
  logicalClaims.exprs.find(
    (e) => e.pos[0] === leftPos[0] && e.pos[1] === leftPos[1],
  ).type = { top: false, atoms: [{ a: "null" }] };
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
      guardAst.functions.find((f) => f.name === "compoundIf").body[1].pos[0],
    ],
    [
      "compoundOr",
      guardAst.functions.find((f) => f.name === "compoundOr").body[0].then[0]
        .pos[0],
    ],
  ]) {
    const wrong = structuredClone(guardClaims);
    const f = wrong
      .find((f) => f.file === guardFile)
      .functions.find((f) => f.name === name);
    f.envs
      .find((e) => e.pos[0] === entry)
      .vars.find((v) => v.name === "value").type = {
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
  const compoundClaims = wrongCompound
    .find((f) => f.file === guardFile)
    .functions.find((f) => f.name === "compoundIf");
  compoundClaims.exprs.find(
    (e) => e.pos[0] === compound.pos[0] && e.pos[1] === compound.pos[1],
  ).type = { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
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
  const coalesceFn = wrongCoalesce
    .find((f) => f.file === guardFile)
    .functions.find((f) => f.name === "coalesceBoolean");
  coalesceFn.exprs.find(
    (e) => e.pos[0] === coalesce.pos[0] && e.pos[1] === coalesce.pos[1],
  ).type = { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
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
  const swapped = swappedCoalesce.functions.find(
    (f) => f.name === "coalesceBoolean",
  ).body[0].e;
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
  const ternaryFn = narrowedTernary
    .find((f) => f.file === guardFile)
    .functions.find((f) => f.name === "ternaryGuard");
  ternaryFn.exprs.find(
    (e) => e.pos[0] === ternary.pos[0] && e.pos[1] === ternary.pos[1],
  ).type = { top: false, atoms: [{ a: "null" }] };
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
  reversedGuard.functions[0].body[0].cond.op = "!==";
  expect(
    "null guard evidence rejects a changed observation",
    run(
      "--check-stateful-source",
      reversedGuard,
      guardClaims,
      guardEvidence,
      guardFile,
      exitAstPath,
      exitClaimsPath,
      exitFile,
    ),
    false,
  );
  const guardContext = vm.createContext({});
  vm.runInContext(
    ts.transpileModule(fs.readFileSync(guardFile, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022 },
    }).outputText,
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
  const staleAst = JSON.parse(fs.readFileSync(staleAstPath));
  const staleClaims = JSON.parse(fs.readFileSync(staleClaimsPath));
  // This suite repairs the positive variant; write-observations covers staleFlip.
  staleAst.functions = staleAst.functions.filter(
    (f) => f.name === "staleCompound",
  );
  staleClaims.find((f) => f.file === staleFile).functions = staleClaims
    .find((f) => f.file === staleFile)
    .functions.filter((f) => f.name === "staleCompound");
  expect(
    "compound stale-read reaches an incoming heap obligation",
    run(
      "--produce-stateful-source",
      staleAst,
      staleClaims,
      undefined,
      staleFile,
    ),
    false,
    "source incoming edge obligation at",
  );
  const { candidate } = require("./skjs-unsound/compound-write-candidate.js");
  const { claims: weakened, edits } = candidate(
    staleAst,
    staleClaims,
    staleFile,
  );
  assert.equal(edits.length, 4);
  const exportedStale = staleClaims.find((f) => f.file === staleFile)
    .functions[0];
  const exitEntry = exportedStale.envs.find(
    (e) => e.pos[0] === staleAst.functions[0].body[2].pos[0],
  );
  const exitCell = exitEntry.vars.find((v) => v.name === "cell");
  assert.equal(exitCell.type.atoms.length, 2);
  assert(exitCell.type.atoms.every((a) => a.a === "record"));
  assert(
    exitCell.type.atoms.some(
      (a) =>
        JSON.stringify(a.fields[0].read) !== JSON.stringify(a.fields[0].write),
    ),
  );
  assert(
    exitCell.type.atoms.some(
      (a) =>
        JSON.stringify(a.fields[0].read) === JSON.stringify(a.fields[0].write),
    ),
  );
  assert(
    !exportedStale.unavailableTypes.some(
      (d) =>
        d.kind === "entry" &&
        d.pos[0] === exitEntry.pos[0] &&
        d.binding === "cell",
    ),
  );
  // Exercise missing-type metadata independently of the now-exportable union.
  const missingStaleClaims = structuredClone(staleClaims);
  const missingStale = missingStaleClaims.find((f) => f.file === staleFile)
    .functions[0];
  missingStale.envs
    .find((e) => e.pos[0] === exitEntry.pos[0])
    .vars.find((v) => v.name === "cell").type = { unsupported: true };
  missingStale.unavailableTypes.push({
    kind: "entry",
    pos: exitEntry.pos,
    binding: "cell",
    reason: "unexpanded-type",
  });
  const { fromSkjs, verifySkjs } = require("../tools/annotate-source.js");
  const staleText = fs.readFileSync(staleFile, "utf8");
  const actualReport = verifySkjs(
    staleFile,
    staleText,
    staleClaims,
    staleFile,
    fromSkjs(staleText, staleFile, staleClaims, "skjs"),
    verifier,
    10,
  ).results[0];
  assert.equal(actualReport.status, "not-established");
  assert.equal(actualReport.obligation.phase, "proof-search");

  const originalReport = verifySkjs(
    staleFile,
    staleText,
    missingStaleClaims,
    staleFile,
    fromSkjs(staleText, staleFile, missingStaleClaims, "skjs"),
    verifier,
    10,
  ).results[0];
  assert.equal(originalReport.stage, "source-extraction");
  assert.equal(originalReport.location.kind, "unavailable-type-claim");
  assert.equal(originalReport.location.binding, "cell");
  assert.equal(
    originalReport.location.start,
    staleAst.functions[0].body[2].pos[0],
  );
  assert.equal(originalReport.obligation, undefined);
  assert.equal(originalReport.location.reason, "unexpanded-type");
  for (const mode of ["absent", "unknown", "malformed"]) {
    const variant = structuredClone(missingStaleClaims);
    for (const f of variant.find((f) => f.file === staleFile).functions) {
      if (mode === "absent") delete f.unavailableTypes;
      else if (mode === "malformed") f.unavailableTypes = { bad: true };
      else for (const d of f.unavailableTypes) d.reason = "future-reason";
    }
    const result = verifySkjs(
      staleFile,
      staleText,
      variant,
      staleFile,
      fromSkjs(staleText, staleFile, variant, "skjs"),
      verifier,
      10,
    ).results[0];
    const expected = structuredClone(originalReport);
    if (mode === "unknown") expected.location.reason = "future-reason";
    else delete expected.location.reason;
    assert.deepEqual(result, expected);
  }
  const candidateReport = fromSkjs(staleText, staleFile, weakened, "candidate");
  assert(
    !candidateReport.functions[0].unavailableTypes.some(
      (d) =>
        d.kind === "entry" &&
        d.binding === "cell" &&
        d.pos[0] === originalReport.location.start,
    ),
  );
  // Successful function export follows cell refusal; no refusal may leak through.
  for (const f of guardClaims.find((f) => f.file === guardFile).functions) {
    for (const e of f.exprs.filter((e) =>
      e.type.atoms?.some((a) => a.a === "function"),
    )) {
      assert(
        !f.unavailableTypes.some(
          (d) =>
            d.kind === "expression" &&
            JSON.stringify(d.pos) === JSON.stringify(e.pos),
        ),
      );
    }
  }

  console.log(
    "  unavailable type is distinguished from failed proof search: OK",
  );
  passed++;
  const unavailableExpression = structuredClone(guardClaims);
  unavailableExpression
    .find((f) => f.file === guardFile)
    .functions.find((f) => f.name === "ternaryGuard")
    .exprs.find(
      (e) => e.pos[0] === ternary.pos[0] && e.pos[1] === ternary.pos[1],
    ).type = { unsupported: true };
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
  const staleResult = run(
    "--produce-stateful-source",
    staleAst,
    weakened,
    undefined,
    staleFile,
  );
  expect(
    "direct write leaves an unprovable singleton read claim",
    staleResult,
    false,
    "evidence search failed",
  );
  const staleRead = staleAst.functions[0].body[1].body[1].e.pos;
  assert(staleResult.stderr.includes(`[${staleRead[0]},${staleRead[1]})`));
  const staleRuntime = vm.createContext({});
  vm.runInContext(
    ts.transpileModule(fs.readFileSync(staleFile, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022 },
    }).outputText,
    staleRuntime,
  );
  assert.equal(staleRuntime.staleCompound(null), true);
  assert.equal(staleRuntime.staleCompound(true), false);
  assert.equal(staleRuntime.staleCompound(false), false);
  console.log("  compound stale-refinement runtime counterexample: OK");
  passed++;
  const exitAst = JSON.parse(fs.readFileSync(exitAstPath));
  const exitClaims = JSON.parse(fs.readFileSync(exitClaimsPath));
  expect(
    "SKJS null loop-exit claims are insufficient",
    run("--produce-stateful-source", exitAst, exitClaims, undefined, exitFile),
    false,
  );
  const repaired = structuredClone(exitClaims);
  const exitFn = repaired.find((f) => f.file === exitFile).functions[0];
  const ret = exitAst.functions[0].body[1];
  const boolean = { top: false, atoms: [{ a: "boolean" }] };
  exitFn.envs
    .find((e) => e.pos[0] === ret.pos[0])
    .vars.find((v) => v.name === "value").type = boolean;
  exitFn.exprs.find((e) => e.pos[0] === ret.e.pos[0]).type = boolean;
  expect(
    "repaired null loop-exit claims produce evidence",
    run("--produce-stateful-source", exitAst, repaired, undefined, exitFile),
    true,
  );
  const exitEvidence = JSON.parse(fs.readFileSync(tmp + "/evidence.json"));
  expect(
    "null loop-exit repair is independently consumed",
    run("--check-stateful-source", exitAst, repaired, exitEvidence, exitFile),
    true,
  );
  const wrong = structuredClone(repaired);
  wrong
    .find((f) => f.file === exitFile)
    .functions[0].envs.find((e) => e.pos[0] === ret.pos[0])
    .vars.find((v) => v.name === "value").type = {
    top: false,
    atoms: [{ a: "null" }],
  };
  expect(
    "null loop-exit cannot retain the opposite refinement",
    run("--produce-stateful-source", exitAst, wrong, undefined, exitFile),
    false,
  );
  vm.runInContext(
    ts.transpileModule(fs.readFileSync(exitFile, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022 },
    }).outputText,
    guardContext,
  );
  for (const value of [true, false])
    assert.equal(guardContext.exitGuard(value), value);
  const context = vm.createContext({});
  vm.runInContext(
    ts.transpileModule(fs.readFileSync(file, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022 },
    }).outputText,
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
