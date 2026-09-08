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
      "equality requires a null literal operand",
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
  const coalesce = guardAst.functions.find((f) => f.name === "coalesceBoolean")
    .body[0].e;
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
    for (const present of [true, false]) {
      assert.equal(guardContext.chosenCell(present, value), present && value);
      assert.equal(guardContext.coalesceCell(present, value), present && value);
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
