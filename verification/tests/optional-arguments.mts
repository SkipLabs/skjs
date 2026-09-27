#!/usr/bin/env node
/*
 * An omitted trailing argument, with and without a default. The machine binds `undefined` in the slot the
 * call leaves empty, so a call may omit a position exactly when that position's
 * contract admits `undefined`. This suite checks that the licence is the
 * contract and nothing else: remove `undefined` from it and the same call must
 * fail, with no actual invented to repair it.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast } from "../tools/fragment.mts";
import type { Arrow } from "../tools/type-graph.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { must } from "./edits.mts";

const [
  astPath,
  claimsPath,
  file,
  verifier,
  tscPath,
  defaultAstPath,
  defaultClaimsPath,
  defaultFile,
  defaultTscPath,
] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "optional-arguments-"));
/** The closure the first function of a fixture binds. */
const firstLambda = (a: Ast) => {
  const statement = must(a.functions[0], "a function").body[0];
  if (statement?.k !== "const") throw Error("expected a const statement");
  const init = must(statement.bindings[0], "a binding").init;
  if (init.k !== "lambda") throw Error("expected a closure");
  return init;
};
let passed = 0;
try {
  // What omission means at run time: the parameter the call does not write
  // holds `undefined`, so the guarded arm runs.
  const source = fs.readFileSync(file, "utf8");
  const execute = (expression: string) => {
    const context = vm.createContext({});
    vm.runInContext(stripTypes(source), context, { timeout: 1000 });
    return vm.runInContext(expression, context, { timeout: 1000 });
  };
  for (const seed of [false, true]) {
    assert.equal(execute(`omittedArgument(${seed})`), seed);
    assert.equal(execute(`writtenArgument(${seed})`), seed);
    assert.equal(execute(`explicitUndefined(${seed})`), seed);
  }
  passed++;
  console.log("  an omitted argument is undefined at run time: OK");

  const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const skjs: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const claims: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
  const input = path.join(work, "ast"),
    contract = path.join(work, "claims"),
    evidence = path.join(work, "evidence");
  const check = (mode: string, a: Ast, c: SourceClaims) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [
      mode.replace("stateful-source", "source-claims"),
      input,
      contract,
      file,
      evidence,
    ];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, { encoding: "utf8" });
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = check(mode, ast, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  passed++;
  console.log("  the TypeScript producer's claims verify independently: OK");

  // SKJS types this source, but every claim mentioning the closure is exported
  // as unavailable: its exporter refuses a signature with an optional
  // parameter. The finding stays visible rather than being repaired here; the
  // corpus records the same gap.
  for (const name of [
    "omittedArgument",
    "writtenArgument",
    "explicitUndefined",
  ]) {
    const f = must(
      fileOf(skjs, file).functions.find((g) => g.name === name),
      `SKJS's claims for ${name}`,
    );
    const reasons = (f.unavailableTypes ?? []).map((u) =>
      typeof u === "object" &&
      u !== null &&
      "reason" in u &&
      typeof u.reason === "string"
        ? u.reason
        : "",
    );
    assert(
      reasons.includes("function-optional-parameter"),
      `${name}: expected the optional-parameter refusal, got ${reasons.join(", ")}`,
    );
  }
  passed++;
  console.log("  SKJS refuses to export an optional parameter: OK");

  /** The arrow this file's closure interns, in one function's claims. */
  const signature = (c: SourceClaims, name: string): Arrow => {
    const f = must(
      c.functions.find((g) => g.name === name),
      "the function's claims",
    );
    for (const e of f.expressions) {
      const labels = e.type;
      if (!Array.isArray(labels) || labels.length !== 1) continue;
      const row = c.types[must(labels[0], "a label")];
      const clause = row && row[0];
      if (clause && typeof clause !== "string" && "arrs" in clause)
        return must(clause.arrs.arrows[0], "an arrow");
    }
    throw Error(`no arrow claim in ${name}`);
  };
  // Label 3 is `undefined`. Removing it from the optional position leaves a
  // contract no omitted argument can meet, and the call that omits it must
  // fail rather than have an actual supplied for it.
  for (const [name, edit] of new Map<string, (c: SourceClaims) => void>([
    [
      "omitted position no longer admits undefined",
      (c: SourceClaims) => {
        const domains = signature(c, "omittedArgument").arguments;
        domains[1] = must(domains[1], "the optional position").filter(
          (l) => l !== 3,
        );
      },
    ],
    [
      "written position no longer admits undefined",
      (c: SourceClaims) => {
        const domains = signature(c, "writtenArgument").arguments;
        domains[1] = must(domains[1], "the optional position").filter(
          (l) => l !== 3,
        );
      },
    ],
    [
      "explicit undefined actual no longer fits",
      (c: SourceClaims) => {
        const domains = signature(c, "explicitUndefined").arguments;
        domains[1] = must(domains[1], "the optional position").filter(
          (l) => l !== 3,
        );
      },
    ],
  ])) {
    const c = structuredClone(claims);
    edit(c);
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(check(mode, ast, c).status, 0, name);
    passed++;
    console.log(`  ${name}: OK`);
  }
  // A default replaces the `undefined` an omitted argument binds. The
  // parameter's own contract is what the body reads; the position admits
  // `undefined` because the call may omit it.
  const defaultSource = fs.readFileSync(defaultFile, "utf8");
  const runDefault = (expression: string) => {
    const context = vm.createContext({});
    vm.runInContext(stripTypes(defaultSource), context, { timeout: 1000 });
    return vm.runInContext(expression, context, { timeout: 1000 });
  };
  for (const seed of [false, true]) {
    assert.equal(runDefault(`omittedDefault(${seed})`), seed);
    assert.equal(runDefault(`writtenArgument(${seed})`), false);
    assert.equal(runDefault(`dependentDefault(${seed})`), seed);
  }
  passed++;
  console.log("  a default replaces the omitted argument at run time: OK");

  const defaultAst: Ast = JSON.parse(fs.readFileSync(defaultAstPath, "utf8"));
  const defaultClaims: SourceClaims = JSON.parse(
    fs.readFileSync(defaultTscPath, "utf8"),
  );
  const checkDefault = (mode: string, a: Ast, c: SourceClaims) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [
      mode.replace("stateful-source", "source-claims"),
      input,
      contract,
      defaultFile,
      evidence,
    ];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, { encoding: "utf8" });
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = checkDefault(mode, defaultAst, defaultClaims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  passed++;
  console.log("  a defaulted parameter verifies independently: OK");

  // The default is an obligation against the type the body reads, and the
  // position it fills is the one a call may omit. Break either and the same
  // closure must fail.
  for (const [name, edit] of new Map<string, (a: Ast, c: SourceClaims) => void>(
    [
      [
        "default outside its parameter's contract",
        (a: Ast) => {
          const lambda = firstLambda(a);
          const p = must(lambda.params[1], "the defaulted parameter");
          const d = must(p.default, "its default");
          if (d.k !== "lit") throw Error("expected a literal default");
          d.lit = { a: "null" };
        },
      ],
      [
        "defaulted position no longer admits undefined",
        (_a: Ast, c: SourceClaims) => {
          for (const row of c.types)
            for (const clause of row)
              if (typeof clause !== "string" && "arrs" in clause)
                for (const arrow of clause.arrs.arrows)
                  arrow.arguments = arrow.arguments.map((labels) =>
                    labels.filter((l) => l !== 3),
                  );
        },
      ],
    ],
  )) {
    const a = structuredClone(defaultAst),
      c = structuredClone(defaultClaims);
    edit(a, c);
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(checkDefault(mode, a, c).status, 0, name);
    passed++;
    console.log(`  ${name}: OK`);
  }
  console.log(`Omitted arguments: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
