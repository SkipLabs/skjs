#!/usr/bin/env node
/*
 * Receiver tests: obligations and input validation for SKJS's type claims.
 * Start with an accepted claim set, alter one claim or identifier, and require
 * rejection for the expected reason. This does not test claim faithfulness.
 *
 * Usage: type-claims.js <ast.json> <type-claims.json> <file-key> <verifier> [<other-ast.json>]
 */
"use strict";

const fs = require("fs");
const os = require("os");
const path = require("path");
const { spawnSync } = require("child_process");

const [astPath, typeClaimsPath, fileKey, verifier, otherAstPath] = process.argv.slice(2);
if (!astPath || !typeClaimsPath || !fileKey || !verifier) {
  process.stderr.write(
    "usage: type-claims.js <ast.json> <type-claims.json> <file-key> <verifier> [<other-ast.json>]\n",
  );
  process.exit(2);
}

const baseTypeClaims = JSON.parse(fs.readFileSync(typeClaimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "typeClaims-"));
const clone = (x) => JSON.parse(JSON.stringify(x));
const fileEntry = (typeClaims) => typeClaims.find((f) => f.file === fileKey);

const UNKNOWN = { top: true, atoms: [] };

// Cases may return null when the base program lacks the required feature.
// Categories describe the requirement, not whether a test adds to the proof.
const INVALID_CLAIMS = [
  ["obligation", "narrow an expression to never", "does not contain every value", (c) => {
    const entry = fileEntry(c).functions[0].exprs.find(
      (e) => e.type && !e.type.unsupported && (e.type.top || e.type.atoms.length > 0),
    );
    if (!entry) return null;
    entry.type = { top: false, atoms: [] };
    return c;
  }],
  ["obligation", "narrow a claimed binding to never", "narrows further than the typing rules justify", (c) => {
    const entry = fileEntry(c).functions[0].envs[0].vars.find(
      (v) => v.type && !v.type.unsupported && (v.type.top || v.type.atoms.length > 0),
    );
    if (!entry) return null;
    entry.type = { top: false, atoms: [] };
    return c;
  }],

  // Duplicated signatures must agree with the source type annotations. A mismatch
  // establishes an inconsistent export, not what SKJS actually did internally.
  ["input", "widen a parameter type", "differs from its annotation", (c) => {
    const f = fileEntry(c).functions[0];
    f.params[0].type = UNKNOWN;
    return c;
  }],
  ["input", "narrow a parameter type", "differs from its annotation", (c) => {
    const f = fileEntry(c).functions[0];
    if (f.params[0].type.atoms.length < 2) return null;
    f.params[0].type = { top: false, atoms: [f.params[0].type.atoms[0]] };
    return c;
  }],
  ["input", "widen the return type", "claimed return type differs from its annotation", (c) => {
    fileEntry(c).functions[0].retType = UNKNOWN;
    return c;
  }],

  // A binding SKJS never claimed, as distinct from one it claimed too
  // narrowly. No corpus program exercises this branch.
  ["input", "drop a binding from a claimed environment", "missing the binding", (c) => {
    const f = fileEntry(c).functions[0];
    const env = f.envs[f.envs.length - 1];
    env.vars = env.vars.filter((v) => v.type && v.type.unsupported);
    return c;
  }],

  // Identity: the claims must be bound to this declaration, in this file,
  // and must cover every function the source declares.
  ["input", "shift the function's name position", "no claims for the function", (c) => {
    fileEntry(c).functions[0].namePos[0] += 1;
    return c;
  }],
  ["input", "drop a function from the claims", "the claims cover", (c) => {
    const e = fileEntry(c);
    e.functions = e.functions.slice(1);
    return c;
  }],
  ["input", "rename the source file", "claims contain no entry", (c) => {
    fileEntry(c).file = fileKey + ".other";
    return c;
  }],
];

function runChecker(typeClaimsObj, ast) {
  const p = path.join(tmp, "type-claims.json");
  fs.writeFileSync(p, JSON.stringify(typeClaimsObj));
  const r = spawnSync(verifier, [ast, p, fileKey], { encoding: "utf8" });
  return { ok: r.status === 0, out: ((r.stdout || "") + (r.stderr || "")).trim() };
}

let pass = 0;
let fail = 0;
let skipped = 0;

// Control: the untouched claims must be accepted, or nothing below means
// anything.
const control = runChecker(baseTypeClaims, astPath);
if (!control.ok) {
  process.stdout.write(`  FAIL     control: the real claims were rejected: ${control.out}\n`);
  process.exit(1);
}
process.stdout.write("  OK       control: the real claims are accepted\n");
pass += 1;

for (const [category, name, expected, alter] of INVALID_CLAIMS) {
  const corrupted = alter(clone(baseTypeClaims));
  if (corrupted === null) {
    skipped += 1;
    process.stdout.write(`  skip     ${name} (does not apply to this program)\n`);
    continue;
  }
  const r = runChecker(corrupted, astPath);
  if (r.ok) {
    fail += 1;
    process.stdout.write(`  FAIL     ${name}: ACCEPTED an invalid claim set\n`);
  } else if (!r.out.includes(expected)) {
    fail += 1;
    process.stdout.write(`  FAIL     ${name}: expected "${expected}", got: ${r.out}\n`);
  } else {
    pass += 1;
    const why = r.out.replace(/^reject: [^:]*: /, "").slice(0, 78);
    process.stdout.write(`  OK       [${category}] ${name.padEnd(44)} ${why}\n`);
  }
}

// These two fixtures have different declaration spans. Reusing the claims
// must fail lookup; this is not a general source-content authentication test.
if (otherAstPath) {
  const r = runChecker(baseTypeClaims, otherAstPath);
  if (r.ok) {
    fail += 1;
    process.stdout.write("  FAIL     claims reused for another program: ACCEPTED\n");
  } else if (!r.out.includes("no claims for the function")) {
    fail += 1;
    process.stdout.write(`  FAIL     claims reused for another program: wrong rejection: ${r.out}\n`);
  } else {
    pass += 1;
    const why = r.out.replace(/^reject: [^:]*: /, "").slice(0, 78);
    process.stdout.write(`  OK       [input] ${"claims reused for another program".padEnd(44)} ${why}\n`);
  }
}

fs.rmSync(tmp, { recursive: true, force: true });
process.stdout.write(`\n  ${pass} passed, ${fail} failed, ${skipped} skipped\n`);
process.exit(fail === 0 ? 0 : 1);
