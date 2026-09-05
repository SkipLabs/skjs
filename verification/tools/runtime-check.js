#!/usr/bin/env node
/*
 * Runtime agreement for the verification experiment.
 *
 * Strips the types, runs the program on Node, and calls every function on
 * representative values drawn from its parameter types. Each returned value
 * must inhabit the declared return type, under the same value semantics the
 * Lean checker uses (a number is its double; -0 and 0 are one value).
 *
 * This is what ties the checker's value domain to a real JavaScript engine.
 * A violation it reports is an unsound acceptance, observed rather than argued.
 *
 * Exit 0: every call agreed. Exit 1: a violation (printed). Exit 2: usage.
 */
"use strict";

const fs = require("fs");
const ts = require("typescript");

// Representative values for one type atom.
function samples(atom) {
  switch (atom.a) {
    case "null": return [null];
    case "undefined": return [undefined];
    case "number": return [0, 1, -1];
    case "string": return ["", "a"];
    case "boolean": return [true, false];
    case "numberlit": return [Number(atom.v)];
    case "stringlit": return [atom.v];
    case "booleanlit": return [atom.v === "true"];
    default: throw new Error(`unknown atom ${atom.a}`);
  }
}

function inhabits(value, ty) {
  if (ty.top) return true;
  return ty.atoms.some((atom) => {
    switch (atom.a) {
      case "null": return value === null;
      case "undefined": return value === undefined;
      case "number": return typeof value === "number";
      case "string": return typeof value === "string";
      case "boolean": return typeof value === "boolean";
      // `===` on numbers, so two spellings of one double agree and -0 === 0.
      case "numberlit": return typeof value === "number" && value === Number(atom.v);
      case "stringlit": return value === atom.v;
      case "booleanlit": return value === (atom.v === "true");
      default: return false;
    }
  });
}

function show(v) {
  return typeof v === "string" ? JSON.stringify(v) : String(v);
}

// Every combination of one sample per parameter, capped so the run stays small.
function argTuples(params, cap) {
  let tuples = [[]];
  for (const p of params) {
    const vals = p.type.atoms.flatMap(samples);
    const next = [];
    for (const t of tuples) for (const v of vals) next.push(t.concat([v]));
    tuples = next.slice(0, cap);
  }
  return tuples;
}

function main() {
  const [file, astPath] = process.argv.slice(2);
  if (!file || !astPath) {
    process.stderr.write("usage: runtime-check.js <file.ts> <ast.json>\n");
    process.exit(2);
  }
  const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const js = ts.transpileModule(fs.readFileSync(file, "utf8"), {
    compilerOptions: { target: ts.ScriptTarget.ES2020 },
  }).outputText;

  const names = ast.functions.map((f) => f.name);
  const mk = new Function(`${js}\nreturn {${names.join(",")}};`);
  const fns = mk();

  const violations = [];
  let calls = 0;
  for (const f of ast.functions) {
    for (const args of argTuples(f.params, 24)) {
      let result;
      try {
        result = fns[f.name](...args);
      } catch (e) {
        violations.push(`${f.name}(${args.map(show).join(", ")}) threw ${e}`);
        continue;
      }
      calls += 1;
      if (!inhabits(result, f.retType)) {
        violations.push(
          `${f.name}(${args.map(show).join(", ")}) returned ${show(result)}` +
            ` (typeof ${typeof result}), which does not inhabit its declared return type`,
        );
      }
    }
  }
  if (violations.length > 0) {
    for (const v of violations) process.stdout.write(`violation: ${v}\n`);
    process.exit(1);
  }
  process.stdout.write(`agreed: ${calls} calls\n`);
}

try {
  main();
} catch (e) {
  process.stderr.write(String((e && e.message) || e) + "\n");
  process.exit(2);
}
