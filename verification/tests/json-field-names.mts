// The parser, the OCaml producer and the Lean verifier exchange JSON documents:
// the Fragment tree with its declaration document, and SourceClaims. Each
// document's fields are written three times: as TypeScript types, as Lean
// decoders, and as the OCaml producer's reads and writes. Nothing compiles one against another, so
// this compares, by text, the field names each one uses, and fails when a
// consumer reads a name no TypeScript type declares, or TypeScript declares a
// name Lean never reads. It checks names only; the suites still decide whether
// a document is understood.
//   node verification/tests/json-field-names.mts
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";

const root = join(import.meta.dirname, "..");
const read = (file: string) => readFileSync(join(root, file), "utf8");

/** Property names a TypeScript file declares. */
const declared = (files: string[]) => new Set(files.flatMap((file) =>
  [...read(file).replace(/\/\*[\s\S]*?\*\//g, "").replace(/\/\/.*/g, "")
    .matchAll(/(?<![\w.])([A-Za-z_]\w*)\??\s*:(?!:)/g)].map((m) => m[1] as string)));

/** Field names a Lean file reads or states: explicit field reads, exact field
 * lists and, where a file decodes structures with `FromJson`, their fields. */
const lean = (files: string[], structures = false) => new Set(files.flatMap((file) => {
  const s = read(file).replace(/\/-[\s\S]*?-\//g, "").replace(/--.*/g, "");
  const exact = [...s.matchAll(/fieldsExactly\s+\S+\s+\[([^\]]*)\]/g)]
    .flatMap((m) => [...(m[1] ?? "").matchAll(/"(\w+)"/g)].map((n) => n[1] as string));
  // Plain and parenthesized arguments separately, since one read can nest in
  // another's argument.
  const reads = [...s.matchAll(/\b(?:jField|field|str|arr|bool|jArr|jStr|jNat|jBool)\s+[^\s()]+\s+"(\w+)"/g),
    ...s.matchAll(/\b(?:jField|field|str|arr|bool|jArr|jStr|jNat|jBool)\s+\([^()]*\)\s+"(\w+)"/g),
    ...s.matchAll(/getObjVal\?\s+"(\w+)"/g),
    ...s.matchAll(/getObjValAs\?\s+\S+\s+"(\w+)"/g)].map((m) => m[1] as string);
  const fields = !structures ? [] : [...s.matchAll(/^structure\s+\w+[^\n]*?\s+where\n((?:[ \t]+.*\n|\n)+?)(?=\S)/gm)]
    .flatMap((m) => [...(m[1] ?? "").matchAll(/^[ \t]+(\w+)\s*:/gm)].map((n) => n[1] as string));
  return [...exact, ...reads, ...fields];
}));

/** Field names the OCaml producer reads from a document. */
const ocamlReads = (file: string) => new Set([...read(file)
  .matchAll(/\b(?:field|text|items|List\.mem_assoc|List\.assoc_opt)\s+"(\w+)"/g)].map((m) => m[1] as string));

/** Field names the OCaml producer writes into an object. */
const ocamlWrites = (file: string) => new Set([...read(file).matchAll(/"(\w+)",/g)].map((m) => m[1] as string));

const missing = (names: Set<string>, from: Set<string>, allowed: Record<string, string>) =>
  [...names].filter((n) => !from.has(n) && !(n in allowed)).sort();

let checked = 0;
const expectSubset = (what: string, names: Set<string>, from: Set<string>, allowed: Record<string, string>) => {
  assert.deepEqual(missing(names, from, allowed), [], `${what}: field names differ; update every side, or record why here`);
  // An exception that no longer applies is itself drift.
  for (const n of Object.keys(allowed)) assert(names.has(n) && !from.has(n), `${what}: stale exception '${n}'`);
  checked++;
};

// The Fragment AST and its declaration document.
{
  const ts = declared(["tools/fragment.mts", "tools/declaration-types.mts", "tools/claim.mts"]);
  const leanNames = lean(["lean/Verification/Model/Source/Fragment.lean",
    "lean/Verification/Model/Source/EquationLowering.lean"]);
  expectSubset("Lean reads of the Fragment", leanNames, ts, {
    envs: "SKJS claims, decoded in Fragment.lean",
    exprs: "SKJS claims, decoded in Fragment.lean",
    vars: "SKJS claims, decoded in Fragment.lean",
    binder: "a source-claims label, lowered in EquationLowering.lean",
    meet: "a source-claims label, lowered in EquationLowering.lean",
    types: "the source-claims document's rows, lowered in EquationLowering.lean",
  });
  expectSubset("OCaml reads of the Fragment", ocamlReads("ocaml-producer/source.ml"), ts, {});
  expectSubset("Fragment fields Lean ignores", ts, leanNames, {
    arguments: "a reference's argument spans are provenance",
    kind: "a root binding's kind is provenance",
    module: "a declaration identity is compared whole",
    v: "a literal atom's value is read by the claim decoder",
  });
}

// The SourceClaims document and its type table.
{
  const ts = declared(["tools/source-claims.mts", "tools/type-graph.mts"]);
  const leanNames = lean(["lean/Verification/Model/Source/SourceClaimJson.lean",
    "lean/Verification/Model/Source/EquationLowering.lean"], true);
  expectSubset("OCaml writes of SourceClaims", ocamlWrites("ocaml-producer/claims.ml"), ts, {});
  expectSubset("SourceClaims fields Lean ignores", declared(["tools/source-claims.mts"]), leanNames, {
    labels: "a tuple element's label, not a field",
  });
}

process.stdout.write(`JSON field names: ${checked} comparisons agree across TypeScript, Lean and OCaml\n`);
