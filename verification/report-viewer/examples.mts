import type { Case } from "../ocaml-producer/cases.mts";
import { cases } from "../ocaml-producer/cases.mts";

// These files are exercised through the current source consumer by run.sh.
const stateful = [
  "basic",
  "undefined",
  "cells",
  "records",
  "closures",
  "loops",
  "loop-transfers",
  "primitive-callbacks",
  "cell-conjunction",
  "negation",
  "null-tests",
  "named-unit-comparisons",
  "null-guards",
  "numbers",
  "numeric-comparisons",
  "mutable-locals",
  "mutable-parameters",
  "captured-local-guards",
  "mutable-locals-guard",
  "mutable-locals-numeric",
  "nullish-assignment",
  "declaration-list",
  "object-patterns",
  "casts",
  "strings",
  "distinct-cells",
  "singleton-operands",
  "computed-keys",
  "arithmetic",
  "logical-assignments",
  "void-results",
  "readonly-views",
  "arrays",
].map((name) => `verification/tests/stateful-source/${name}.ts`)
  .concat("verification/tests/export-snapshots/inferred-replacement.ts");
const callables = ["unions", "factories", "arguments", "cells", "thunks", "arity", "guards", "function-field", "receiver-call"].map((name) => `verification/tests/callables/${name}.ts`);
const callableBoundaries = ["verification/tests/callables/call-objects.ts"];
// Rigid type parameters and their bounds. Checked under the source generic
// rules rather than the graph request, and verified like any other example.
const generics = [
  "generic-identity",
  "generic-aliases",
  "generic-extends",
  "generic-bodies",
].map((name) => `verification/tests/stateful-source/${name}.ts`);
const supported = [...stateful, ...callables, ...generics];
/*
 * The OCaml producer's own fixtures. `ocaml-producer/cases.mts` is its
 * inventory — which case is expected to verify, which is a negative control,
 * and which names a gap — so the lists below are read from it rather than
 * written again here, and a case added there is offered by the reader without
 * anything else changing. Listing one never implies it is verified.
 */
const ocamlExamples = (kinds: Case["kind"][]) =>
  cases
    .filter((c) => kinds.includes(c.kind))
    .map((c) => `verification/ocaml-producer/examples/${c.file}.ts`);
const groups = [
  { label: "Current verifier examples", files: stateful },
  { label: "Callables", files: [...callables, ...callableBoundaries] },
  { label: "Generics · rigid parameters and bounds", files: generics },
  {
    label: "Claim repair · producer rejects",
    files: ["verification/tests/partial-claims.ts"],
  },
  {
    label: "SKJS incomplete · safe programs rejected",
    files: [
      "verification/tests/skjs-incomplete/negated-loop-exit.ts",
      "verification/tests/skjs-incomplete/singleton-negation.ts",
      "verification/tests/skjs-incomplete/null-loop-exit.ts",
      "verification/tests/skjs-incomplete/write-refined-read.ts",
      "verification/tests/skjs-incomplete/empty-domain-escape.ts",
      "verification/tests/skjs-incomplete/undefined-completes.ts",
      "verification/tests/skjs-incomplete/arrow-intersection.ts",
      "verification/tests/skjs-incomplete/bound-arguments.ts",
    ],
  },
  {
    label: "SKJS unsound · unsafe programs accepted",
    files: [
      "verification/tests/skjs-unsound/captured-refinement.ts",
      "verification/tests/skjs-unsound/never-completes.ts",
      "verification/tests/skjs-unsound/arrow-intersection.ts",
      "verification/tests/skjs-unsound/beyond-precision.ts",
    ],
  },
  {
    label: "SKJS repaired · unsafe programs rejected",
    files: ["verification/tests/skjs-unsound/compound-write-refinement.ts"],
  },
  {
    label: "Unsupported examples · expected limitations",
    files: [
      "typeof_narrow",
      "mutable_binding",
    ].map((name) => `verification/tests/unsupported/${name}.ts`),
  },
];
/*
 * Two lists, because they answer different questions. `groups` is corpus
 * policy: `verification/examples.mts` runs SKJS and tsc over every file in it
 * and holds each function to `expectedVerified`. The reader's picker is a way
 * to reach a file, so it also offers another producer's fixtures, which carry
 * their own expectations and are no part of that policy.
 */
const viewerGroups = [
  ...groups,
  {
    label: "OCaml producer · verified fixtures",
    files: ocamlExamples(["positive"]),
  },
  {
    label: "OCaml producer · negative controls and named gaps",
    files: ocamlExamples(["negative", "gap"]),
  },
];
export { supported, groups, viewerGroups };
