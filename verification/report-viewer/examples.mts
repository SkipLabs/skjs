
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
export { supported, groups };
