
// These files are exercised through the current source consumer by run.sh.
const stateful = [
  "basic",
  "undefined",
  "cells",
  "closures",
  "loops",
  "loop-transfers",
  "primitive-callbacks",
  "cell-conjunction",
  "negation",
  "null-tests",
  "null-guards",
].map((name) => `verification/tests/stateful-source/${name}.ts`);
const callables = ["unions", "factories", "arguments", "cells", "thunks", "arity", "guards", "function-field", "receiver-call"].map((name) => `verification/tests/callables/${name}.ts`);
const callableBoundaries = ["verification/tests/callables/call-objects.ts"];
const supported = [...stateful, ...callables];
const groups = [
  { label: "Current verifier examples", files: stateful },
  { label: "Callables", files: [...callables, ...callableBoundaries] },
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
    ],
  },
  {
    label: "SKJS unsound · unsafe programs accepted",
    files: [
      "verification/tests/skjs-unsound/captured-refinement.ts",
      "verification/tests/skjs-unsound/compound-write-refinement.ts",
      "verification/tests/skjs-unsound/never-completes.ts",
      "verification/tests/skjs-unsound/arrow-intersection.ts",
    ],
  },
  {
    label: "Unsupported examples · expected limitations",
    files: [
      "calls_and_consts",
      "typeof_narrow",
      "mutable_binding",
      "beyond_precision",
    ].map((name) => `verification/tests/unsupported/${name}.ts`),
  },
];
export { supported, groups };
