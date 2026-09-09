"use strict";

// These files are exercised through the current source consumer by run.sh.
const supported = [
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
const groups = [
  { label: "Current verifier examples", files: supported },
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
    ],
  },
  {
    label: "SKJS unsound · unsafe programs accepted",
    files: [
      "verification/tests/skjs-unsound/captured-refinement.ts",
      "verification/tests/skjs-unsound/compound-write-refinement.ts",
      "verification/tests/skjs-unsound/never-completes.ts",
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
module.exports = { supported, groups };
