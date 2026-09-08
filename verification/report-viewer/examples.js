"use strict";

// These files are exercised through the current source consumer by run.sh.
const supported = [
  "basic",
  "cells",
  "closures",
  "loops",
  "loop-transfers",
  "primitive-callbacks",
  "negation",
].map((name) => `verification/tests/stateful-source/${name}.ts`);
const groups = [
  { label: "Current verifier examples", files: supported },
  {
    label: "Claim repair · producer rejects",
    files: [
      "verification/tests/partial-claims.ts",
      "verification/tests/counterexamples/negated-loop-exit.ts",
    ],
  },
  {
    label: "Counterexamples · SKJS accepts",
    files: ["verification/tests/counterexamples/captured-refinement.ts"],
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
