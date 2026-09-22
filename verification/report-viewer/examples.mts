import type { Case } from "../ocaml-producer/cases.mts";
import { cases } from "../ocaml-producer/cases.mts";
import type { ExampleGroup, GroupFile } from "./types.ts";

// Paths and descriptions are authored together. The corpus's path-only view
// is derived below, so adding a path cannot bypass the required description.
const examples = (
  directory: string,
  entries: [string, string][],
): GroupFile[] =>
  entries.map(([name, about]) => ({ path: `${directory}/${name}.ts`, about }));

const stateful = [
  ...examples("verification/tests/stateful-source", [
    [
      "basic",
      "Widen a singleton while checking initializer and binding claims separately.",
    ],
    [
      "undefined",
      "Keep undefined distinct at function boundaries and in unions.",
    ],
    [
      "cells",
      "Write through an alias and read through the original cell reference.",
    ],
    [
      "records",
      "Track independent fields, initializer order, and captured field guards.",
    ],
    ["closures", "Read live captured storage after an alias writes to it."],
    ["loops", "Preserve loop invariants without requiring termination."],
    [
      "loop-transfers",
      "Preserve storage contracts across break and continue edges.",
    ],
    [
      "primitive-callbacks",
      "Check callback argument and result contracts for primitive values.",
    ],
    ["cell-conjunction", "Combine invariant contracts on the same location."],
    ["negation", "Reverse Boolean refinements under negation."],
    ["null-tests", "Test null membership in primitive unions."],
    [
      "named-unit-comparisons",
      "Refine against null and undefined singletons obtained through bindings.",
    ],
    [
      "null-guards",
      "Eliminate absent alternatives before using a guarded value.",
    ],
    ["numbers", "Pass and store numbers with family and singleton contracts."],
    [
      "numeric-comparisons",
      "Refine numeric unions by comparing stable snapshots.",
    ],
    [
      "mutable-locals",
      "Keep fixed storage contracts while captured locals change contents.",
    ],
    [
      "mutable-parameters",
      "Assign parameters without losing unrelated refinements.",
    ],
    [
      "captured-local-guards",
      "Retain guarded captured reads only across paths that preserve storage.",
    ],
    [
      "mutable-locals-guard",
      "Guard a live captured local when its reader is invoked.",
    ],
    [
      "mutable-locals-numeric",
      "Separate numeric storage contracts from current-content facts.",
    ],
    [
      "nullish-assignment",
      "Assign a fallback only when a local is null or undefined.",
    ],
    [
      "declaration-list",
      "Evaluate declarators left to right in one statement.",
    ],
    [
      "object-patterns",
      "Destructure fields in order and evaluate defaults only for undefined.",
    ],
    [
      "casts",
      "Check type assertions as obligations rather than assuming them.",
    ],
    ["strings", "Pass, store, and compare string families and singletons."],
    [
      "distinct-cells",
      "Preserve facts about distinct storage while allowing parameter aliases.",
    ],
    [
      "singleton-operands",
      "Refine reads against named or field-held singleton operands.",
    ],
    [
      "computed-keys",
      "Read and write a field named by a checked singleton key.",
    ],
    [
      "arithmetic",
      "Check numeric operations and evaluate compound-write targets once.",
    ],
    [
      "logical-assignments",
      "Conditionally write fields while evaluating their targets once.",
    ],
    [
      "void-results",
      "Discard callback result guarantees while retaining their effects.",
    ],
    [
      "readonly-views",
      "Read through covariant views without granting write access.",
    ],
  ]),
  ...examples("verification/tests/export-snapshots", [
    [
      "inferred-replacement",
      "Export the inferred storage contract across a replacement write.",
    ],
  ]),
];
const callables = examples("verification/tests/callables", [
  [
    "unions",
    "Guard callable alternatives and preserve their argument and result contracts.",
  ],
  [
    "factories",
    "Distinguish private per-call storage from storage shared by closures.",
  ],
  [
    "arguments",
    "Pass and return callbacks that observe live captured storage.",
  ],
  [
    "cells",
    "Replace and recursively invoke callbacks stored in mutable cells.",
  ],
  ["thunks", "Create, return, and replace zero-argument closures."],
  ["arity", "Check multiple arguments and their evaluation order."],
  ["guards", "Refine callable values before invocation."],
  [
    "function-field",
    "Use one object through both its fields and its call signature.",
  ],
  ["receiver-call", "Check explicit .call receivers and forwarded arguments."],
]);
const callableBoundaries = examples("verification/tests/callables", [
  [
    "call-objects",
    "Exercise .call on callable objects at the source boundary.",
  ],
]);
const generics = examples("verification/tests/stateful-source", [
  ["generic-identity", "Check identity once under a rigid type parameter."],
  [
    "generic-aliases",
    "Substitute generic aliases without introducing another type identity.",
  ],
  [
    "generic-extends",
    "Use upper bounds in their declared direction, never in reverse.",
  ],
  [
    "generic-bodies",
    "Preserve rigid types through local copies and multiple parameters.",
  ],
]);
const supported = [...stateful, ...callables, ...generics].map(
  (file) => file.path,
);

// The producer inventory owns each fixture's description and expected boundary.
// Comparison groups reuse it rather than maintaining another description.
const ocamlExample = (c: Case): GroupFile => ({
  path: `verification/ocaml-producer/examples/${c.file}.ts`,
  about: c.area,
});
const ocamlExamples = (kinds: Case["kind"][]): GroupFile[] =>
  cases.filter((c) => kinds.includes(c.kind)).map(ocamlExample);
const ocamlWitnesses = [
  "objects",
  "blocks-bind",
  "top-void",
  "generic-closure",
  "generic-two-calls",
  "generic-bounded",
  "generic-captured-store",
  "generic-callback",
  "generic-dependent-inference",
].map((name) => {
  const c = cases.find((c) => c.file === name);
  if (!c) throw Error(`Unknown OCaml comparison example: ${name}`);
  return ocamlExample(c);
});

const corpusGroups: ExampleGroup[] = [
  {
    label: "Current verifier examples",
    note: "the source suites `make verify` runs",
    files: stateful,
  },
  {
    label: "Callables",
    note: "call signatures, callable objects, arity",
    files: [...callables, ...callableBoundaries],
  },
  {
    label: "Generics · rigid parameters and bounds",
    note: "type parameters under the source generic rules",
    files: generics,
  },
  {
    label: "Claim repair · producer rejects",
    note: "a partial collection, rejected on purpose, to edit back into shape",
    files: examples("verification/tests", [
      [
        "partial-claims",
        "Repair missing and invalid claims in a partially checked source.",
      ],
    ]),
  },
  {
    label: "SKJS incomplete · safe programs rejected",
    note: "findings about SKJS, kept as they are — not bugs to fix here",
    files: examples("verification/tests/skjs-incomplete", [
      [
        "negated-loop-exit",
        "Recover the Boolean refinement established when a negated loop exits.",
      ],
      [
        "singleton-negation",
        "Negating true produces false rather than an arbitrary Boolean.",
      ],
      [
        "null-loop-exit",
        "A loop's exit excludes null even when the null path never terminates.",
      ],
      [
        "write-refined-read",
        "A write establishes precise contents within a fixed Boolean contract.",
      ],
      [
        "empty-domain-escape",
        "A callable with an empty domain has a vacuous result contract.",
      ],
      [
        "undefined-completes",
        "Normal completion satisfies an undefined return contract.",
      ],
      [
        "arrow-intersection",
        "Incomparable callable signatures can have an inhabited intersection.",
      ],
      [
        "bound-arguments",
        "Partial .bind saves argument values while retaining live captures.",
      ],
    ]),
  },
  {
    label: "SKJS unsound · unsafe programs accepted",
    note: "findings about SKJS, kept as they are — do not make one verify",
    files: examples("verification/tests/skjs-unsound", [
      [
        "captured-refinement",
        "A callback invalidates a captured field's singleton refinement.",
      ],
      [
        "never-completes",
        "Normal completion contradicts a never return contract.",
      ],
      [
        "arrow-intersection",
        "Collapsing an inhabited arrow intersection to never permits an invalid result.",
      ],
      [
        "beyond-precision",
        "Distinct numeric spellings can denote the same runtime number.",
      ],
    ]),
  },
  {
    label: "SKJS repaired · unsafe programs rejected",
    note: "an unsoundness since repaired",
    files: examples("verification/tests/skjs-unsound", [
      [
        "compound-write-refinement",
        "A direct write invalidates the refinement established by a compound guard.",
      ],
    ]),
  },
  {
    label: "Producer gaps · OCaml witnesses under SKJS and tsc",
    note: "programs the OCaml producer verifies and another producer cannot claim or establish — findings, kept as they are",
    files: ocamlWitnesses,
  },
  {
    label: "Unsupported examples · expected limitations",
    note: "outside the fragment on purpose; listing one never implies it verifies",
    files: examples("verification/tests/unsupported", [
      ["typeof_narrow", "Narrow a union through successive typeof tests."],
      ["mutable_binding", "Declare a mutable local without an initializer."],
    ]),
  },
];

const viewerGroups: ExampleGroup[] = [
  ...corpusGroups,
  {
    label: "OCaml producer · verified fixtures",
    note: "checked end to end by ocaml-producer/test.mts",
    files: ocamlExamples(["positive"]),
  },
  {
    label: "OCaml producer · negative controls and named gaps",
    note: "expected not to verify — each names the boundary it stops at",
    files: ocamlExamples(["negative", "gap"]),
  },
];

// Type checking rejects omissions. Validate at the common export boundary too:
// Node's type stripping and an empty string must not bypass the contract.
for (const group of viewerGroups) {
  for (const file of group.files) {
    if (
      typeof file.about !== "string" ||
      !file.about.trim() ||
      /[\r\n]/u.test(file.about)
    )
      throw Error(
        `Example needs a non-empty, one-line description: ${file.path}`,
      );
  }
}

// Corpus execution needs paths only; it cannot define another, undescribed list.
const groups = corpusGroups.map(({ label, files }) => ({
  label,
  files: files.map((file) => file.path),
}));
export { supported, groups, viewerGroups };
