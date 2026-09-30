# Verification regressions and the corpus

`make verify-test` runs the maintained regressions (`verification/run.sh`).
The pipeline's own cases live with the OCaml producer
([`ocaml-producer/cases.mts`](../ocaml-producer/cases.mts), run by
`run-cases.mts` and `test.mts`); Lean tests build alongside the
implementation in `lean/Verification/Model/Tests/`. This directory holds the
suites that check the repository around the pipeline and the example corpus.

| Tests | Coverage |
| --- | --- |
| [`docs.mts`](docs.mts) | Documents: links, anchors and math GitHub renders. |
| [`json-field-names.mts`](json-field-names.mts) | TypeScript, Lean and OCaml use the same JSON field names. |
| [`rule-inventory.mts`](rule-inventory.mts) / `rule-inventory.snap` | The rules REQUEST-PROTOCOL documents are the rules Lean declares. |

## The corpus

`make verify-examples` reports per-function outcomes on the viewer's example
corpus, listed in [`report-viewer/examples.mts`](../report-viewer/examples.mts):
TypeScript's own claims for each file ([tsc claims](tsc-claims/README.md)),
checked by the same verifier. The corpus asserts no outcome; a refusal is a
reported result.

- `stateful-source/`: storage contracts, refinements, loops, generics and the
  operations of the fragment, one phenomenon per file.
- [`callables/`](callables/README.md): call signatures, callable objects,
  arity, receivers and argument lists.

`tsconfig.json` is the regime the corpus is claimed and checked under.

To promote a boundary example, add a pipeline case with a positive witness
and an independent negative control, then remove its expected rejection.
Promotion depends on implemented semantics and checking, not merely on the
parser accepting the syntax.

A negative control must be independent: it must fail the check being added and
pass every shortcut that would also accept the positives. A bad program that
any lowering refuses proves nothing about the new rule. For a universal check,
this means a program that satisfies every observed instance and fails only the
universal obligation — `ocaml-producer/examples/invalid-scheme-capture.ts`
instantiates its binder at `boolean` at every call, so per-call specialization
accepts it and only scheme introduction refuses it. A control must reach that
obligation and fail there; a refusal before any obligation exists is a boundary
fixture, not a control, and is filed as one.

Each example function has a doc comment explaining the behavior or proof
obligation it illustrates. Keep these comments alongside new examples; for
unsupported examples, distinguish the adapter's limitation from a soundness
result. Loop examples say when termination is not established. Comments are
part of the displayed source, so claims are always regenerated rather than
reused with offsets from an earlier source.
