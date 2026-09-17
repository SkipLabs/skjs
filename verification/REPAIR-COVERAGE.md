# Increasing repair coverage

This is the continuation guide for extending the verification pipeline over the
SKJS repair regressions. The checker repair objective lives in
[skjs-improvement.md](../docs/skjs-improvement.md); architecture and semantic
boundaries live in [DESIGN.md](DESIGN.md). Preserve SKJS acceptance, inference
and diagnostics. Behavior-preserving claim export improvements are in scope.

## Start here

Read [AGENTS.md](AGENTS.md), inspect `git status` and the current diff, then read
[repair-work.census](corpus/repair-work.census). Do not assume the last commit
contains all completed work. Pick an original repair function, inspect its full
source and raw claims, and identify the first actual obstruction before changing
syntax or proof search. A gate disappearing is progress, but is not yet a newly
verified repair.

There are three different measurements:

| Measurement | Command | What it counts |
| --- | --- | --- |
| Repair coverage | `make verify-census` | Original repair functions accepted by SKJS whose exported claims verify |
| Curated examples | `make verify-examples` | Viewer examples, with separate SKJS and TS producer/proof outcomes |
| Regression suites | `make verify-test` | Test executables, including rejection and mutation tests |

The repair selector is [repair-work.json](corpus/repair-work.json). It selects
named top-level functions introduced since the repair arc began, in
`tests/expect-error/*.ts`; it does not count all functions in an edited file.
The extractor carries other top-level context, including ambient declarations,
aliases, classes and variables. It omits other named function implementations;
it is not a dependency resolver. Context being available to SKJS does not mean
the source adapter can model its values.

`make verify-census UPDATE=1` records a new baseline. Review every changed row,
including changes in producer acceptance and the denominator. A refusal is a
measurement, not a test failure; baseline drift and invalid certificates are
failures. The standard census currently measures SKJS, not TS. Use both producers
on the targeted fixture to distinguish shared adapter gaps from export gaps.

The census abbreviates and normalizes failure messages. Its `unproved` category
includes adapter refusals and unavailable claims, not just failed proof search.
Each row reports only the first obstruction. Groups are not additive estimates
of the work remaining.

## Checkpoint: 17 September 2026

The working-tree baseline is **14/115 verified**, out of 315 selected functions:
200 SKJS-rejected, 89 gated, 12 unproved. The separate curated run had 53 files,
215 verified functions, 6 search failures and 16 unavailable checks; the suite
run had 53 suites. These are checkpoint results, not permanent expectations;
the baseline and fresh command output are authoritative.

Recent repair gains were numeric heap predicates (`checkedEvolvingCapture`),
local nullish assignment (`localFallback`), and inferred object replacement
(`checkedMutableObjectReplacement`): 11 → 12 → 13 → 14.
TS observation fixes also improved curated coverage without themselves moving
this SKJS repair count.

The inferred replacement implementation is committed in `59eb0637`, following
`60d5468b`, the pre-change export snapshot. `46b3a7b7` committed local `??=`
lowering. The replacement implementation includes:

- `src/SkjsTypeClaims.sk` exports unions containing saved substitutions without
  dropping alternatives, consulting live substitutions, or solving constraints.
  `tests/TypeClaimSnapshot.sk` tests saved versus live state, missing bounds and
  cycles; the exporter snapshot records the new output.
- `SourceExtraction.lean` distinguishes a mutable local's private holder from
  the source object it contains, including separate local-content and field
  snapshot keys. It supports stable read-only field guards through that holder.
- `tsc-claims.mts` gives ordinary assignment expressions the exported RHS type,
  keeping contextual allocation contracts consistent. This does not apply to
  `??=`, whose result also includes the skipped arm.
- `tests/inferred-replacement.mts` checks both producers and certificate
  consumption, runtime observations, and rejection of a forged local assertion
  that tries to borrow an object-field snapshot. Its source is shared with the
  export snapshot and viewer corpus.

Do not recreate this completed work. Validation before committing passed: full SKJS
suite (isolated), 53 verification suites, full Lean build, curated expectations,
repair census, and the node unchecked audit (0 `any`, 9 decoder `as`, 0 `!`).
A concurrent SKJS test run had subprocess crashes; an isolated rerun passed.
Avoid overlapping full SKJS tests with suite/census container workloads.

## Inspected blockers

Paths below are relative to `tests/expect-error/`. These observations identify
where to investigate, not a promise that one extension will verify each row.

| Cases | Observed obstruction and additional caveats |
| --- | --- |
| `call-effect-boundaries.ts`: `clearEffect`, `postCallGuard`; `captured-read-stability.ts`: `checkedAliasChain`; `field-refinement.ts`: `inferredFieldComparison`; `unsound-refinement.ts`: `assignmentResultSnapshot`, `checkedAfterWrite` | External object parameters. Structural TypeScript annotations do not establish the model's plain heap-object behavior. Getters, proxies and external effects need a justified boundary. Do not simply remove the gate. |
| `obj-literal-var-field-growth.ts`: `retainedReceiver` | Unavailable expression claim at extracted span `[185,209)`. Inspect raw `unavailableTypes` next; this has not been established to reach numeric proof search. There is a different, SKJS-rejected function with the same name in `unsound-refinement.ts`. |
| `captured-read-stability.ts`: `checkedGenericCallResult` | Unavailable expression claim at extracted span `[551,574)`, involving ambient generic factory `makeCapturedGenericCell`. Reinspect the current raw reason after the saved-substitution export change; the earlier environment blocker has changed. |
| `captured-read-stability.ts`: `evolvedInferredSnapshotStillString` | General string type outside the supported source types. |
| `binding-initialization.ts`: `conditionBeforeLocal` | Reads top-level `seed` before declaring an inner `seed`. Context extraction carries the declaration, but lowering lacks that external value. Do not diagnose this solely as local shadowing. |
| `captured-read-stability.ts`: `checkedPropertyResult`; `unsound-refinement.ts`: `identityMemberSnapshot` | Nested record claims refused. Both also have external objects; the latter additionally compares object identities. Nested record support alone is insufficient. |
| `binding-initialization.ts`: `earlierDeclarator` | Multiple declarators in one `const`. SKJS supplies one entry environment for the whole declaration list, not an intermediate cut for the second binding. TS site indexing also anchors the whole statement. Preserve left-to-right evaluation and binding visibility without fabricating producer claims. |
| `definite-assignment-tvar-soundness.ts`: `typeofInferredFieldAfterAssignment`, `typeofUndefinedFieldAdmitsInitialValue`; `test_ternary_refinements.ts`: `bothBranchesInitialize` | Uninitialized `let`. Requires an initialization discipline; seeding every private cell with undefined must not weaken the declared write contract or allow a read before initialization. |
| `logical-compound-computed-key.ts`: `computedFallback` | `??=` currently requires a local identifier. Property/computed targets must save receiver and key before the RHS and evaluate each once. String/key restrictions may be the next gate. |

Other first gates include destructuring/defaults, spread/accessors, optional or
readonly fields, arrays/tuples, unknown/generic parameters, implicit returns,
arithmetic and classes. Audit representative full functions before choosing a
large extension. A useful next investigation is the two unavailable-expression
rows above, then multiple declarators; external objects require a design decision,
not just exporter work.

To retain diagnostics for an investigation, follow [census.sh](census.sh):
`census.mts --extract` writes per-function sources and an index, one shared SKJS
export produces claims and diagnostics, then `--report` consumes them. The
wrapper deletes temporary files on exit. Use an explicit temporary directory
under `verification/tests/` when retention is needed so the strict project and
container can see it, and remove it afterwards. Inspect the extracted source
when interpreting offsets. Never rewrite the original regression to fit the
fragment or change the denominator to create a coverage gain.

## Extending the pipeline safely

First decide which layer is missing. [LANGUAGES.md](LANGUAGES.md) maps the typed
languages; [REQUEST-PROTOCOL.md](REQUEST-PROTOCOL.md) owns encodings. The usual
path is source syntax (`fragment.mts`, `fragment-parse.mts`), Lean decoding and
alias expansion (`Fragment.lean`, `GenericAlias.lean`), then
`SourceExtraction.lean` and the shared claim producers. Follow exhaustive match
errors through site traversal, scopes, reporting and tests. Keep semantic
lowering in Lean. A parser extension alone need not change the calculus.

Before implementing, write down evaluation order, result value, binding/storage
lifetime, effects, and required incoming/outgoing assertions for the construct.
Then check the following failure modes from earlier work:

- **Lean soundness does not prove correct JavaScript lowering.** A translated
  graph can be well typed while evaluating the wrong branch, duplicating an
  effect, or returning the wrong value. Source extraction remains trusted;
  see [the trust boundary](DESIGN.md#trust-boundary). Use a distinguishing
  source example and, where there is a credible risk, a graph-shape or execution
  observation check. Moving lowering into Lean does not prove preservation.
- **Separate identities from their contents.** `Tm.letE` is immutable;
  mutable locals use private cells. Source declarations and assignment analysis
  determine storage, not diagnostic descriptors or current producer types.
  The holder's `value` is not the contained object's `value`. Immutable saved
  reads and live mutable identities need distinct snapshot keys. Closure
  capture shares the location but cannot retain arbitrary creation-time facts.
- **Preserve evaluation order and expression results.** Assignment saves its
  RHS once; the calculus write returns null while JavaScript assignment returns
  that saved RHS. Save a property receiver/key before an RHS can rebind it.
  Evaluate record initializers in source order, matching contracts by field
  name rather than annotation order. `??=` evaluates the RHS only on its nullish
  arm. `.call` still evaluates the receiver even when the supported arrow body
  does not use it.
- **Require evidence for observations and joins.** Statement entries are
  supplied cuts, including empty ones. Prove join requirements on every incoming
  edge; do not carry whichever predecessor is convenient. Calls and writes may
  invalidate observations; different source names do not establish nonaliasing.
  A mutable field guard is stable only under the supported effect restrictions.
  Never silently drop an unsupported assertion to obtain acceptance.
- **Keep producers independent and the protocol shared.** TS and SKJS map into
  one source-claim language, including generics. Do not add a producer-specific
  alternate encoding. TS flow facts come from actual valid observation sites;
  do not hoist a later RHS or branch fact to statement entry. Keep contextual
  allocation invariants consistent across child and parent claims. Saved SKJS
  substitutions must stay saved; exporting them must not normalize live state,
  solve inference constraints or drop union alternatives.
- **Respect semantic boundaries.** A broad number is not a finite enumeration;
  do not decide an unknown numeric equality outcome. Structural object types
  do not exclude getters or proxies. Rigid generic parameters, inference
  variables and hidden witnesses have different quantifiers. A failed search
  means no derivation within the budget, not a counterexample or a soundness bug.

## Evidence required before calling an extension done

1. The original repair function, under its original producer claims, reaches
   the intended stage; record the census diff. If another gate appears, state it.
2. Add a small, distinguishing source regression. Check fresh SKJS and TS claims
   when both producers support it, and independently consume the certificates.
   Add an altered-claim rejection that exercises the new trust boundary when
   applicable. Prefer pipeline tests; do not generate costly extracted Lean
   programs without a credible verifier issue.
3. For exporter changes, inspect a before/after snapshot. Preserve producer
   acceptance and diagnostics. Do not turn known incompleteness or unsoundness
   witnesses into expected successes just to make a suite pass.
4. Follow the shared-container/batched setup rules in [AGENTS.md](AGENTS.md).
   Run targeted Lean modules during iteration, then the relevant full build and
   suites. Run `make verify-examples` and `make verify-census` to establish final
   outcomes. Run SKJS tests when `.sk` changes, not for verifier/docs-only edits.
   Run strict node checking from `verification/tools` and the unchecked audit
   for node changes; check the viewer when its types or UI change.
5. Keep `#print axioms` checks and introduce no `sorry` or project axiom. Update
   the owning language/design documentation and baseline, and commit coherent,
   green changes. A docs-only handoff update needs no suite rerun.
