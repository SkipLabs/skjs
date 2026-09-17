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

The baseline is **35/116 verified**, out of 319 selected functions:
203 SKJS-rejected, 72 gated, 9 unproved. The separate curated run had 56 files,
235 verified functions, 7 search failures and 13 unavailable checks; the suite
run had 62 suites. These are checkpoint results, not permanent expectations;
the baseline and fresh command output are authoritative.

Recent repair gains were numeric heap predicates (`checkedEvolvingCapture`),
local nullish assignment (`localFallback`), inferred object replacement
(`checkedMutableObjectReplacement`), declaration lists (`earlierDeclarator`)
object patterns (`inferredFieldDefault`, `checkedStateAfterDefault`) and
object parameters assumed at their annotation (`clearEffect`, `postCallGuard`,
`checkedAliasChain`, `checkedAfterWrite`) and type assertions (`castScalarSnapshot`,
`satisfiesSnapshot`, `nonNullScalarSnapshot`) and distinct-location links, under
which a write to a fresh private cell keeps a guard's fact about a parameter's
field (`assignmentResultSnapshot`), and singleton comparisons whose other
operand is an effect-free name or field read rather than a literal
(`inferredFieldComparison`), and element access with a computed key claimed
as a string singleton, with ternaries branching in the graph so an effect in
the key is seen (`keyInitializesRhs`), and arithmetic on numbers with compound
assignments and increments, plus a Boolean typing for a numeric test the operand's
type does not settle (`mutateConstantObject`, `annotatedCompoundKey`,
`computedUpdate`), and logical assignments to fields and elements
(`selectedReceiver`, `computedAnd`, `computedFallback`):
11 → 12 → 13 → 14 → 15 → 17 → 21 → 24 → 27 → 28 → 29 → 32 → 35.
TS observation fixes also improved curated coverage without themselves moving
this SKJS repair count.

The retained-binding-contract repair (`a1a84a9d`, following baseline tests in
`56a4575a`) added four regressions: two compatible
cases verify, and two incompatible replacements reject. Of the previous 315
functions, `evolvedInferredSnapshotStillString` moved from unproved to
SKJS-rejected; none moved to verified. Thus 24 → 26 reflects the two new positive
regressions, not additional coverage of the previous corpus. All 57 pipeline
suites, the full Lean build and full SKJS tests passed; curated expectations
had zero mismatches or runner errors.

Declaration lists (`const a = …, b = …;` and the `let` form) are lowered in
Lean under the statement's one entry, left to right, each initializer in the
scope the earlier bindings extend; the Fragment statement now carries a
`bindings` list on both sides, so every consumer was updated rather than
silently reading one declarator. Inside closure bodies a list stays gated.
`tests/declaration-list.mts` checks both producers, forged entries, reversed
and dropped declarators, cross-cell contents, the gates and source executions;
`DeclarationListTests.lean` traces the lowered program of the separate-cell
case, since source executions alone do not show what the lowering does. While
building it, one boundary was recorded, not fixed: a TS entry claim narrower
than a cell's contract (`second: boolean` after `let second: boolean | null =
first` with `first` narrowed to `boolean`) is not re-established after a
write to a different cell, whether or not the declarations share a statement.
The fixture seeds its cells from a `boolean | null` parameter to stay within
the supported contents tracking.

Object patterns on `const` (`const { value = 0 } = box`) followed: identifier
properties, optional renames and defaults, over a local record. The lowering
reads each property in order from the initializer held once, dispatches a
default on the undefined tag and joins both arms at a node typed by their
union; the producers claim only the initializer and the defaults, and the
entry after the statement states the bindings. `tests/object-patterns.mts`
and `ObjectPatternTests.lean` cover it. TypeScript types a literal destructured
directly with optional properties, so the TS column covers patterns over a
bound local only; SKJS claims both forms, which is what the census measures.
Object parameters were then admitted at their annotation. No rule was added:
`RequestJson.verify_safe` already quantifies over every environment, world and
heap meeting the input types, and a record parameter is a reference whose
fields the read and write rules use as for an allocated record. The extractor
had refused reference-typed inputs by policy; that refusal is gone, the
interpretation (a conforming JavaScript value is a plain data object, as a
conforming function respects its contract) is recorded in DESIGN.md, and
`cells.ts` gains an external cell and an aliased pair whose forged claims are
refused. Four census rows verified at once; the two others report knowledge
limitations below.

Strings are admitted on the same terms as numbers: an opaque `str` value with
`strLit` singletons, `isStr` and `strEq` tags, interned labels, heap atoms,
and both producers. That extension alone did not increase repair coverage.
`evolvedInferredSnapshotStillString` exposed a checker defect: an uncaptured
write replaced its flow type with string without checking the retained number
contract. No common number/string invariant was computed. The source adapter
uses the exported point `type` for its inferred storage candidate, not the raw
`declared` field; changing the latter would not fix this refusal.

The checker repair now rejects that string assignment. This is a newly rejected
repair regression, not a newly verified function. Concrete inferred contracts
are enforced without requiring capture, and writes through open inference
variables constrain the same variable. Do not resurrect the discarded optional
export-contract workaround or synthesize a union to certify the original
acceptance. See the [agent decision rules](../AGENTS.md#resolving-checkerverifier-disagreements).
`tests/strings.mts` and `StringEqualityTests.lean` still cover string support;
the precision witness lives in `tests/skjs-unsound/`.

Type assertions (`e as T`, `e satisfies T`, `e!`) lower to a node returning
the operand unchanged at the assertion's own claim, with `T` an obligation on
the operand; a downcast with nothing known is refused. The TS producer's entry
field observation now looks through an assertion to the read beneath it. The
census also hands the verifier only the censused function's claims: carried
class methods are claimed by SKJS but have no body in the extracted source.

The other destructuring rows stay out: `identityPatternScalar` now reports
its nested pattern, and it, `checkedNestedPattern`, `earlierPatternRead`,
`patternEarlierBinding` and `checkedDeclarationDefault` all destructure
external object parameters; `checkedDestructuredDefault` destructures an
ambient call's tuple.

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
| `obj-literal-var-field-growth.ts`: `retainedReceiver` | The exporter reports `fuel-exhausted` for `{ slot: seed }` and every type mentioning `box` or `original`: the object literal's growable field variable has a cyclic saved bound, which the bounded export refuses rather than unrolls (see `testTypeClaimSnapshotUnion`). Fixing the export is only the first gate: the function then aliases a mutable local's object, assigns inside an expression, and compares a numeric field. Only three census functions carry this reason. There is a different, SKJS-rejected function with the same name in `unsound-refinement.ts`. |
| `captured-read-stability.ts`: `checkedGenericCallResult` | The callee `makeCapturedGenericCell` at extracted span `[551,574)` is refused as `function-generic`; the call's result claim itself exports. The claim language has no generic function type, so an export would have to state the call-site instantiation, and the TS producer refuses the same signature (`generic-arrow`). Beyond that, the extractor binds identifiers only from parameters and local declarations, so an ambient function value is unbound: the same external-value boundary as the object rows above. Four census functions carry `function-generic`. |
| `binding-initialization.ts`: `conditionBeforeLocal` | Reads top-level `seed` before declaring an inner `seed`. Context extraction carries the declaration, but lowering lacks that external value. Do not diagnose this solely as local shadowing. |
| `captured-read-stability.ts`: `checkedPropertyResult`; `unsound-refinement.ts`: `identityMemberSnapshot`, `stableMemberScalar`; `assignment-receivers.ts`: `temporaryReceiver` | Nested record claims refused. The first two also have external objects; `identityMemberSnapshot` and `stableMemberScalar` additionally compare object identities (`x.child !== narrow`). Nested record support alone is insufficient. |
| `unsound-refinement.ts`: `checkedConditionalAlias` | A parameter typed as a union of two record shapes with a discriminant: the claimed parameter type differs from the source annotation, since record unions are outside the claim language the extractor accepts for parameters. |
| `unsound-refinement.ts`: `capturedReceiver` | The guard `(x = { value: null }) === x` compares two object operands: equality is lowered only against a null, undefined or singleton operand, so reference identity between records has no test in the calculus. |
| `definite-assignment-tvar-soundness.ts`: `typeofInferredFieldAfterAssignment`, `typeofUndefinedFieldAdmitsInitialValue`; `test_ternary_refinements.ts`: `bothBranchesInitialize` | Uninitialized `let`. Requires an initialization discipline; seeding every private cell with undefined must not weaken the declared write contract or allow a read before initialization. |
| `logical-compound-computed-key.ts`: `computedFallback` | `??=` currently requires a local identifier. Property/computed targets must save receiver and key before the RHS and evaluate each once. String/key restrictions may be the next gate. |

Other first gates include destructuring/defaults, spread/accessors, optional or
readonly fields, arrays/tuples, unknown/generic parameters, implicit returns,
arithmetic and classes. Audit representative full functions before choosing a
large extension. Over the whole census export, the raw exporter reasons that
appear in gated functions' claims are dominated by `void-type` (arrows returning
`void`), `unexpanded-named-type` (class instances and named types),
`unsupported-type`, `cell-callable` and `nested-object-type`. That is a count of
unavailable claims, not of next gates: a site the verifier never needs does not
obstruct, so a gated row may or may not meet one of these after its syntax gate.
Ambient values (top-level declarations and generic callees) remain unbound in
the extractor. Object parameters are assumed at their annotation as arrow
parameters already were; the rows that carried the old refusal now verify or
report their next obstruction above.

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
