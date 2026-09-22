# OCaml producer prototype

An independent OCaml producer with **verified acceptance**, using the existing
Fragment → SourceClaims → Lean evidence pipeline. It does not invoke SKJS or
TypeScript's type checker to infer claims. The shared TypeScript parser remains
the source front end. The producer uses the shared Lean model, lowering and
proof rules; it has no separate acceptance calculus.

## Try it

From the repository root, with OCaml 5 and Dune 3 installed:

```sh
npm ci --prefix verification/tools
lake -d verification/lean build verifier
dune build --root verification/ocaml-producer
node verification/ocaml-producer/check.mts verification/ocaml-producer/examples/callbacks.ts
dune runtest --root verification/ocaml-producer
node verification/ocaml-producer/test.mts
```

Set `VERIFIER` to reuse a verifier executable built from this checkout's Lean
sources. This avoids rebuilding Lean in a fresh worktree. The prototype requires
Dune for building, but no OCaml libraries beyond the standard library, and no
Skip toolchain or Docker. Install Dune with `opam install dune` if needed.
`dune runtest` runs the OCaml unit tests; `node test.mts` (from this directory)
runs the end-to-end verification tests.

The checker prints `verified`, `unverified`, `unsupported`, or `error`, with an
artifact directory containing the exact source snapshot, Fragment, claims,
evidence (if produced), and diagnostic logs. The outcome identifies the failing
phase (`source`, `proposal`, `search`, or `check`); success lists every verified
function. Only `verified` exits successfully.
Proof search has fuel 12; each child process has a 30-second timeout. An
`unverified` result is not a proof that the source is wrong. A timeout or failed
executable is an infrastructure error. Artifacts remain available for inspection.

The low-level `_build/default/producer.exe fragment.json` command **only proposes claims**.
Its successful exit is never a type-checking verdict.

## Reading its claims

`make viewer` offers this producer beside SKJS and `tsc`: select **OCaml
claims**, and the reader runs the same two steps `check.mts` runs — the shared
parser, then `producer.exe` over the Fragment — and hands what came out to the
same verifier. What it then shows is this producer's own document, claim by
claim at the spans it is about, with the verifier's verdict beside each
function; its examples above are in the picker, negative controls and named
gaps included. The reader displays outcomes and never reaches one, so an
outcome there means what it means here: `✗` is no derivation found, never a
disproof. A source this producer does not implement is refused where it is
refused — the parser's gate, or its own `unsupported:` — rather than displayed
as a report with nothing in it. The reader runs the executable `dune build`
leaves in `_build/`; it does not build it.

`node verification/ocaml-producer/test.mts` checks that correspondence: that
the claims the reader carries are the ones this producer wrote, that its
verdicts are the verifier's, and that a source outside the fragment is refused
by name.

## Architecture, including the parts not implemented yet

The scope limit is in the implemented cases, not a different account of the
language. The boundaries are:

1. `source.ml` decodes the shared Fragment into typed OCaml data. It preserves
   source positions, declared contracts, and quantified parameters with bounds.
   Alias substitution uses a fresh parameter environment, retaining the scoped
   identities of its actual arguments; recursive expansion is explicitly refused.
   Unsupported constructs fail explicitly. It does not lower JavaScript into a
   second calculus; existing Lean lowering owns that step.
2. `semantic.ml` describes immutable semantic types. Rigid binder identity
   includes scope and binder index; spelling is only for export. Object shapes
   contain both field capabilities and call signatures. Fields distinguish
   presence, reads and writes; function objects will not require a second
   type universe. Required invariant fields, readonly views and array/tuple
   contracts are implemented. Optional field presence remains separate from
   present-undefined, and is blocked by the shared source/proof interface.
3. `environment.ml` distinguishes immutable value snapshots from mutable
   storage contracts. In this implementation, mutable reads always propose
   the fixed storage type, including inside closures. No point-specific
   refinement or inference operation can replace that contract.
4. `proposal.ml` infers immutable candidate claims. It neither validates nor
   publishes acceptance. For a call to a quantified callable, `inference.ml`
   collects constraints through callable shapes — a callback's parameters from
   the scheme, its result from the argument — and the first occurrence of a
   binder proposes its type; a later disagreement is not refused, because every
   argument is validated against the substituted signature and fails there. It conservatively joins branches and infers local
   values, object shapes, callback results and calls from explicit signatures.
   Expected types guide fresh object/array construction, while the actual
   initializer claims remain separate obligations. Immutable branch refinements
   cannot refine a mutable binding's storage contract. Loops use the incoming
   fixed contracts as candidate invariants; `break` and `continue` edges are
   validated by the existing control-flow checker. Declared types are candidates to prove, not proof that their bodies satisfy
   them. There is no second, approximate subtype relation used for acceptance.
5. `claims.ml` serializes those candidates into the existing producer-neutral
   SourceClaims protocol. Graph interning is local to one document. Graph
   labels are an export detail, not type-variable identities.
6. `check.mts` freezes source bytes, runs the parser and OCaml producer, asks Lean
   to reconstruct obligations and produce evidence, then invokes the independent
   evidence consumer. Every source function must be covered. Acceptance is
   printed only after that final check succeeds.

Inference metavariables and existential witnesses are **not implemented**.
When introduced, they must have separate identities and capabilities from rigid
binders. They belong to proposal/search state; they cannot be substituted into
published semantic types without discharging retained obligations. Likewise,
delayed literals are inference work, not new semantic types.

The active architectural milestone remains **polymorphic call inference**:
scoped schemes, fresh inference variables, constraint proposals with retained
obligations, and validation before publication. The current executable breadth
path accepts
a quantified closure, bounded by earlier binders or `boolean` or not, called any
number of times at any ground types.
It preserves the scheme in SourceClaims, checks the closure body once and
universally against its declared signature, validates each call's own explicit
substitution, and only then compiles the checked eliminations to ordinary graph
arrows. The universal gate reads the body from the source rather than from its
claim, so it does not depend on which calls the program makes. Nested
quantified schemes throughout the direct checker, fresh inference variables,
and a compositional scheme certificate are still missing.
An unquantified returned closure may retain an outer binder in the implemented
slice; that is not a nested quantified scheme.
Keep inference-variable identities and write capabilities out of the published
semantic-type API.

The inferred-copy prerequisite is now supported: an unannotated immutable local
retains its checked initializer type, and subsequent claims must follow from it.
This includes dependent bounds and sequential declarators. It adds no inference
metavariables and is not evidence that polymorphic call inference works.

## Extending the producer

Every row runs these steps. Each names the document that owns the rule it
applies; this file records only what is specific to this producer.

1. Add the motivating positive and negative sources without simplifying away
   the feature. Add them to [`cases.mts`](cases.mts) with their expected phase
   and diagnostic; that file is the executable source of truth, and the reader
   lists its cases without further registration.
2. Run the case once and identify the first honest boundary: shared parsing,
   OCaml proposal, Lean obligation reconstruction, evidence production, or
   evidence checking.
3. Extend an existing shared representation in place; the
   [languages index](../LANGUAGES.md) says which file owns each. If Fragment
   or SourceClaims changes, update every producer, decoder, printer and
   consumer; never add an OCaml-only format or a second accepted wire shape.
   What the change must carry — soundness lemma, located obligations, or a
   tampering test — is set by
   [documentation ownership](../README.md#documentation-ownership).
4. Keep inference candidates in `inference.ml`. Published `Semantic.ty` values
   may contain rigid binders and schemes, never solver metavariables or an
   unresolved substitution. A proposal is not an acceptance fact.
5. Make Lean reconstruct every obligation from source and claims. A check that
   can fail is an obligation with a source span, reported through the
   [located diagnostic channel](../OBLIGATION-DIAGNOSTICS.md#direct-obligations);
   a bare error string is a defect. Add a negative control that is
   [independent](../tests/README.md) — it reaches that obligation and fails
   there, and no shortcut that accepts the positives also rejects it — plus a
   mutation showing that valid evidence cannot certify a forged claim or
   substitution.
6. Run `dune build --root verification/ocaml-producer`,
   `dune runtest --root verification/ocaml-producer`,
   `lake -d verification/lean build` (all of it: fixtures construct shared
   structures), and `node verification/ocaml-producer/test.mts`. Run the shared
   TypeScript check and the viewer tests when their files change. SKJS suites
   are unnecessary unless a `.sk` file changes.
7. Update the documents that own what changed, per
   [documentation ownership](../README.md#documentation-ownership) — wire
   fields in the protocol documents, the notation in the viewer language, the
   decision in DESIGN — then the table below from the
   final test output. Name any remaining blocked witness; passing adjacent
   examples does not complete its row. Do not create a handoff or checkpoint
   file.

## Breadth progress and work queue

The current goal is breadth: exercise each major language mechanism with the
smallest source that forces the final architecture to represent it honestly.
Small examples are intentional; subset-specific representations are not. A row
is complete only when its positive witness reaches `verified`, its relevant bad
program reaches validation and is rejected there, and any new evidence field is
covered by a tampering test. [`cases.mts`](cases.mts) is the executable source of
truth for outcomes; this table records why the next rows matter.

| Slice | State | Existing witness or next acceptance test | Architectural pressure |
| --- | --- | --- | --- |
| Primitive values and fixed local storage | complete | `values.ts` | Separate value snapshots from location contracts |
| Branches, nullish flow and loops | complete | `branches.ts`, `flow.ts`, `loops.ts` | Join path knowledge without changing storage types |
| Multi-field objects and aliases | complete | `objects.ts`, `aliases.ts` | Preserve field identity and capture-avoiding substitution |
| Arrays, tuples and readonly views | complete | `arrays.ts`, `readonly.ts` | Separate sequence presence, reads and writes |
| Higher-order callbacks and variance | complete | `callbacks.ts` | Check parameters contravariantly through ordinary evidence |
| Closure scope and partial application | complete | `blocks-bind.ts` | Retain captures and residual signatures |
| Callable objects with fields | complete | `function-fields.ts` | Give one value call and field capabilities |
| Generic declarations and rigid bounds | complete | `generics.ts`, `generic-inferred.ts` | Keep rigid identities distinct through copies and dependent bounds |
| Quantified closure, one inferred call | complete | `generic-closure.ts` | Keep a scheme in SourceClaims and validate its body universally |
| One closure called at two types | complete | `generic-two-calls.ts`, `invalid-scheme-capture.ts` | Give each call fresh proposal state; do not specialize the stored scheme |
| Bounded quantified closure | complete | `generic-bounded.ts`, `invalid-bound-reversed.ts`, `invalid-bound-body.ts` | Export and validate the concrete substitution and every bound obligation |
| Returned quantified/outer-dependent closure | complete | `generic-returned.ts`, `invalid-returned-capture.ts` | Preserve nested scope and avoid capture during substitution |
| Quantified closure with captured storage | complete | `generic-captured-store.ts`, `invalid-captured-write.ts` | Keep one fixed world contract across every instantiation |
| Generic callback argument | complete | `generic-callback.ts`, `invalid-callback-variance.ts`, `invalid-callback-result.ts` | Collect directional constraints without placing solver state in semantic types |
| Optional object-field presence | blocked at shared source/proof boundary | `optional-field.ts` | Model absence separately from a present `undefined` value |
| Bare return and implicit completion | blocked at shared parser | `bare-return.ts`, `empty-closure.ts` | Represent completion and discarded results explicitly |
| Arbitrary numeric array indexing | blocked in lowering | `dynamic-index.ts` | Prove a general index obligation rather than inventing a singleton key |
| Inferred mutable lifetime contract | deferred flow milestone | `unsupported.ts` | Solve one invariant against initialization and every write before publication |

Agents should take the first incomplete row whose prerequisite representation
already exists. The quantified rows are complete for this slice; what remains
is blocked at the shared boundaries the table names, so take the first row
whose boundary has moved. This slice admits one quantified closure per
containing function and refuses a second by name. For every quantified row, rewriting a closure to the finite overloads observed in that
program, checking its body once per observed call, or replacing its scheme claim
with a monomorphic arrow does not satisfy the row.

For this breadth row, a universal Lean source checker may establish scheme
introduction first and then compile each validated elimination to the ordinary
graph arrows that the existing evidence engine understands. The graph may
therefore contain redundant per-arrow body derivations. They are consequences
of the universal result, not its justification: acceptance must always require
the universal check independently of the number and types of observed calls,
and each call must validate its fresh substitution and bounds before lowering.
Keep this compilation behind one interface so a later first-class scheme
certificate can replace it without changing Fragment, SourceClaims, OCaml
semantic types or inference. A negative closure that happens to work at every
observed call type but cannot produce an arbitrary rigid result must reach Lean
and fail the universal gate. First-class scheme hypotheses in the request
protocol remain a later certificate-depth milestone; they do not block this
breadth row.

The procedure for a row is [Extending the producer](#extending-the-producer)
above.

### Polymorphic calls and closures: next implementation boundary

The model interprets rigid labels under an assignment in `TypeParams.lean` and
proves parameter/field substitution equations. `TypeSchemes.lean` now provides
general semantic scheme introduction/elimination, call safety, and allocation
with fixed field contracts. Its closure-body rule quantifies over assignments
while retaining the same captured environment and world; outer parameter
meanings cannot change. Scheme meanings are admissible closed-value families,
so they can themselves serve as semantic type arguments.

A scheme, bounded or not, now has an executable path: `SourceClaimJson`'s scheme
section checks introduction universally from the source, validates each call's
explicit substitution, and compiles the checked eliminations to ordinary arrows.
The executable subtype gate is connected to ordinary semantic families:
`DirectObligation.Ty.leUnder_sound` proves its rigid-bound, ground-union and
contravariant/covariant arrow cases denote inclusion. What is not yet connected
is the source checker: no theorem states that `GenericSource.closureTy`
establishes the premises of `TypeSchemes.scheme_intro`. Consequently the graph
certificates prove the compiled ground instances used by the current program;
they do not certify the universal scheme claim itself.
The general rules are still **not** a general executable scheme certificate
checker: nested quantified schemes, arbitrary substitution evidence
and body proof reconstruction still need implementing, and the compiled arrows
are consequences carried by the graph rather than a certificate of the scheme
itself. `identity_scheme_safe` remains a closed theorem about one term, tied to
the executable path by wire-shape guards, not by a proof. Recursive scheme graph
nodes also need the layer congruence/contractiveness argument; admissibility
alone does not establish recursive interpretation. Extending only the parser or
specializing each closure body at its observed calls would bypass the universal
obligation. Follow this order:

1. Represent scoped quantifiers at callable signatures, including bounds and
   occurrences inside fields, callbacks and results. Preserve the same structure
   in Fragment, semantic types and the single SourceClaims representation. A
   spelling-only top-level `{param: "T"}` cannot identify nested, shadowing
   binders. Update all producers and consumers together; do not add an OCaml-only
   encoding or flatten quantifiers into monomorphic arrows.
2. Connect the established semantic introduction/elimination rules to an
   executable evidence consumer. Introduction checks the body under fresh rigid
   parameters for every admissible assignment satisfying its bounds. Captures retain their existing
   types and location contracts; an already allocated location must not acquire
   a different contract at each instantiation. Elimination supplies an explicit
   substitution and proves substituted bounds and argument obligations. Its
   result follows by capture-avoiding substitution. General syntactic substitution
   still needs proof. `make_scheme_fields` already proves allocation with field
   contracts independent of the call instantiation, and
   `invocation_of_scheme_body` retains the same capture environment. The source
   checker must establish these premises, not simply trust an inferred scheme.
3. Give each call fresh proposal-only inference candidates in a separate solver
   module. Collect directional constraints, including reversed callback inputs
   and both read/write obligations for writable fields. Retain the original
   operands and bounds. A candidate solution produces a concrete substitution
   to check, never an acceptance fact. No unresolved candidate ID appears in
   published semantic types or evidence. Hidden existential witnesses remain
   rigid and cannot be solved as inference candidates.
4. Implement simple explicit and inferred calls through that interface first.
   Test one closure at two distinct argument types, a returned closure retaining
   its outer parameter, a dependent bound, and a captured fixed-contract object.
   Negative controls must reach validation: fabricated generic results, reversed
   bounds, callback variance and a capture used as incompatible storage. Tamper
   with instantiation evidence and check rejection by the independent consumer.

`generic-closure.ts` is the first end-to-end witness and `generic-two-calls.ts`
the first with two independently substituted eliminations of one retained
scheme. Their producer proposals are not enough: a negative closure that
fabricates `T` reaches Lean and is refused at the universal gate, while the
accepted instances still receive the ordinary graph certificate.
`invalid-scheme-capture.ts` is what separates this from specialization — every
one of its calls instantiates `T` at Boolean, so the compiled arrow is
satisfied, and only the universal check refuses it. A successful OCaml solver
unit test or an unchecked concrete specialization would not close that gap.

### Subsequent flow work

Then extend flow analysis with location identity, alias/effect tracking and
invariant proposals. For inferred storage, solve one lifetime contract against
initialization and **all** writes before publication. For heap flow facts, keep
refinements separate from persistent field capabilities, invalidate them across
unknown calls/writes, and preserve immutable snapshots. Cache validated decisions
only with their complete assumptions/dependencies, separately from inference
caches. None of that machinery is needed or claimed by the current conservative
fixed-contract loop analysis.

This is not a promise that full-language support needs no new representations.
For example, recursive types, effect summaries and general quantifier proofs
still need implementation and mathematical work. The invariants above must
survive those extensions rather than being replaced by subset shortcuts.

## What works and what the tests establish

[cases.mts](cases.mts) is the executable inventory, including expected phase
and diagnostic for every negative control and known gap. `node test.mts` prints
what the suite verifies, refuses and keeps visible, and how many tampering
controls hold; the numbers live in its output, not here.

| Architectural pressure                      | Small examples that verify                                     |
| ------------------------------------------- | -------------------------------------------------------------- |
| Stable storage vs value snapshots           | `values.ts`, captured storage in `callbacks.ts`                |
| Field identity and aliasing                 | `objects.ts`                                                   |
| Bidirectional construction hints            | `contextual.ts` (fresh object and tuple)                       |
| Read permission vs write permission         | `readonly.ts` (alias view, array covariance)                   |
| Sequence shape and presence                 | `arrays.ts` (write, inferred literal, optional tuple position) |
| Path-local knowledge                        | `flow.ts` (null test, conditional, nullish expression)         |
| Cyclic control flow                         | `loops.ts` (invariant, break, continue)                        |
| Higher-order values and variance            | `callbacks.ts`                                                 |
| Closure-local scope and partial application | `blocks-bind.ts`                                               |
| One value with both fields and calls        | `function-fields.ts`                                           |
| Scoped parameters and substitution          | `generics.ts`, `generic-inferred.ts`, `aliases.ts`                  |
| Quantified closure and fresh call inference | `generic-closure.ts`, `generic-two-calls.ts`                   |
| Bounded scheme and substituted bound obligations | `generic-bounded.ts` |
| Returned closure retaining an outer binder | `generic-returned.ts` |
| Captured cell at one fixed contract under a scheme | `generic-captured-store.ts` |
| Binder inferred through a callback, checked contravariantly | `generic-callback.ts` |
| No usable result guarantee                  | `top-void.ts` (unknown, discarded callback result)             |

Every negative control must reach validation and fail for its expected reason;
a premature gate refusal is a test failure. Controls cover bad returns,
local/aliased/array writes, readonly writes, callback arguments and variance,
mutable captures, generic fabrication, a closure valid at every observed call
but not universally, a reversed substituted bound at a call, a body that
reverses its binder's bound, bad contextual initializers and stale heap refinements. Contextual types cannot turn a bad initializer into a fact.

The five named gaps are:

- `unsupported.ts`: OCaml refuses an unannotated mutable binding rather than
  guessing a lifetime contract. Constraint-based contract inference is pending.
- `dynamic-index.ts`: the existing lowering needs a proved array-index singleton;
  it does not model arbitrary numeric properties.
- `optional-field.ts`: the shared parser cannot yet represent optional presence.
- `bare-return.ts` and `empty-closure.ts`: the shared parser refuses these forms
  of completion, although the explicit discarded-result callback verifies.

The motivating sources are preserved. No gap is counted as a verification,
rewritten into an easier witness, or allowed to disappear behind another error.
Overloads/intersections, recursive types, modules, classes/prototypes, exceptions,
async behavior and general effects still need separate work; this is breadth
across the current calculus's major mechanisms, not the full language.

## What is proved, and what is trusted

Successful checking uses the existing Lean certificate consumer and its
soundness theorems for the modeled fragment. The OCaml inference algorithm is
not itself proved correct; a bad proposal must fail validation. Generic
variable-copy checking uses the existing direct generic checker in both Lean
phases rather than ordinary graph evidence.

The shared parser, source-to-calculus correspondence, executable toolchain and
runner remain part of the trust boundary. Source lowering being written in Lean
is not a proof of preservation of full JavaScript semantics. Existing model
assumptions and restrictions in [DESIGN.md](../DESIGN.md) still apply. This is a
first producer against that boundary, not a verified implementation of the full
TypeScript language.
