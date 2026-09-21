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
   publishes acceptance. It conservatively joins branches and infers local
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

The active architectural milestone is **polymorphic call inference**: scoped
schemes, fresh inference variables, constraint proposals with retained
obligations, and validation before publication. The first executable slice
accepts a unary identity closure instantiated at Boolean. It preserves the
scheme in SourceClaims, checks the body universally, and then sends the checked
instance through the ordinary graph proof. General instantiation still needs a
compositional scheme certificate. Keep inference-variable identities and write
capabilities out of the published semantic-type API.

The inferred-copy prerequisite is now supported: an unannotated immutable local
retains its checked initializer type, and subsequent claims must follow from it.
This includes dependent bounds and sequential declarators. It adds no inference
metavariables and is not evidence that polymorphic call inference works.

### Polymorphic calls and closures: next implementation boundary

The model interprets rigid labels under an assignment in `TypeParams.lean` and
proves parameter/field substitution equations. `TypeSchemes.lean` now provides
general semantic scheme introduction/elimination, call safety, and allocation
with fixed field contracts. Its closure-body rule quantifies over assignments
while retaining the same captured environment and world; outer parameter
meanings cannot change. Scheme meanings are admissible closed-value families,
so they can themselves serve as semantic type arguments.

The exact unary identity scheme now has an executable path and a matching
universal allocation theorem. The general rules are still **not** a general
executable scheme certificate checker: arbitrary substitution evidence and body
proof reconstruction still need implementing. Recursive scheme graph nodes also
need the layer congruence/contractiveness argument; admissibility alone does not
establish recursive interpretation. Extending only the parser or specializing
each closure body at its observed calls would bypass the universal obligation.
Follow this order:

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

`generic-closure.ts` is the first end-to-end witness. Its producer proposal is
not enough: a negative closure that fabricates `T` reaches Lean and is refused
before specialization, while the accepted instance still receives the ordinary
graph certificate. A successful OCaml solver unit test or an unchecked concrete
specialization would not close that gap.

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
and diagnostic for every negative control and known gap. The suite currently
verifies **34 functions in 16 feature groups**, checks **14 negative controls**,
and keeps **5 named gaps** visible. Seven independent evidence-tampering controls
remain. These counts concern this prototype, not the SKJS repair census.

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
| Quantified closure and fresh call inference | `generic-closure.ts`                                               |
| No usable result guarantee                  | `top-void.ts` (unknown, discarded callback result)             |

Every negative control must reach validation and fail for its expected reason;
a premature gate refusal is a test failure. Controls cover bad returns,
local/aliased/array writes, readonly writes, callback arguments and variance,
mutable captures, generic fabrication, bad contextual initializers and stale
heap refinements. Contextual types cannot turn a bad initializer into a fact.

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
