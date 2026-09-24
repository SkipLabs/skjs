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
node verification/ocaml-producer/check.mts verification/ocaml-producer/examples/recursive-json.ts \
  --project verification/ocaml-producer/upstream
node verification/ocaml-producer/check.mts verification/ocaml-producer/examples/recursive-json-variants.ts \
  --project verification/ocaml-producer/upstream
dune runtest --root verification/ocaml-producer
node verification/ocaml-producer/test.mts
```

The `--project` argument reads TypeScript files, package exports, workspace
symlinks, and a `tsconfig.json` that includes the client. The checked-in
`upstream` directory is a small source-tree snapshot with that project setup.
A full Skip checkout needs an equivalent client project before its imports can
pass the new TypeScript resolution check.

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
   Local alias substitution uses a fresh parameter environment, retaining the scoped
   identities of its actual arguments. Imported recursive aliases retain named
   declaration identities; the producer never expands their equations.
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
   accumulates directional lower/upper constraints through callable shapes,
   reversing direction at each callback parameter and preserving it at results.
   Declared dependent bounds propagate lower constraints forward and upper
   constraints backward to a fixed point. Candidate types join lower bounds;
   upper-only candidates intersect primitive bounds when representable. Every
   argument and substituted bound is still validated by Lean. It conservatively joins branches and infers local
   values, object shapes, callback results and calls from explicit signatures.
   Expected types guide fresh object/array construction, while the actual
   initializer claims remain separate obligations. Immutable branch refinements
   cannot refine a mutable binding's storage contract. Loops use the incoming
   fixed contracts as candidate invariants; `break` and `continue` edges are
   validated by the existing control-flow checker. Declared types are candidates to prove, not proof that their bodies satisfy
   them. There is no second, approximate subtype relation used for acceptance.
5. `claims.ml` serializes those candidates into the existing producer-neutral
   SourceClaims protocol. It reserves empty rows for imported declarations
   without parameters and for generic applications, listing the applications
   with their declaration and argument rows (`"applications"`). Lean fills the
   reserved rows from the source equations: every declaration has one lowering,
   and OCaml cannot supply a competing interpretation. Graph interning is local to one
   document. Graph labels are an export detail, not type-variable identities.
6. `check.mts` freezes source bytes, runs the parser and OCaml producer, asks Lean
   to reconstruct obligations and produce evidence, then invokes the independent
   evidence consumer. Every source function must be covered. Acceptance is
   printed only after that final check succeeds.

Inference metavariables and existential witnesses are **not implemented**.
When introduced, they must have separate identities and capabilities from rigid
binders. They belong to proposal/search state; they cannot be substituted into
published semantic types without discharging retained obligations. Likewise,
delayed literals are inference work, not new semantic types. Keep
inference-variable identities and write capabilities out of the published
semantic-type API.

The implemented slice accepts a quantified closure — unbounded, or bounded by
`boolean` or by an earlier binder — called any number of times at any ground
types. It preserves the scheme in SourceClaims, checks the closure body once and
universally against its declared signature, validates each call's own explicit
substitution, and only then compiles the checked eliminations to ordinary graph
arrows. The universal gate reads the body from the source rather than from its
claim, so acceptance does not depend on which calls the program makes. One
quantified closure per containing function is admitted; a second is refused by
name. An unannotated immutable local retains its checked initializer type,
through dependent bounds and sequential declarators alike.

Missing: nested quantified schemes throughout the direct checker, fresh
inference variables, and a compositional scheme certificate. An unquantified
returned closure may retain an outer binder in the implemented slice; that is
not a nested quantified scheme.

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
6. While iterating, run only the cases the change touches:
   `node verification/ocaml-producer/run-cases.mts <pattern>` after
   `dune build --root verification/ocaml-producer` (and
   `lake -d verification/lean build` when Lean changed). Before committing,
   run `node verification/ocaml-producer/test.mts`, plus
   `dune runtest --root verification/ocaml-producer` for unit tests, and the
   wider tiers in [AGENTS.md](../AGENTS.md#iterating-run-what-the-change-touches)
   when Lean, the parser or a wire format changed. SKJS suites are
   unnecessary unless a `.sk` file changes.
7. Update the documents that own what changed, per
   [documentation ownership](../README.md#documentation-ownership) — wire
   fields in the protocol documents, the notation in the viewer language, the
   decision in DESIGN — then the queue below from the final test output. Name any remaining blocked witness; passing adjacent
   examples does not complete its row. Do not create a handoff or checkpoint
   file.

## Breadth progress and work queue

The current goal is breadth: exercise each major language mechanism with the
smallest source that forces the final architecture to represent it honestly.
Small examples are intentional; subset-specific representations are not. A row
is complete only when its positive witness reaches `verified`, its relevant bad
program reaches validation and is rejected there, and any new evidence field is
covered by a tampering test. [`cases.mts`](cases.mts) is the executable source of
truth for outcomes; the queue below records why the open rows matter.

Complete, with their witnesses in [`cases.mts`](cases.mts): primitive values and
fixed local storage; branches, nullish flow and loops; multi-field objects and
aliases; arrays, tuples and readonly views; higher-order callbacks and variance;
closure scope and partial application; callable objects with fields; omitted
trailing arguments, for optional and for defaulted parameters; closures
advertising several signatures, checked once per signature; rest parameters,
tuple or mutable array, and spreads among the actuals; universally certified
quantified array rests and calls through variadic callbacks; universally checked
rigid defaults and acyclic forward captures with preserved effect order; generic
declarations and rigid bounds; quantified closures — one inferred call, one
closure called at two types, bounded, returned or outer-dependent, reading
captured storage, and as a callback argument; and generic inference constraints,
for the maintained witnesses.

| Open row                            | State                                   | Witness                              | Architectural pressure                                                        |
| ----------------------------------- | --------------------------------------- | ------------------------------------ | ----------------------------------------------------------------------------- |
| Optional object-field presence      | blocked at shared source/proof boundary | `optional-field.ts`                  | Model absence separately from a present `undefined` value                     |
| Bare return and implicit completion | blocked at shared parser                | `bare-return.ts`, `empty-closure.ts` | Represent completion and discarded results explicitly                         |
| Arbitrary numeric array indexing    | blocked in lowering                     | `dynamic-index.ts`                   | Prove a general index obligation rather than inventing a singleton key        |
| Inferred mutable lifetime contract  | deferred flow milestone                 | `unsupported.ts`                     | Solve one invariant against initialization and every write before publication |

Take the first open row whose prerequisite representation already exists. For
every quantified row, rewriting a closure to the finite overloads observed in
that program, checking its body once per observed call, or replacing its scheme
claim with a monomorphic arrow does not satisfy the row: acceptance must require
the universal check independently of the number and types of observed calls, and
each call must validate its fresh substitution and bounds before lowering. The
compiled arrows stay behind one interface, so a later first-class scheme
certificate can replace them without changing Fragment, SourceClaims, OCaml
semantic types or inference.

The procedure for a row is [Extending the producer](#extending-the-producer)
above.

### Schemes: what exists, what is missing

The model interprets rigid labels under an assignment in `TypeParams.lean` and
proves parameter/field substitution equations. `TypeSchemes.lean` provides
semantic scheme introduction/elimination, call safety, and allocation with fixed
field contracts (`make_scheme_fields` allocates independently of the call
instantiation, and `invocation_of_scheme_body` retains the same capture
environment). Its closure-body rule quantifies over assignments while retaining
the same captured environment and world, so outer parameter meanings cannot
change, and scheme meanings are admissible closed-value families that can
themselves serve as semantic type arguments.

The executable path runs from `SourceClaimJson`'s scheme section, which checks
introduction universally from the source, validates each call's explicit
substitution and compiles the checked eliminations to ordinary arrows.
`DirectObligation.Ty.leUnder_sound` proves the executable subtype gate's
rigid-bound, ground-union and contravariant/covariant arrow cases denote
inclusion. `GenericSource.closureCertificate` reconstructs a proof for immutable
reads, captured-cell reads, nested closures and callback calls independently of
the observed calls — nested closure proofs use safe allocation and the same
invocation lemma as universal introduction, and callback proofs use the existing
effectful call rule for the callee and every argument, with subtyping at the call
boundary. `GenericCertificate.ClosureCertificate.check_safe` then establishes
`InvocationSpec` for every admissible assignment satisfying the bounds, with one
unchanged capture environment and world: the universal code premise of scheme
introduction. Final acceptance requires that certificate as well as the enclosing
function's graph evidence. Cell slots carry their declaration's fixed contract,
and `bag_read` proves reads through the captured identity.

Missing: nested quantified schemes, arbitrary substitution evidence, a proof of
general syntactic substitution, further body proof constructors, and recursive
scheme graph nodes, which need the layer congruence/contractiveness argument —
admissibility alone does not establish recursive interpretation. There is no
general executable scheme certificate checker; the compiled arrows are
consequences carried by the graph rather than a certificate of the scheme itself.
First-class scheme hypotheses in the request protocol are a later
certificate-depth milestone. `identity_scheme_safe` is a closed model example;
executable acceptance uses the general `ClosureCertificate.check_safe` theorem
instead.

Invariants any extension must keep. Scoped quantifiers have one shared
representation across Fragment, semantic types and SourceClaims, including bounds
and occurrences inside fields, callbacks and results; a spelling-only top-level
`{param: "T"}` cannot identify nested, shadowing binders, and no producer may add
its own encoding or flatten quantifiers into monomorphic arrows. Introduction
checks the body under fresh rigid parameters for every admissible assignment
satisfying its bounds, captures keep their types and location contracts, and an
already allocated location must not acquire a different contract at each
instantiation. Elimination supplies an explicit substitution and proves the
substituted bounds and argument obligations. Each call gets fresh proposal-only
candidates in the solver module, including reversed callback inputs and both
read/write obligations for writable fields; no unresolved candidate ID appears in
published semantic types or evidence, and hidden existential witnesses remain
rigid rather than being solved as candidates. Extending only the parser, or
specializing each closure body at its observed calls, would bypass the universal
obligation.

`generic-closure.ts` is the first end-to-end witness and `generic-two-calls.ts`
the first with two independently substituted eliminations of one retained scheme.
`invalid-scheme-capture.ts` is what separates this from specialization: every one
of its calls instantiates `T` at Boolean, so the compiled arrow is satisfied, and
only the universal check refuses it. A successful OCaml solver unit test or an
unchecked concrete specialization would not close that gap.

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

| Architectural pressure                      | Small examples with full certificates                                                                                                         |
| ------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- |
| Stable storage vs value snapshots           | `values.ts`, captured storage in `callbacks.ts`                                                                                               |
| Field identity and aliasing                 | `objects.ts`                                                                                                                                  |
| Bidirectional construction hints            | `contextual.ts` (fresh object and tuple)                                                                                                      |
| Read permission vs write permission         | `readonly.ts` (alias view, array covariance)                                                                                                  |
| Indexed reads and absent keys                | `index-signature.ts` (readonly dictionary identity, mixed named views, fresh construction, and results including `undefined`)                |
| Sequence shape and presence                 | `arrays.ts` (write, inferred literal, optional tuple position)                                                                                |
| Path-local knowledge                        | `flow.ts` (null test, conditional, nullish expression)                                                                                        |
| Cyclic control flow                         | `loops.ts` (invariant, break, continue)                                                                                                       |
| Higher-order values and variance            | `callbacks.ts`                                                                                                                                |
| Closure-local scope and partial application | `blocks-bind.ts`                                                                                                                              |
| One value with both fields and calls        | `function-fields.ts`                                                                                                                          |
| No usable result guarantee                  | `top-void.ts` (unknown, discarded callback result)                                                                                            |
| Rigid parameters and dependent bounds       | `generics.ts`, `aliases.ts`, `generic-inferred.ts`                                                                                            |
| Quantified rest collection and callbacks | `generic-rest.ts` (declaration, fresh arrays, independent instances, prefixes, spreads, defaults, callback invocation) |
| Quantified closures and their calls         | `generic-closure.ts`, `generic-two-calls.ts`, `generic-bounded.ts`, `generic-returned.ts`, `generic-captured-store.ts`, `generic-callback.ts` |

Every negative control must reach validation and fail for its expected reason;
a premature gate refusal is a test failure. Controls cover bad returns,
local/aliased/array writes, readonly writes, callback arguments and variance,
mutable captures, generic fabrication, a closure valid at every observed call
but not universally, a type argument violating its bound, a body that
reverses its binder's bound, bad contextual initializers and stale heap refinements. Contextual types cannot turn a bad initializer into a fact.

The named gaps are:

- `unsupported.ts`: OCaml refuses an unannotated mutable binding rather than
  guessing a lifetime contract. Constraint-based contract inference is pending.
- `dynamic-index.ts`: the existing lowering needs a proved array-index singleton;
  it does not model arbitrary numeric properties.
- `optional-field.ts`: the shared parser cannot yet represent optional presence.
- `bare-return.ts` and `empty-closure.ts`: the shared parser refuses these forms
  of completion, although the explicit discarded-result callback verifies.

The motivating sources are preserved. No gap is counted as a verification,
rewritten into an easier witness, or allowed to disappear behind another error.
General recursive and interface types, value imports, classes/prototypes,
exceptions, async behavior and general effects still need separate work.
Callable overloads, imported recursive aliases and named type-only imports
have narrower implemented slices; this is breadth across the current
calculus's major mechanisms, not the full language.

Decision completeness is stated and proved for the rigid fragment:
`RigidJudgments.Sub` is inclusion under declared bounds, decided by
`Ty.leUnder` on the well-formed parameter lists `parametersOf` builds;
`SourceJudgments.HasTy` and `Checked` are typing of lowered closure and
declaration bodies, decided by the pure checker `GenericSource` runs after
lowering; `CertificateJudgments.Typed` types calculus terms, and every
derivation has a certificate accepted by `Proof.check`. Each is stated by
rules, without proof terms or fuel, and each
theorem gives both directions. This is completeness for the declared rules,
not for every inclusion that happens to hold in the semantic model, and it is
separate from completeness of graph proof search. The operational target
stands beside it: every positive row reaches final semantic certification and
every negative control fails its intended obligation. [DESIGN.md](../DESIGN.md) records the
counterexamples repaired to get here. These are component results, not a
completeness theorem for the complete source-to-certificate pipeline or for
OCaml inference. Captured-cell writes still have a source typing rule but no
direct certificate constructor.

Callable upper bounds are outside the current completeness theorem, not the
semantic soundness result. The [planned extension](../POSITIVE-TYPES.md#planned-completeness-extension-callable-upper-bounds)
starts with acyclic bounds referring to earlier binders; recursive bounds
require separate work. The repaired fuel regression is not a general
completeness proof for those bounds.

### OCaml inference completeness

`inference.ml` proposes one substitution per call. It now accumulates constraints
instead of committing to the first occurrence. The original witness
`second(true, flag)` in `generic-inference.ts` infers `boolean`; callback-only
constraints can infer the intersection `true` of upper bounds `boolean` and
`true`. A dependent constraint `T ≤ U` propagates every lower bound of `T` to
`U`, and every upper bound of `U` to `T`. If `U` has a chosen lower-bound join,
that choice also constrains an upper-only `T`; otherwise `U = true` could still
leave `T = boolean`. Each saturation copies finite seed sets (including these
chosen joins), so cycles terminate without a heuristic fuel limit.
Solver variables are local records keyed by scoped binder identities, never
semantic types or exported inference state.

The former `invalid-bound-reversed.ts` is preserved as the positive
`generic-dependent-inference.ts`: `pick(true, flag)` has the valid substitution
`U = T = boolean`. TypeScript 7.0.2's implicit inference rejects this call;
the verifier accepts the OCaml producer's explicit substitution. The genuine
negative `invalid-bound-argument.ts` supplies `number` for `T extends boolean`.
Existing forged-substitution and callback-variance controls still fail Lean
obligations; inference does not publish acceptance or hide contradictions.

This is still not a complete solver. Constraint decomposition covers bare
binders and simple monomorphic callable shapes, not generic record/array
positions, overload alternatives or higher-rank schemes. Upper-only primitive
intersections are computed; unrepresentable structural/rigid intersections
fall back to a deterministic existing upper candidate that Lean must validate.
There is no search over alternative substitutions or result-context inference.
A binder with neither argument constraints nor a usable declared bound is
explicitly unsupported. Further work must retain these constraints and the
independent acceptance boundary, not add a permissive subtype checker here.

## After callable part 5: reactive-runtime integration

Status: **the recursive `Json` prerequisite has verified clients; all three
framework milestones remain open**. The receiver work in the
[callable roadmap](../tests/callables/README.md) is certified. Classes,
construction and the runtime's generic API are not yet certified.
The target is Skip's `skipruntime-ts` TypeScript API and implementation, not
the native runtime written in Skip. The initial assessment inspected
`skipruntime-ts/core/src/api.ts` and `skipruntime-ts/examples/sum.ts` in the
sibling `skip` checkout; it is not a coverage census.

The integration target is `sum.ts` as a sound client of the runtime's
type-safe API. Preserve its classes, signatures and library interactions: do
not rewrite it into today's fragment and call that runtime coverage. Retain
the selected sources as fixtures, with provenance and expected outcomes in
`cases.mts`. Measure each function's first blocker through parsing, proposal,
lowering, evidence production and independent checking. Report verified,
rejected and unsupported separately.

The baseline is pinned to upstream `skip` commit
`5c902f17431d963c1b6e07fc1d15da054ba30e70`, whose `api.ts` is the type-safe
collection API: `EagerCollection<K, V>` extends the type-erased, branded
`AbstractEagerCollection`, and `Resource<Collections extends
SharedCollections>` bounds collection records by that base. That is how the
API avoids the variance problem: `EagerCollection<K, V>` uses `K` and `V` in
parameter positions, so it is not a subtype of `EagerCollection<Json, Json>`
under sound subtyping, and nothing requires it to be. SKJS's
[`@skipruntime/core` stubs](../../import-stubs/@skipruntime/core/index.d.ts)
describe the same API. The byte-for-byte upstream
[`sum.ts`](examples/reactive-sum-prettier-ignore.ts) and
[`api.ts`](upstream/skipruntime-ts/core/src/api.ts) snapshots are checked by
SHA-256 in `test.mts`.

The upstream `sum.ts` is not a sound client of that API, and SKJS rejects it:
loose `==`, a statement starting with `[`, and a plain object type
`Collections` passed as `Resource<Collections>` — a named-field type is not an
index-signature type, so it does not meet `SharedCollections` (TypeScript
accepts it only by its unsound implicit index rule). It stays as provenance,
with its first parser refusal recorded. The target is
[`reactive-sum-sound.ts`](examples/reactive-sum-sound.ts), the same program
corrected as a client, which SKJS accepts with no errors and TypeScript accepts
against the pinned API (the fixture project has no Node types for `process`).
It changes only what soundness or SKJS requires: `===`; `interface Collections
extends NamedEagerCollections`; parameter annotations in `Plus` and an
explicit `reduce<number | null>` in `Minus`; the service as a `Service` class
with `inputs`, `resources`, `externalServices` and `createGraph`, the form
Skipper generates, since SKJS refuses object-typed top-level constants; and
startup, shutdown and signal registration inside `async function main()`. The
mapper and resource bodies are upstream's. SKJS's stubs gained the two real
APIs it uses, `Values.getUnique` and `process.on`
([`runtime-client-apis.ts`](../../tests/expect-error/runtime-client-apis.ts)).

Its whole declaration graph is read: the runtime API, the standard
library's `Promise`, `Iterable` and `Iterator`, and `ResourceClass` as a
construct signature. Its first refusal is `async function main`. So **zero of
its callables are checked** yet; no producer proposal, Lean lowering or certificate is
reached. Module constants and top-level statements are in the fragment (see
[Modules and code units](../DESIGN.md#modules-and-code-units)); the
`platform` initializer before that class is admitted syntax, though its
`process.env` read still needs the `process` contract. Measured one construct
at a time, the blockers behind it are:

| Client part | First refusal when isolated | Later requirement |
| --- | --- | --- |
| whole file | `async function main` | `async`/`await`; then the `process` global |
| import graph | `InputDefinition` is a value import (a class) | classes as declarations and values |
| `Plus`, `Minus`, `AddIndex`, `Add`, `Sub`, `Service` | class declaration | classes, `this`, parameter properties, field initializers, `new` |
| `AddIndex.mapEntry` reading `Values` | `bigint` in `DepSafe` | `Values` contract, `getUnique` and its exception |
| `Plus`/`Minus` bodies | library array methods | `reduce`, `sort` and `Iterable` contracts |
| `main` | value imports | `async`/`await`, `Promise`, `runService` contract |
| signal registration | `process` global | `process` global contract (`Promise` is read from the standard library) |

The configured TypeScript project includes both files. TypeScript resolves
upstream `sum.ts`'s type imports from `@skipruntime/core` (`EagerCollection`,
`Mapper`, `Resource`, `Values`) to interfaces in `core/src/api.ts`, its value
import `InputDefinition` to a class there, and `runService` from
`@skipruntime/server` to a function in `server/src/server.ts` (`importTargets`
in [`declaration-graph.mts`](../tools/declaration-graph.mts)); the test pins
those targets and all six class callables. The first value import makes the
whole declaration graph refuse. This is resolution inventory, not acceptance of
those contracts. The source gate
currently admits named type-only imports of aliases and single interfaces
whose fields, string indexes, function-valued properties or method signatures
fit the imported graph. An optional parameter contributes `T | undefined` at
its position; an array rest parameter contributes its element contract to the
existing variadic call clause, and a tuple rest its positions. These are the same call clauses as local
functions, with no new callable semantics or proof rule. Imported call
signatures become the existing conjunction of fixed and variadic
arrows. A callable interface may also have invariant writable fields, using
the existing callable-object clause. Readonly fields or string indexes mixed
with calls still refuse because that combined clause is not represented.
Synthetic `Box`, recursive `Node`, callable-property `CallableBox`,
method-bearing `WithMethod`, overloaded callable interfaces and callable
objects with a field, plus required, optional and rest tuple aliases (mutable
or readonly), verify through the same Lean path. A detached method call fails
its receiver obligation, while an incorrect callable result fails its return
obligation.
The method graph promises safe invocation for every receiver satisfying the
interface, which is stronger than TypeScript's structural method declaration.
This is a relative client contract; imported runtime values cannot be granted
it without an explicit assumption or a checked implementation.
Interface inheritance is interpreted (see below); nested methods, optional
method *presence*, generic methods and declaration merging refuse. All four
runtime API interfaces reach a refused declaration, and `InputDefinition` and
`runService` are value imports, so the interface slice does not yet admit
`sum.ts`. Applied in a
client of the same project, each stops at its first refused declaration
(pinned in `test.mts`):

| Interface | First refusal | Why |
| --- | --- | --- |
| `Mapper<K1, V1, K2, V2>` | none: collected | `mapEntry` returns `Iterable<[K2, V2]>`, read from the standard library |
| `Resource<C>` | none: collected | its `Context` parameter's generic methods are opaque members |
| `EagerCollection<K, V>` | none: collected | it extends `Managed`, whose brand `[sk_managed]: true` is a symbol-keyed field; its generic methods are opaque members |
| `Values<T>` | none: collected | it extends `Iterable<T & DepSafe>`, read from the standard library |

The admitted contract work is larger than recognizing the declaration keyword:
`Mapper` has four `Json`-bounded parameters and a method returning
`Iterable<[K2, V2]>`; `Values<T>` extends `Iterable<T & DepSafe>` and supplies
`getUnique` and `toArray`; `EagerCollection` extends `Managed` and supplies the
generic `map`/`merge` calls used below; `Resource` connects a collections
parameter to `instantiate`. The `runService` value import and its return type
are a separate, effectful module contract. Each dependency must either be
interpreted and certified or appear as an explicit external assumption.
Collecting the pinned `Mapper` declaration reaches its method and resolves its
`Iterable` result reference to the configured TypeScript project's
`lib.es2015.iterable.d.ts` declaration; omitted trailing type arguments are
retained as source defaults. Its first refusal is now `Context`'s generic
method, above. Behind it, `Values` extends `Iterable<T & DepSafe>`: the
library interface has a computed-symbol method and references to `Iterator`,
so resolving its name is not interpreting it, and `T & DepSafe` is an
intersection over a binder. The tuple shape in `mapEntry`'s result is
interpreted by the declaration graph; finite ground applications of generic
declarations use their source bounds and trailing defaults. Named tuple
position labels still refuse explicitly.

The next file-level steps are to model the top-level initializer and other
declarations without dropping their effects, and extend the admitted interface
slice to generic methods, constructor contracts, `bigint`/`symbol` and
computed-symbol keys, and bounded or recursive generic instantiation over
binders, together with value imports. Then represent the imported API contracts as explicit client assumptions; checking
the runtime's implementations is the separate third milestone below. Class construction,
parameter properties, `implements`, method receivers and prototype lookup must
be certified before counting a mapper body. Later source statements include
service creation, top-level `await` and asynchronous shutdown; they remain
outside the current fragment. Skipping any of these statements and then
counting the whole file as verified would change the program under test.

### Cross-file recursive `Json` milestone

**Status: partly implemented.** The concrete target is to verify small source functions that
import and use the *actual* `Json` declaration at the pinned upstream revision,
then use the same contract in `Mapper` bounds. Passing a locally rewritten or
nonrecursive approximation of `Json` does not close this milestone. This is a
prerequisite of the mapper and collection milestones below, not a claim that
the runtime implementation satisfies its API contracts.

Checkpoint 1 has a source-closure implementation for aliases and single
field/index/callable-property/method interfaces in
[`declaration-graph.mts`](../tools/declaration-graph.mts). The fixture pins the
tracked `skiplang-json` source; TypeScript follows the core star export,
API-local `export type`, and the workspace link to that source. The
collector reaches `Json` and `JsonObject` as two nodes without inlining either,
and a separate two-file generic cycle checks binder and argument retention.
Each collected alias now also has a structural source-type expression: the
pinned `Json` cycle retains its readonly array, dictionary index, unions,
`null`, and declaration-identified references; the generic cycle retains
binder indices and applied arguments. Unsupported syntax is refused during
collection rather than left inside an opaque span.
Nested, optional and generic methods, merging and other declaration kinds
still refuse explicitly. The
Fragment document has one required `declarations` slot: the roots and the
deduplicated declaration equations. The source parser fills it for named
type-only imports and for the file's own declarations. TypeScript's checker, in
the file's configured project, decides what every name denotes: each client
import, and every reference and `extends` clause inside a collected
declaration, must resolve to exactly one alias or interface declaration. Global
declaration files the project loads, the standard library included, supply
unimported names; merged declarations refuse. Code the graph uses must be code
TypeScript accepts: an error TypeScript reports in a collected declaration (an
interface that incorrectly extends its base) or on an import or export
statement the resolution passes through (an ambiguous star reexport) refuses
the graph. Errors elsewhere in those files are not the graph's: the snapshot's
core barrel has errors for modules it omits, none of them on the `Json` route.
A synthetic global interface verifies end to end. TypeScript reads the declarations it resolves once, and
the equations are parsed from its own trees; the parser only checks that
TypeScript read the same client bytes it parsed. Function annotations are
source type terms like declaration bodies, and a reference in one names the
declaration TypeScript resolved; the producer decodes both with one decoder. Exported source functions are accepted as strict
module code. With that project, both `nest` and `lookup` in
[`recursive-json.ts`](examples/recursive-json.ts) now reach Lean evidence
production and checking and verify. In
[`recursive-json-values.ts`](examples/recursive-json-values.ts), Boolean,
number, string, array and object values pass to a `Json` consumer. In
[`recursive-json-variants.ts`](examples/recursive-json-variants.ts), those
kinds of values pass to a universally checked `<T extends Json>` closure.
At each call OCaml proposes the imported `Json` bound as a widened
instantiation of `T`; Lean checks the concrete argument and the bound. These
calls do not establish separate precise inferred types for `T`. Four invalid
clients in the same project reach search and fail: a non-JSON
dictionary member, a missing-key read without `undefined`, and a function
passed to `<T extends Json>`, and a `boolean[]` assigned to a writable `Json[]`
alias before a string write and Boolean read. TypeScript accepts the last
program; the verifier refuses the alias assignment because a location's write
contract cannot widen. OCaml reserves empty rows for imported declarations
without parameters; Lean derives and fills their equations from the Fragment's
source-type expressions. A finite ground application of an unbounded imported
generic instead gets an interned row for its substituted equation. The producer
uses that row as a candidate, while Lean independently substitutes the source
binder arguments and derives the row before checking the client. Synthetic
cross-file clients now verify unary, two-parameter, and transitive record
applications, plus tuple and callable applications; a wrong result fails proof search. Recursive generic applications
need memoized application rows. Imported bounds are checked using the existing
certified subtype relation after each argument is completed; failed bounds
refuse, including a supplied argument that violates its bound. Source defaults
are applied in declaration order, so a later default may use an earlier
argument. Interface `extends` edges also remain explicit in the collected
source document. For disjoint plain object fields, Lean derives one equivalent
record contract from the local and inherited fields; other representable
intersections use the graph's general conjunction operation. OCaml inspects
the bases only to propose member-read types. A generic inherited object and
two-base interface now verify, while an incorrect inherited-field result
fails proof search. Overlapping fields and richer inherited shapes are still
refused by the OCaml proposal path. The suite refuses producer-filled rows and source-authored internal
graph labels. The CLI accepts `--project` with a source checkout containing the
TypeScript files, package manifests and workspace symlinks; the test and command
above read the same checked-in source snapshot. All intermediate JSON is
generated from that source tree. The viewer uses the same project mapping from
the executable case inventory; a bare CLI invocation still needs `--project`.
This is conditional verification relative to the trusted declaration document, not
closure of the full milestone.

An interface or alias declared in the client file now uses that same source
declaration graph. The local `Derived extends Base` example verifies, and an
incorrect inherited-field result fails. TypeScript resolves the local root to
the declaration itself, as it resolves an imported one. Every declaration
application, local or imported, has one interpretation from its source
equation. With ground arguments it lowers to graph rows. With an argument over
the enclosing function's rigid binders, Lean expands the equation with the
arguments substituted: parameters, functions and arrays become the forms the
rigid checker reads, and parameter-free parts still lower to graph rows. The
OCaml encoder expands the same application from the same definition. So
`GenericCallable<T> = (value: T) => T` applied to a rigid `T` verifies, and a
wrong result fails with the same generic obligation, whether the declaration
is local or imported; `test.mts` compares the two outcomes. A record over a
rigid binder (`{ readonly value: T }`) stays outside the rigid checker for both.
Bounded declarations and recursive applications over a binder refuse.
Declaration location is no longer a separate type meaning.

The present source checker recognizes `boolean`, an earlier rigid parameter,
and a non-generic declared graph node as bounds. This is a translation gap,
not a semantic restriction on generics: a well-formed bound can be any type
the model interprets. General ground bounds should go through the same
annotation-to-graph translation as parameter and result types, with the
translated upper bound checked under the preceding binders. Adding individual
special cases for `number`, objects, or arrays would leave the wrong boundary.

OCaml also reads the same source-type expressions to choose useful candidates
for fresh literals, including a dictionary candidate for `{ child: ... }`.
That inspection has no authority over the imported graph: a wrong hint can
lose a proof or propose a false claim, but Lean derives the graph equation and
checks every field obligation independently. This keeps candidate search from
becoming a second implementation of the imported type's meaning.

The declaration document contains the collected declaration equations. Resolution
is TypeScript's, under the snapshot's dedicated
[`upstream/tsconfig.json`](upstream/tsconfig.json), which includes the
imported-`Json` clients and mirrors upstream's strict Node16 resolution;
`--project` names it explicitly, leaving the other OCaml examples' TypeScript
project unchanged. Because the snapshot
contains neither built `dist`
declarations nor npm's workspace links, its two package entry points have
explicit source `paths` mappings; the `skiplang-json` workspace link is real.
The remaining trust assumption is that this project configuration agrees with
the actual upstream build. The TypeScript checker and our source-type parser
remain trusted: Lean interprets the collected equations but does not reparse
TypeScript or reconstruct package exports and symlink routes. TypeScript reads
each declaration from its project, and the collector parses that same tree;
only the client text is compared with the independent source parser's text.
There is no independent byte check for declaration files or module mappings.
The test's pinned hashes guard accidental fixture changes and are not a
soundness argument. The result remains relative to the supplied source tree
and this front end, rather than verification of arbitrary imports.

`core/src/api.ts` imports `Json`, `JsonObject` and `DepSafe` from
`../skiplang-json/index.js`. In the Skip checkout, `prebuild.mjs` makes
`skipruntime-ts/core/skiplang-json` a symlink to the tracked
`skiplang/skjson/ts/binding/src` directory. The canonical declaration is
`skiplang/skjson/ts/binding/src/index.ts`, not a generated copy under `core`.
At commit `5c902f17431d963c1b6e07fc1d15da054ba30e70`, it says:

```ts
type Json = boolean | number | string | readonly (Json | null)[] | JsonObject;
type JsonObject = { readonly [key: string]: Json | null };
```

The type equations are one mutually dependent graph: `J = boolean ∪ number ∪
string ∪ readonlyArray(J ∪ null) ∪ O`, and `O = readonlyStringDictionary(J ∪
null)`. `null` is admitted *inside* those collections, not as a top-level
`Json`. Keep the named nodes and their declaration identities; recursively
inlining an alias, choosing an arbitrary unfolding depth, or replacing a cycle
with `unknown` changes the contract. Type parameters on other declarations
must remain binders and arguments on graph edges, rather than becoming global
names or a finite set of observed instantiations.

The inline readonly string-index slice now verifies parameter and result
contracts, named and computed string-key reads returning `boolean | undefined`,
and a fresh two-field dictionary literal through OCaml claims, Lean source lowering and
evidence checking. `invalid-index-signature-read.ts` shows that a missing-key
read cannot establish plain `boolean` although `tsc --strict` accepts it.
`invalid-index-signature-construction.ts` confirms that every fresh field must
meet the index value type. `invalid-dynamic-index-read.ts` checks the same
missing-key bound for a computed key; its certificate has a tampering control.
The same source path now accepts required named fields alongside a readonly
string index in parameter and result contracts, preserving their invariant or
readonly-view roles. The mixed `readMixed` example checks a computed key;
`invalid-mixed-index-read.ts` checks absence even when another field is
required. Mixed-literal construction and a precise read of a named field from
such a contract remain outside this slice. The graph's `dict` clause supports
recursive index operands; the explicit-universe `Json` example above now
exercises that path.

Current progress against the `Json` prerequisite:

| Checkpoint | Current result | Remaining boundary |
| --- | --- | --- |
| 1. Source closure | Canonical `Json`/`JsonObject` cycle, workspace link, cross-file generic cycle, trailing type-parameter defaults, single field/index/callable-property/method interfaces, interface heritage edges, and configured global declaration sources collected. | Computed-symbol keys and methods, `bigint` and `symbol`, declaration merging and value declarations remain outside this collector. |
| 2. Shared graph and gate | Imported alias and supported interface equations, including a global declaration, reach the common Fragment and Lean request; TypeScript supplies declaration identities; the client-byte comparison checks the two parser inputs. | The configured project and source parser remain trusted; richer declarations are refused. |
| 3. Semantic interpretation | Recursive readonly array, dictionary, fixed callable, interface method receiver, disjoint plain-object inheritance, and finite ground imported generic record, tuple and callable applications with bounds and defaults reach `CertifiedPlan` and `checkJson_safe`. | Recursive generic applications, overlapping or richer inherited contracts, mutable dictionary and implementation contracts need their own certified paths. |
| 4. Relative contracts and controls | Forged alias equations, targets, source bytes and evidence have negative controls. | External value-contract assumptions and their eventual discharge are not yet represented. |
| 5. Actual-source acceptance | Imported `Json` clients, a bound-instantiation case and four negative controls run end to end; synthetic cross-file generic applications with bounds, defaults and inheritance also verify. | Actual `Mapper` now first refuses an unsupported method signature in `Context`; library iterator semantics, richer generic interfaces, classes and their dependencies follow. |

The checkpoints below spell out the current implementation and the remaining
proof and trust obligations; the table above records the outcomes.

Implementation checkpoints:

1. **Canonical source closure.** The configured TypeScript checker resolves
   each named import and each reference in a reachable declaration to one
   alias or interface; the collector parses those declarations from the
   checker's own source trees. Each declaration has a module-qualified
   identity, binders, spans, an expression and heritage edges. References
   occur in those expressions, bounds, defaults and edges, with no second
   serialized edge inventory. The pinned fixture hashes guard changes to
   test inputs; they do not validate the resolution or bind request bytes.
2. **One shared graph format and source gate.** The existing Fragment
   document carries those equations to Lean, which interprets them rather
   than trusting the OCaml candidate graph. TypeScript's project configuration
   and source parsing remain trusted. The client-byte comparison ensures the
   source parser and TypeScript checker saw the same client text; both use
   TypeScript's own trees for declarations. The configured package exports,
   workspace links and `paths` entries are assumptions about the upstream
   build, not independently certified mappings. Unsupported declarations are
   refused at the source gate.

3. **Semantic interpretation and proof.** Extend the existing guarded
   recursive-graph interpretation with the dictionary constructor and prove
   that the accepted graph equations denote admissible semantic types. Define
   indexed lookup over actual JavaScript properties, including absence: a
   missing key reads `undefined`, so an arbitrary `JsonObject[key]` cannot be
   promised only `Json | null` merely because TypeScript says so. A readonly
   index is a read view, not a claim that no other alias can mutate the object;
   writes and flow refinements still obey fixed world contracts. Extend
   subtyping, indexed-read obligations, normalization and evidence checking
   with their safety proofs. A successful graph check must enter the exhaustive
   `CertifiedPlan` path and the `SourceClaimJson.checkJson_safe` conclusion;
   an unconnected Lean lemma or OCaml proposal is not verification.
4. **Relative contracts and controls.** Forged source equations,
   declaration identities, client bytes and evidence have rejection controls.
   These controls exercise the existing request and proof boundary, not an
   independent declaration-byte or module-mapping hash check. Imported value
   contracts remain external assumptions until implementations are checked;
   an imported type equation does not assert that a runtime value implements
   it. Make those assumptions visible in the report and theorem boundary.
   Cross-file recursive and invalid unguarded-cycle fixtures exercise the
   graph interpretation.

5. **Actual-source acceptance.** Add positive OCaml-producer cases that import
   the pinned `Json` through the real package path, build nested arrays and
   objects containing `null`, read them safely, and instantiate a bound such
   as `T extends Json`. Add negative cases for a non-JSON nested value and a
   missing dictionary key used as though it could not be `undefined`. Each
   case must reach independent Lean evidence checking with its expected
   outcome; record the first blocker if one remains. Then use the same graph
   for `Mapper<string, number, string, [number, number]>`'s four bound
   obligations. `DepSafe`, `Values`, `Iterable` and class bodies may still be
   separately unsupported; do not count those as failures of this milestone
   or silently weaken their contracts to make the mapper pass.

The milestone closes when at least one real-import `Json` example and its
bound-instantiation case verify against the canonical declaration, the negative
and forged controls fail at their intended obligations, the recursive graph is
accepted through the soundness theorem, and the reader states any remaining
external assumptions. Check that all new cases are counted by the OCaml suite
and viewer; report verified, rejected and unsupported outcomes separately.

For classes, preserve separate `[[Call]]` and `[[Construct]]` capabilities on
one function object. `new` allocates an instance, runs its constructor with
that instance as receiver, and exposes it only under the JavaScript
constructor-return rules. Prototype lookup supplies methods on instances;
their receiver comes from the call reference as in part 5. Instance fields
and parameter properties need initialization obligations before the instance
can satisfy its exported class contract. Do not lower `new C` to an ordinary
call or treat an `implements Mapper` clause as proof of the constructor and
method bodies. The first mapper milestone ends only when those bodies and the
actual imported method contracts are certified, with independent failures for
initialization, receiver, result and forged evidence.

| Requirement | Work to assess after part 5 |
| --- | --- |
| Mutable objects, captured callbacks, fixed storage contracts | Existing foundations; exercise them together on actual runtime clients. |
| Methods using `this` | Part 5 prerequisite; verify its coverage against mapper methods. |
| Classes, constructors, `new`, field initialization | Additional semantics and certified lowering; construction is not ordinary invocation. |
| `Mapper<K1, V1, K2, V2>` and bounds such as `K extends Json` | Ground multiple-parameter applications, source bound checking, and disjoint object inheritance work; `Context` first needs a generic method with constructor and variadic tuple contracts. |
| `new (...params: Params) => Mapper<…>` | Constructor contracts and generic tuple packs; ordinary quantified array-rest support is insufficient. |
| Recursive `Json`, dictionaries and optional fields | The [cross-file `Json` milestone](#cross-file-recursive-json-milestone) covers the canonical recursive type and indexed reads; optional named-field presence is a further extension, still distinct from present-undefined. |
| `Iterable`, iteration and array/library methods | Explicit contracts and execution semantics, including callback effects and iterator behavior. |
| Promises, exceptions and native/Wasm bindings | Further model extensions and explicit external assumptions for the implementation. |

The three framework milestones remain open:

1. **One actual mapper class.** Verify constructor initialization, method
   receiver use and callback results end to end. Include independent failures
   for an invalid initialization/receiver/result and forged evidence. Merely
   accepting the class declaration or trusting its method signature is not
   completion.
2. **A synchronous collection graph.** Verify the synchronous mapper/resource
   portion of `sum.ts`, including generic collection methods, constructor
   arguments and iteration, against explicit runtime contracts. Record which
   contracts are external assumptions; keep service startup and asynchronous
   shutdown visible as remaining work. This establishes client typing relative
   to those contracts, not correctness of the runtime implementation.
3. **Runtime implementation.** Check the TypeScript implementation behind those
   contracts, extending to asynchronous behavior, exceptions and native/Wasm
   boundaries. Discharge the contracts where implementation is modeled and
   enumerate the remaining external assumptions. Count checked implementations,
   not declarations, toward this milestone.

### Fragment extensions still required

Work proceeds extension first: each fragment extension is developed with its
own witnesses, negative controls and tampering tests, following
[Extending the producer](#extending-the-producer), and only then assessed,
separately, for how far it moves `sum.ts` and the milestones above. An
extension is not shaped around `sum.ts`, and progress toward the milestones is
reported from measured first blockers, not from the extension landing.

The target is the corrected client
[`reactive-sum-sound.ts`](examples/reactive-sum-sound.ts). Required for the
first milestone, in order of how much each gates:

1. **Module-level code and value imports.** Done: module functions reachable
   from one another at their signatures, module constants read by functions
   at their annotations, top-level expression statements, and an
   initialization unit with its order check, and value imports of
   non-generic functions, annotated constants and classes, assumed at their
   declared types and listed in the declaration document. Remaining: generic
   value imports (`InputDefinition<K, V>`, `runService`), globals (`process`)
   as external contracts, top-level `await`, module-level `let`, and the Lean
   theorem composing the units into a module result.
2. **Classes.** Done for top-level classes without inheritance or generics:
   a class declares its instance type in the declaration graph (fields at
   their annotations, methods as readonly fields whose receiver is the
   instance, parameter properties); its value is lowered in module
   initialization to method closures allocated once, as its prototype's, and
   a constructor that allocates the instance from the field initializers,
   parameter properties and `this.f = e` assignments; `new C(args)` calls
   it, and no other read of the class is admitted. Remaining: `implements` as
   a checked obligation, inheritance (`extends`, needed by
   `InputDefinition`), generic classes, general constructor bodies, statics,
   and array operations inside methods (a closure limitation `AddIndex`
   meets).
3. **Generic calls.** Done for generic module functions and generic imported
   functions and classes (`InputDefinition<K, V>`): a call validates its
   instantiation and reaches that instance; a class's `extends` is a base of
   its instance type; and each ground application of a generic declaration
   with methods has its own row, its methods' receiver. Remaining: generic
   methods (next item) and constructor or tuple-pack parameters.
4. **The runtime API's declaration forms.** `Mapper` reaches `Context` and
   `Values`; interpreting them needs:
   - generic interface methods, i.e. quantified method signatures: read today
     as opaque readonly members, which a program may read but not call. They
     are quantified types in the graph, one semantics for every use (below,
     "Quantified types"); calling one (`EagerCollection.map`) is its
     elimination;
   - constructor types (done: construct signatures in the calculus, class
     values first class, `new` on any value with a construct signature) and
     generic tuple packs, `new (...params: Params) => T` with `Params extends
     readonly DepSafe[]` (remaining);
   - `bigint` and `symbol` (done: opaque values in the calculus and types
     in the graph, and `typeof` tests for every shape but `"object"`), and
     symbol-keyed properties (done: the heap's keys are strings or symbols,
     and a declaration's `[x]: T` member, with `x` a `unique symbol`
     constant, is a field keyed by that symbol). Remaining for `Managed` and
     the `Opaque` types: `typeof x` of a unique symbol as a singleton type
     (the `internal.ts` tags), and a class field's definite-assignment `!`
     (`Frozen`'s `[sk_managed]!: true`);
   - types over rigid binders, such as `T & DepSafe`.
5. **Library contracts**, read from TypeScript's own standard library
   declarations (`lib.*.d.ts`) through the same declaration graph as any
   library, not written by hand. Done: global type names are declaration
   roots; an interface declared several times is merged, as TypeScript
   merges it; well-known symbol keys (`[Symbol.iterator]`) are symbol keys; a
   declaration's `any` is `unknown`; a recursive generic application at the
   same arguments is its reserved row. `Promise<T>` is read this way (its
   generic `then`/`catch` are opaque, so its argument is not yet visible).
   `Iterable`/`Iterator` are read too: `next(...[value]: [] | [TNext])` is
   one signature per tuple, and `return?`/`throw?` are optional fields.
   Remaining: arrays as iterables (every `mapEntry` returns an array literal as
   `Iterable`), and `Array.prototype.reduce` and `sort` with their callback
   effects and mutation.
6. **Optional field presence** (done for mutable optional fields: see
   DESIGN.md's object milestone; `optional-field.ts` verifies). Remaining: a
   readonly optional field, `in` tests and presence narrowing.
   `getUnique(_default?: { ifMany?: T })` needs only the done part.
7. **Exceptions.** `getUnique` throws when a key has several values.

Required for the second milestone in addition:

8. **Generic calls taking classes.** `.map(Plus)` and `.map(AddIndex, 0)`
   infer constructor and tuple-pack arguments, chained across `merge` and
   `map`.
9. **Asynchronous startup.** `async`/`await`, the library `Promise`, and the
   `runService` and `process.on` contracts, kept visible as out-of-scope
   effects until they are modeled.

**Branded types (planned, not yet implemented).** TypeScript brands types two
ways: a `private` or `protected` member makes a class nominal, and a field
keyed by a `unique symbol` can be written only by code holding the symbol.
The instance types here are structural and ignore visibility, so today a
brand such as `AbstractEagerCollection`'s `__sk_collectionBrand` is just a
field any object of the right shape has. That reading is sound, since types
describe runtime values, but it is weaker than the brand intends. With
classes in the fragment, brands can be real: a class's instances are exactly
the objects its constructor allocates, so its instance type can carry a
hidden brand field no source can spell and only that constructor sets. Then
only constructed instances (and, with inheritance, subclass instances)
inhabit the type. A class declared elsewhere whose constructor is not
checked here gets its brand as an external contract. `unique symbol` brands
(`Managed`, the `Opaque` types) are symbol-keyed fields, which the fragment
now reads (item 4). Brands matter for `SharedCollections`: its bound is meant to admit
only runtime collections.

**Quantified types (in progress).** A generic method's type is a scheme row
of the graph: binders, which are parameter rows, and signatures whose rows may
mention them (`Promise<T>`'s `then` reaches `PromiseLike<R1>`). The
denotation is indexed by an assignment of the parameter rows as well as by the
label, over the same guarded fixed point (`qDenote` in
`Types/PositiveGraphs.lean`): a scheme row means one callable meeting its
signatures at every reassignment of its binders to a family of closed values.

Stages 1 and 2 are done. A `NormalGraph` carries clause rows, scheme rows,
parameter rows and the assignment `env`, and `meaning G` is the denotation at
`G.env`. No check reads `env`, so a theorem proved for every graph holds at
every reassignment `{G with env := η}` (`meaning_reassign`): a derivation that
types a generic body once, with its binders opaque, is sound at each instance.
This is what the introduction rule will use, so the soundness proofs are not
redone for it. `Types/QuantifiedGraphs.lean` proves elimination
(`scheme_elim`), the introduction principle (`scheme_intro`), and that
without scheme rows the denotation is the parametric semantics
(`qDenote_no_schemes`). Parameter and scheme rows are opaque to every check:
they have no clauses (`expand` of a type holding one is empty, so
`Represents` and `Answers` fail), a parameter is below itself, a union holding
it, and `unknown` (`Opaque` in `Valid`), and test refinement keeps it
(`Tests/QuantifiedRowTests.lean`). The graphs the pipeline builds have only
clause rows, so every verified result is unchanged.

Stage 3 is done: subtyping over scheme rows, with certificates
(`PositiveRules`, `Proof.inst` and `Proof.gen`).
- *Elimination* (`Sub.inst`): a scheme row is below an arrow type whose
  signatures are instances of its own. The instance is checked by a table of
  entries (row, context, image): the context says what each binder in scope
  stands for, an instance type or, under a scheme mapped to another, that
  scheme's binder, and each row maps to the graph's substituted copy of it
  (`Box<T>` to `Box<boolean>`), clause by clause, or to itself when it has no
  free row the context names. Scheme rows map to scheme rows up to renaming
  their binders, without capture. Under its context a row means its image
  (`table_row`). This is capture-avoiding substitution up to renaming of bound
  binders, which the colouring of generic methods (stage 4) needs: one binder
  row serves several scopes. A call
  through a generic function is then the existing call rule after
  subsumption: `id(true)` is typed a Boolean, `wrap(true)` a `Box<boolean>`.
- *Coverage* (`Sub.gen`): a type is below a scheme when it is below the
  scheme's signatures with the binders opaque and none of its free parameter
  rows is a binder (a checked free-variable certificate);
  it then means the same at every instantiation (`agree_free`). So
  `<T>(x: T) => T` is below `<U>(x: U) => U`, and `(x: T) => T` at one `T` is
  not below `<T>(x: T) => T`.
- Subtyping is proved at every assignment (`Sub.sound_at`). This is where "no
  check reads `env`" became a theorem: the one judgment that was indexed by
  the graph beyond its rows, overload coverage, is now indexed by the graph's
  compatibility test.
- The Lean producer proposes instance maps by matching a signature against
  the target (`matchInst`), and generalizations from a type of the pool that
  states the scheme's signatures. Tests: `Tests/QuantifiedRowTests.lean`.

`TypeSchemes.lean` is an older, separate scheme layer for local generic
closures (with bounds and rest signatures, outside the graph). Scheme rows
subsume it once they have bounds (stage 5) and rest signatures; that slice
then moves onto them, so there is one mechanism.

The one semantics serves three rules, each needed:
- *elimination*, calling a generic method at an instance: every generic call
  `sum.ts` makes (`EagerCollection.map`, `Promise.then` under `await`,
  `Array.reduce`) is one, on a value the library provides;
- *introduction*, a body checked at rigid binders, as a local generic closure
  already is (`TypeSchemes.scheme_intro`): no client `sum.ts` needs it, but
  the runtime it calls implements every one of those methods
  (`EagerCollectionImpl.map`, `ContextImpl.createLazyCollection`, in
  `core/src/index.ts`), and TypeScript accepts it for classes and objects
  implementing generic interface methods, custom thenables, and generic
  functions passed where a generic function type is expected;
- *coverage* between two quantified types, for the last of those.

So there is no instance-only version first: the rules are built once, over
this semantics. Stages: (2, done) scheme rows in `meaning`, with the typing
rules never reading a scheme label as a ground clause; (3, done) coverage
and elimination, with certificates; (4) the pipeline; (5) bounded binders
(`K2 extends Json`), which need the denotation to be non-expansive in the
assignment; introduction when the runtime is a target.

Generic methods are necessary for `sum.ts`, not sufficient. Each of its
generic calls also needs something else: `await` needs an operational
meaning (the engine calls `then` and resumes from a job queue, which the
calculus does not have: a faithful model or a trusted `await` step);
`.map(Plus)` needs tuple-pack binders (`Params extends readonly DepSafe[]`,
used as a rest parameter, so an instance fixes the arity) and bounded
binders; the mappers' bodies return array literals as `Iterable` and call
`reduce`/`sort`, which needs arrays as library objects, with `Array<T>`'s
declared methods, where the calculus's arrays are stores with none.

**Record values as `Json` (to do).**

*The problem.* A record type is open: its value may carry keys the type does
not name, of any type. So `{ readonly n: number }` is not a subtype of
`Json`'s object arm `{ readonly [k: string]: Json }`. Readonly does not help:
the unsoundness is on reads, since an unnamed key would be read at `Json`
(`Object.values`, serialization), not on writes. TypeScript accepts the
subtyping and is unsound; SKJS refuses it (`skjs-rules.md` §28), and so does
the model: `recT` is open and `dictViewT` constrains every present string key.
A Skip client whose collection keys or values are records meets this at the
framework's `K, V extends Json` bounds. `sum.ts` does not: its keys and values
are strings and numbers.

*What was done elsewhere.* Skipper generates such types from OpenAPI schemas.
- skipper#1217 intersected each generated object type with
  `{ readonly [key: string]: Json | null }`: sound, and a `Json` subtype.
- skipper PR #1239 (open) replaced it with a comment tag re-expanded to the
  intersection only for SKJS, because under `tsc` it broke `deepFreeze`.
- skipper PR #1242 (open) proposes SKJS's closed-object type `Closed<T>`
  (identity under `tsc`) instead. Neither is merged.

*What actually breaks under `tsc`* (reproduced with `tsc` 6.0.3 against the
pinned upstream):

```ts
type Todo = { readonly title: string; readonly done: boolean }
          & { readonly [key: string]: Json | null };
const b: Todo = deepFreeze({ title: "x", done: false });   // error
```

`deepFreeze<T>(value: T): T & DepSafe`, with `DepSafe = null | boolean |
number | bigint | string | symbol | Managed`. `T` is inferred from the
literal, and the result distributes over `DepSafe`; TypeScript keeps members
such as `{ title; done } & string` (the branded-primitive idiom), whose
apparent type is the `String` wrapper, which has no string index signature.
Against the plain record the member is assignable; against the index part it
is not. These all check: a fresh literal at `Todo`; `deepFreeze(t)` with `t`
already a `Todo`; `deepFreeze<Todo>({ ... })`; the plain record type as
`Json` under `tsc`. So the intersection is not the problem, `DepSafe`'s
primitive arms at a literal's inferred type are. The workaround is local:
freeze a value that already has the type, or pass the type argument, which an
instruction to agents covers. The root-cause fix would be upstream
(`deepFreeze`'s result `T & Managed` for an object `T`).

*Plan.* No closed-object notion: `Serializable<T> = T & { readonly [k:
string]: Json }` states exactly what the framework needs, every present key
holding `Json`, and it is plain TypeScript. The model already lowers that
intersection to one dictionary clause with named fields and an index (`meet`,
`meet_sound`), and its subtyping to `Json` is dictionary coverage. Missing:
establishing it from a literal. `alloc` builds a record and `allocDict` a pure
dictionary; a literal at a record-and-index type needs one allocation rule
proving both, as `recT_fresh_dict` does for fresh slots. Witnesses: a literal
at `Serializable<T>`, passed as `Json`; a negative with a non-`Json` field;
and the `deepFreeze` form above, with its explicit type argument, once
`deepFreeze`'s declaration is in the fragment.

Generic interface variance is not on this list: the type-safe API does not
ask for `EagerCollection<K, V> ≤ EagerCollection<Json, Json>`, and the
corrected client meets `SharedCollections` through `interface Collections
extends NamedEagerCollections`.

The third milestone adds asynchronous behavior, exceptions and native/Wasm
boundaries in the runtime implementation, outside the fragment work.

Type safety alone does **not** establish reactive dependency correctness. The
API's mapper-construction and `DepSafe` restrictions aim to keep dependencies
trackable. That requires a separately stated property and justification; a
brand, interface or successful ordinary typing certificate is not its proof.
Keep this obligation distinct from the three typing milestones, with its
scope and completion criteria to be specified before claiming reactive
correctness.

For every extension, follow [Extending the producer](#extending-the-producer):
shared representations, reconstructed obligations, semantic certification and
tampering controls remain mandatory. Design for the full language while
implementing these milestones incrementally; record a remaining blocker rather
than weakening a witness or silently narrowing a milestone.

## What is proved, and what is trusted

Successful certification uses the existing Lean certificate consumer and its
soundness theorems for the modeled fragment. The OCaml inference algorithm is
not itself proved correct; a bad proposal must fail validation. Generic
variable-copy certificates and immutable read/closure/call certificates
are checked at the `CertifiedPlan` boundary and covered by `checkJson_safe`.
Other scheme checking still runs in both Lean phases, but its success is not
promoted to verification until the missing semantic theorem is connected there.

The shared parser, source-to-calculus correspondence, executable toolchain and
runner remain part of the trust boundary. Source lowering being written in Lean
is not a proof of preservation of full JavaScript semantics. Existing model
assumptions and restrictions in [DESIGN.md](../DESIGN.md) still apply. This is a
first producer against that boundary, not a verified implementation of the full
TypeScript language.
