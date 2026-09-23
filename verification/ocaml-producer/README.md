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
   SourceClaims protocol. It reserves empty rows for imported declaration
   identities. Lean alone fills those rows from the source equations; OCaml
   cannot supply a competing interpretation. Graph interning is local to one
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
6. Run `dune build --root verification/ocaml-producer`,
   `dune runtest --root verification/ocaml-producer`,
   `lake -d verification/lean build` (all of it: fixtures construct shared
   structures), and `node verification/ocaml-producer/test.mts`. Run the shared
   TypeScript check and the viewer tests when their files change. SKJS suites
   are unnecessary unless a `.sk` file changes.
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

Use the real `sum.ts` mapper/resource shapes as the first integration target.
Preserve its classes, signatures and library interactions: do not rewrite it
into today's fragment and call that runtime coverage. At the start of this
work, record the upstream revision and retain the selected sources as fixtures,
with provenance and expected outcomes in `cases.mts`. Measure each function's
first blocker through parsing, proposal, lowering, evidence production and
independent checking. Report verified, rejected and unsupported separately.

The baseline is pinned to upstream `skip` commit
`cb030b5ac7beda28fd5f65e3292a485173d5faef`. The byte-for-byte
[`sum.ts`](examples/reactive-sum-prettier-ignore.ts) and
[`api.ts`](upstream/skipruntime-ts/core/src/api.ts) snapshots are checked by SHA-256 in
`test.mts`. The executable case supplies the snapshot's import universe and
records the actual first refusal: the top-level `platform` initializer at line
10 is outside the source fragment. Thus **zero of the six class callables below
are currently checked**; no producer proposal, Lean lowering, or certificate is
reached. This is one file-level blocker, not six independent findings. The
following rows name what each body will additionally need after the file-level
gates are lifted:

| `sum.ts` callable | First reached boundary | Later body requirement |
| --- | --- | --- |
| `AddIndex.constructor` | top-level `platform` initializer | parameter property and initialized instance storage |
| `AddIndex.mapEntry` | top-level `platform` initializer | method receiver, external `Values.getUnique`, tuple result |
| `Plus.mapEntry` | top-level `platform` initializer | external `Values.toArray`, array reduction callback |
| `Minus.mapEntry` | top-level `platform` initializer | nullable accumulator, array sort/reduction |
| `Add.instantiate` | top-level `platform` initializer | external collection method and generic constructor argument |
| `Sub.instantiate` | top-level `platform` initializer | chained generic collection methods and constructor arguments |

The module inventory in [`module-deps.mts`](../tools/module-deps.mts) identifies
four type imports from `@skipruntime/core` (`EagerCollection`, `Mapper`,
`Resource`, `Values`) and the runtime value import `runService` from
`@skipruntime/server`. [`module-resolve.mts`](../tools/module-resolve.mts)
follows package exports and the core reexport to source declarations, and the
test pins the routes and all six class callables. The configured TypeScript
project now includes the unchanged `sum.ts`; a separate preflight test checks
that TypeScript resolves all five bindings to those same interface or function
declarations, with exactly one declaration and matching source bytes. Forged
interface and function targets and altered API bytes are refused. This is
resolution inventory, not acceptance of those contracts. The source gate
currently admits named type-only imports of aliases and single interfaces
whose fields, string indexes, function-valued properties or method signatures
fit the imported graph. An optional parameter contributes `T | undefined` at
its position; an array rest parameter contributes its element contract to the
existing variadic call clause. These are the same call clauses as local
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
Inheritance, nested methods, optional method *presence*, generic methods, and
declaration merging refuse. All four runtime API interfaces have unsupported
members or dependencies, and `runService` is a
value import. The new interface slice therefore does not yet admit `sum.ts`.

The admitted contract work is larger than recognizing the declaration keyword:
`Mapper` has four `Json`-bounded parameters and a method returning
`Iterable<[K2, V2]>`; `Values<T>` extends `Iterable<T & DepSafe>` and supplies
`getUnique` and `toArray`; `EagerCollection` extends `Managed` and supplies the
generic `map`/`merge` calls used below; `Resource` connects a collections
parameter to `instantiate`. The `runService` value import and its return type
are a separate, effectful module contract. Each dependency must either be
interpreted and certified or appear as an explicit external assumption.
Collecting the pinned `Mapper` declaration alone now reaches its method and
resolves its `Iterable` result reference to the configured TypeScript project's
`lib.es2015.iterable.d.ts` declaration. It then refuses the omitted defaulted
type arguments: the source writes one argument for an interface with three
parameters. The library interface also contains a computed-symbol method and
references to `Iterator`, so resolving its name is not interpreting it.
The tuple shape in that result is now interpreted by the imported graph;
generic interface substitution, defaulted arguments, computed-symbol methods
and the other API dependencies remain after that refusal. Named tuple position
labels in imported declarations still refuse explicitly.

The next file-level steps are to model the top-level initializer and other
declarations without dropping their effects, and extend the admitted interface
slice to generic methods, inheritance and generic instantiation, together with value
imports. Then represent the imported API contracts as explicit client assumptions; checking
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
[`module-closure.mts`](../tools/module-closure.mts). The fixture pins the tracked
`skiplang-json` source and `prebuild.mjs`; the resolver follows the core star
export, API-local `export type`, and the workspace link to that source. The
collector reaches `Json` and `JsonObject` as two nodes without inlining either,
and a separate two-file generic cycle checks binder and argument retention.
Each collected alias now also has a structural source-type expression: the
pinned `Json` cycle retains its readonly array, dictionary index, unions,
`null`, and declaration-identified references; the generic cycle retains
binder indices and applied arguments. Unsupported syntax is refused during
collection rather than left inside an opaque span.
Nested, optional and generic methods, inheritance, merging and other declaration
kinds still refuse explicitly. The
Fragment document now has one required `imports` slot, emitted empty by the
source parser. The collector can assemble both real `Json` imports into that
shared slot with deduplicated declaration equations, module bytes, route
fingerprints, and the workspace symlink target. The source parser fills
the slot for named type-only imports when its caller supplies an explicit
module universe. The configured TypeScript project contributes the standard
library declaration files it actually loaded; these are scanned as candidate
global type sources, and ambiguous names refuse. A synthetic global interface
verifies end to end, while altered global source bytes are refused. Before
admitting a closure, a separate TypeScript checker instance resolves each
client import and every reference inside the collected type
definitions to exactly one alias or interface declaration. Its real file path and span must
match our resolver's choice; every touched module's TypeScript source text must
match the text from which our equations were parsed. The parser represents imported references in
function annotations as alias atoms whose local spellings resolve through the
declaration-identified roots. Exported source functions are accepted as strict
module code. With that universe, both `nest` and `lookup` in
[`recursive-json.ts`](examples/recursive-json.ts) now reach Lean evidence
production and checking and verify. In
[`recursive-json-values.ts`](examples/recursive-json-values.ts), Boolean,
number, string, array and object values pass to a `Json` consumer. In
[`recursive-json-variants.ts`](examples/recursive-json-variants.ts), those
kinds of values pass to a universally checked `<T extends Json>` closure.
At each call OCaml proposes the imported `Json` bound as a widened
instantiation of `T`; Lean checks the concrete argument and the bound. These
calls do not establish separate precise inferred types for `T`. Four invalid
clients using the same pinned universe reach search and fail: a non-JSON
dictionary member, a missing-key read without `undefined`, and a function
passed to `<T extends Json>`, and a `boolean[]` assigned to a writable `Json[]`
alias before a string write and Boolean read. TypeScript accepts the last
program; the verifier refuses the alias assignment because a location's write
contract cannot widen. OCaml reserves empty rows for imported declarations;
Lean derives and fills their equations from the Fragment's source-type
expressions. The suite refuses producer-filled rows and source-authored internal
graph labels. The CLI accepts `--project` with a source checkout containing the
TypeScript files, package manifests and workspace symlinks; the test and command
above read the same checked-in source snapshot. All intermediate JSON is
generated from that source tree. The viewer uses the same project mapping from
the executable case inventory; a bare CLI invocation still needs `--project`.
This is conditional verification relative to the trusted import document, not
closure of the full milestone.

The present source checker recognizes `boolean`, an earlier rigid parameter,
and a non-generic imported graph node as bounds. This is a translation gap,
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

The import document contains the collected declaration equations and their
source bytes. Resolution is cross-checked against TypeScript under the
snapshot's dedicated [`upstream/tsconfig.json`](upstream/tsconfig.json), which
includes the imported-`Json` clients and mirrors upstream's strict Node16
resolution. The checker opens this configured project explicitly, leaving the
other OCaml examples' TypeScript project unchanged. Because the snapshot
contains neither built `dist`
declarations nor npm's workspace links, its two package entry points have
explicit source `paths` mappings; the `skiplang-json` workspace link is real.
The remaining trust assumption is that this project configuration agrees with
the actual upstream build. The TypeScript checker and our source-type parser
remain trusted: Lean interprets the collected equations but does not reparse
TypeScript, reconstruct package exports or symlink routes, or check the
`imports.sources` and `mappings` hashes. Those hashes record provenance only.
The test's pinned hashes guard accidental fixture changes and are not a
soundness argument. The result remains relative to the supplied source tree
and this front end, rather than verification of arbitrary imports.

`core/src/api.ts` imports `Json`, `JsonObject` and `DepSafe` from
`../skiplang-json/index.js`. In the Skip checkout, `prebuild.mjs` makes
`skipruntime-ts/core/skiplang-json` a symlink to the tracked
`skiplang/skjson/ts/binding/src` directory. The canonical declaration is
`skiplang/skjson/ts/binding/src/index.ts`, not a generated copy under `core`.
At commit `cb030b5ac7beda28fd5f65e3292a485173d5faef`, it says:

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
| 1. Source closure | Canonical `Json`/`JsonObject` cycle, workspace link, cross-file generic cycle, single field/index/callable-property/method interfaces, and configured global declaration sources collected. | Defaulted type arguments, computed-symbol methods, inheritance, merging and value declarations remain outside this collector. |
| 2. Shared graph and gate | Imported alias and supported interface equations, including a global declaration, reach the common Fragment and Lean request; TypeScript checks declaration identities and source bytes. | The configured project and source parser remain trusted; richer declarations are refused. |
| 3. Semantic interpretation | Recursive readonly array, dictionary, fixed callable, and interface method receiver clauses reach `CertifiedPlan` and `checkJson_safe`. | Generic-interface, mutable dictionary and implementation contracts need their own certified paths. |
| 4. Relative contracts and controls | Forged alias equations, targets, source bytes and evidence have negative controls. | External value-contract assumptions and their eventual discharge are not yet represented. |
| 5. Actual-source acceptance | Imported `Json` clients, a bound-instantiation case and four negative controls run end to end. | Actual `Mapper` first refuses defaulted `Iterable` arguments; library iterator semantics, generic interfaces, classes and their dependencies follow. |

The checkpoints below state the design obligations in dependency order; the
table above records which parts have actually been implemented.

Implementation checkpoints:

1. **Canonical source closure.** Pin the tracked `skiplang-json` declaration
   bytes and the `prebuild.mjs` mapping at the upstream revision. Extend module
   resolution through local `export type { Json }`, relative imports and the
   mapped workspace path. Starting from a requested imported declaration,
   collect exactly its reachable type definitions across files, including
   cycles, with module-qualified declaration identities, binders, source spans
   and a fingerprint for every file and mapping used. Resolve each edge once;
   report absent, ambiguous or unsupported edges at their source location.
   This is still provenance, not type acceptance.
2. **One shared graph format and source gate.** Represent that closure in the
   existing Fragment/claim language, including parameterized references,
   recursive nodes, readonly arrays and string index signatures. Update all
   producers, decoders and printers together; do not add an OCaml-only shape or
   a second accepted wire format. The trusted source parser must derive the
   graph from the snapshotted declarations and distinguish type-only imports
   from runtime values. The request and evidence must bind the client, every
   declaration and the resulting graph to their bytes. Include the authority
   for package exports and workspace links, not only their chosen destinations;
   validate that authority independently or state it as an external assumption.
   Keep imports refused until the independent checker consumes and validates
   this information.
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
4. **Relative contracts and controls.** Imported value contracts are explicit
   assumptions for client safety until their implementations are checked; an
   imported type definition is an interpreted graph, not an assertion that a
   runtime value implements it. Make those assumptions visible in the report
   and theorem boundary. Mutate a declaration, reexport, symlink mapping,
   graph equation, binder argument, source hash and certificate independently;
   both evidence production and checking must refuse the forged documents.
   Include a cross-file mutually recursive fixture and an invalid unguarded
   cycle, so this is general graph support rather than a special `Json` case.
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
| `Mapper<K1, V1, K2, V2>` and bounds such as `K extends Json` | Multiple parameters, structural bounds and richer generic bodies beyond the current rigid slice. |
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
