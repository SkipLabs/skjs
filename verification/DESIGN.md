# Independent verification of SKJS results

The goal is to check selected SKJS claims with a small, independently justified
consumer. It is not to prove SKJS's inference implementation sound. SKJS supplies
candidate types and invariants; acceptance requires derivations in an independent
calculus whose rules are proved sound against its execution model.

The chosen architecture has a stateful positive-type calculus, a serialized
certificate consumer, and a source adapter for parameterized null/undefined/boolean functions.
The extraction format may change to provide the program points, binding identities and exact
types needed by the chosen calculus. SKJS acceptance, inference and diagnostics
must remain unchanged by this experiment. A rejected safe program is an
incompleteness finding to preserve, not a reason to extend the checker.
Extraction-only changes must preserve that behavior.

This document owns architecture, design decisions, trust boundaries, priorities,
and integration status. The [documentation map](README.md#documentation-ownership)
assigns mathematical rules, semantic definitions, wire formats, and user workflows
to their detailed references. Link to those definitions rather than duplicating
them here.

## Corpus-led priorities

Prioritise known unsoundness over adding syntax for its own sake. Auditability wins over raw language
coverage: a milestone should expose a witnessed bad claim or settle a concrete
semantic obstacle. Operator integration is useful
when it makes those witnesses reachable; it is not itself the next priority.

The evidence source is branch `docs/type-soundness-corpus`, reviewed here at
`bf20814b4c0bfc72305e9e58411e13da68f94bca`. Its
[ledger](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/ledger.yaml)
records statuses; the deep dives explain causes and the issue reports link runnable
reproductions. The corpus models SKJS revision `bafdcf7c` (2026-08-05), so its
verdicts must be rechecked against the binary used by this pipeline. It is a source
of targets, not an assumption that the current checker still has every defect.
The independent calculus need not reproduce or prove SKJS's inference machinery.

### Immediate targets with the existing stateful foundation

Issues #597/#598/#599 and deep dives F/H are the first group to cover systematically.
The existing captured-write example and the direct-write compound example cover
instances of this known mutation/refinement family; they are not new bug discoveries.
Two further targets offer more value now than another unrelated expression form:

| Next target | What the verifier should expose | Work and boundary |
| --- | --- | --- |
| **1. Both directions of alias writes — `L-MUT-ALIAS`, deep dive H.** [Corpus report](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/narrowed-alias-stale-write.md). | A narrow alias cannot promise Boolean contents while another alias may legally write null; conversely, writing through a wide alias cannot preserve the original view's non-null read fact. | Reduce to locally allocated `{ value: null \| boolean }` cells and explicit aliases. The calculus already has shared locations and invariant references. Expect an unjustified alias contract in the first direction and a stale read in the reverse direction; pin the actual failing obligation. Do not introduce covariant mutable views to accept the original export. |
| **2. A closure reads under its creation-time narrowing — `L-STALE-READ`, deep dive F.** [Corpus report](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/stale-closure-reads-narrowing.md). | A reader created while a cell is non-null cannot promise a Boolean result after another write stores null. This differs from a callback that writes and leaves the caller's refinement stale. | Use the report's field-level variant, a local primitive cell and a unary null-argument reader. No mutable lexical binding or external object parameter is needed. Exercise the arrow guarantee over every admissible future heap: a creation-time observation is not a permanent captured invariant. |

Boolean/null reductions of these three programs (both alias directions and the
captured reader), and of the loop target below, were checked on 2026-09-08 with
the current SKJS binary. All four were accepted in normal collection mode, had
no unavailable named binding or expression types needed by the reductions, and
returned null at a declared Boolean result (using true as the seed where needed).
Unused `this` exports were excluded from that claim-availability check. These
probes confirm known failures survive the reduction; they do not establish that
the current verifier already reaches a semantic rejection of the raw claims.
In particular, refined cell read/write pairs still encounter the invariant-profile
boundary. Preserve the original export and label any weakened candidate separately.

For both targets add a positive counterpart: two aliases retaining the same
invariant contract, and a reader that either returns a saved immutable snapshot or
checks for null at invocation. This guards against obtaining negative coverage
merely by refusing all useful programs involving cells or closures.

### Next fragment extension: mutable locals, aimed at a known loop failure

**3. `L-LOOP-CARRIED`, deep dive F**, is the next substantial source extension.
The [corpus witness](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/loop-carried-narrowing-stale.md)
and the older design's reduced example need no arithmetic, strings, general calls or
new loop construct after reduction:

```ts
function loopCarried(): boolean {
  let value: null | boolean = true;
  let second: boolean = false;
  if (value !== null) {
    while (true) {
      const saved: boolean = value;
      if (second) { return saved; }
      value = null;
      second = true;
    }
  }
  return false;
}
```

SKJS accepts this reduction and it returns null on the second iteration. The
target is a failed loop-head/back-edge obligation or the stale read it justifies,
not an unsupported-`let` error. A counterpart that checks the value inside the
loop must verify, with supplied invariants on every incoming edge and no
fixed-point inference.

The storage decision is taken and implemented, in
[SourceExtraction.lean](lean/Verification/ExperimentState/SourceExtraction.lean).
An initialized, annotated `let` lowers to a private cell using the existing
heap semantics, one representation whether or not it is captured: the slot
holds the cell's identity, a source read is a read of the cell, and assignment
evaluates its right-hand side once, writes it, and yields the saved value, since
the calculus's write yields null. A closure therefore holds the cell's identity
and observes later writes, while `const saved = x` holds the value read and is
untouched by them. The annotation is the stable storage contract; the write
rule is the check that every assignment meets it, and the initializer is
checked against it too rather than admitting the declaration at a narrower
type. Storage is decided by the declaration and carried in an internal scope
binding, never in a diagnostic descriptor and never from a producer's point
claim, which describes contents. Every occurrence of the name lowers through
one resolution, so no site can take the identity for the value: the identity
escapes the frame only inside a closure's environment, never as something a
source expression produces.

Assigned function parameters use the same storage convention. The Lean lowering
scans the body and nested closures for assignments, then initializes a separate
private cell for each assigned parameter. It replaces only that parameter's
slot, preserving the order and values of all other inputs. The written parameter
annotation remains the storage contract; no producer claim chooses whether a
parameter is a location. A closure captures that location and a const captures
a snapshot, as for `let`. The function's public input contract is unchanged.

Nullish assignment to a local (`x ??= rhs`) uses the same private storage.
The parser records the operator; Lean reads once and dispatches on the saved
value's nullish tag. Only the nullish arm evaluates and writes `rhs`; the other
returns the saved value. Both arms establish the expression claim and, for
primitive results, an explicit heap postcondition at their join. This is a
checked obligation, not a new typing rule or an assumed refinement. The LHS
read, RHS, and whole expression each retain their producer claim. Closures use
the existing let/conditional/write terms. Property and computed assignment
targets remain outside this form: their receiver must be saved separately.

Ordinary producer claims for a mutable binding describe its current contents,
and are checked even at entries where the binding is unused. Claims implied
by the storage invariant become read obligations; narrower supported primitive
claims become heap observations checked on incoming edges. Writes, calls and
back edges use the existing heap-knowledge rules. A closure's entry claims must
follow from the stable invariant, not creation-time contents. Immutable snapshots
can retain a precise value after the original local changes.

Saved reads distinguish a mutable local's contents from fields of the object
it contains. A read-only guarded closure can retain either observation, including
nested guards on both. Field assertions describe the inner object, not the
private holder; graph entry assertions on such fields still require the inner
object's invariant when no stable inner-object slot is available. Effects and
escaping closures prevent the read-only snapshot optimization.

A number reaches all of this through the same interning path every other type
uses: wherever the table can grow, a type's numeric arms are interned rather
than refused, which is what lets a closure be typed `(): number => …` and a
`let` hold `number`. The source record path also interns numeric field
contracts. The older pure `SourceTypes.translate` helper and its exactness
lemmas remain limited to the fixed primitive labels; source extraction uses
the interning path for numeric types.

Current-content assertions have a finite syntax without requiring a finite
set of inhabitants. `HeapFacts.Atom` denotes null, undefined, Boolean singletons,
numeric singletons, or the whole number family. `Atom.holds` interprets these
predicates; `covers_sound` justifies singleton-to-number weakening. The existing
heap/value facts and read links use this one vocabulary. Writes establish it,
call effects invalidate heap facts, and immutable snapshots retain their facts.
A numeric equality test keeps an unknown broad-number outcome on both edges.
Claims outside this vocabulary still require invariant-based inclusion rather
than being dropped or widened to a different claim.

Guard shortcuts that refine an immutable slot never apply to a mutable cell's
identity: the condition tests the actual read. This is conservative for guarded
contents, and the loop-carried target above still needs further precision work.
The lowering is trusted code: Lean proves the resulting calculus program sound,
not that this translation preserves TypeScript execution. Regression tests pair
source executions with forged claims and independent certificate consumption to
exercise that boundary; they are not a semantic-preservation theorem.

The annotation may be omitted. The candidate contract is then the producer's
claim at the next statement entry in the same lexical block. That entry belongs
to this declaration, independently of the order of exported entries or names
reused in sibling blocks. If there is no such entry claim, extraction refuses
the inferred contract. It is supplied and then checked exactly as a written one
is — every assignment against it, and the initializer too — so an inferred
binding is not admitted at whatever its first value happened to be, and no
lifetime union is invented for it here.

A `let` without an initializer stays gated:
after the declaration executes its value is `undefined`, and definite
assignment must show a suitable write precedes each read, through branches and
captures. Shadowing stays gated with it.

**4. Captured mutable locals — #599, `L-STALE-READ` and `L-CAPT-EVOLVE`.** After
that storage decision, port the whole-local variants and
[the evolving-binding witness](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/evolving-capture-unchecked.md).
Test both a captured writer invalidating the caller and a captured reader whose
creation-time narrowing expires. Start with explicitly annotated primitive
bindings. An evolving `let x = null` needs a supplied storage contract covering
later writes; its initial value claim alone is not that contract. Add such producer
information or make its absence explicit, rather than inferring a lifetime union
or treating the initializer as a permanent invariant.

### Valuable later targets and the traps they introduce

| Target | Why keep it on the list | Why it follows the mutation targets |
| --- | --- | --- |
| **Incomparable function signatures are not disjoint — `L-INTER-BOT`.** [Witness](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/tfun-inter-incomparable-not-disjoint.md). | Directly exercises the positive calculus's function intersections. Begin with a calculus witness: one checked constant-null closure inhabits both a null-domain arrow and a Boolean-domain arrow. | Source integration needs richer callable claims and a sound identity/comparison story to reproduce the equality branch. Extensional arrow membership does not establish JavaScript function identity. Do not add intersection completeness or unrestricted arrow-result merging as a prerequisite. |
| **Numeric false disjointness — `L-LIT`, deep dive G.** [Witness family](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/beyond-precision-numeric-literals.md). | Distinct decimal spellings can denote the same binary64 value, making a claimed unreachable branch live. It tests runtime grounding independently of mutation. | The calculus now models numbers opaquely, and a literal's identity is the bit pattern of the double it denotes, with `-0` normalized, so distinct decimal spellings of one value are one singleton rather than distinct integers. Strict equality against a numeric singleton now filters finite singleton unions using Number::equal; a test on the broad number family is typed as a Boolean and both branches retained; arithmetic is the double operation yielding the family; truthiness remains absent. |
| **Callability/absence, getters and void.** `F-CABSENT`, `ACCESSOR-METHOD`, `L-SEQ`. | The corpus has concrete reachable-never and non-callable-call witnesses. | They require object-shape guarantees, accessor execution, or an explicit distinction between void as a typing convention and undefined as a value. Object parameters are assumed at their annotation as part of the interpreted caller contract, which is not the same as trusting a structural declaration to exclude accessors at runtime; do not treat void as a disjoint runtime tag. |
| **Inference-state and expansion failures.** `MR-1`, `C-FREEZE-CACHE`, `L-SUB-TSINST`, `E-EXPKEY`. | Wrong inferred types remain valid verifier targets even when their cause is a cache or substitution bug. | Select a concrete escaping wrong claim whose ground types fit the calculus. This pipeline should check that consequence, not model SKJS caches, rollback or its entire generic inference algorithm. Once a ground consequence is in reach, export the responsible subtype or expansion judgment with the snapshot in force at that judgment and check that operation's contract independently. Universal generic certification needs separate rules; checking one ground instance does not supply it. See [Semantic contracts for SKJS operations](#semantic-contracts-for-skjs-operations). |

### Completion criteria for every corpus target

Record the existing issue/ledger identity, corpus revision and reduced program.
Recheck SKJS acceptance and execute the reduction to establish the contradicting
value or stuck operation. Inspect the actual normal-mode export before extending
syntax; do not depend on `--keep-going`. Distinguish an unsupported type or missing
claim from failure of an actual typing/edge obligation. If a manual candidate is
needed, preserve the original, state every repair, and retain the false claim the
experiment is intended to challenge. Include an independently checked positive
counterpart and pin the expected negative obligation. New syntax or rules should
be justified by the next named target and reuse the existing semantic contracts
where possible. The corpus is also a regression source: a new spelling of #598
is useful coverage, but must not be counted as a newly discovered unsoundness.

## Chosen architecture

The intended path is:

![Architecture: source extraction and associated claims form a request; an untrusted producer supplies certificates, and the proved consumer checks both before establishing modeled safety.](diagrams/architecture.svg)

[Open the full-size diagram](diagrams/architecture.svg). The SVG is the editable
diagram source and renders without a Mermaid preview extension.

Green nodes are connected by Lean proofs. Amber nodes identify source/model
meaning that still requires review or preservation proofs. The producer and
SKJS are outside the soundness argument: their output must pass the consumer.
The direct request-to-consumer path is essential; certificates cannot substitute
a different program or a weaker set of requirements.

### Requirements, claims and evidence

These inputs have different roles:

- **Source annotations** are requirements: the program must meet them.
- **Type claims** propose expression types and environments at program points.
  They are checked facts, not trusted assumptions.
- **Proof evidence** justifies the required relations using the declarative
  rules. It cannot change the program, annotations or claims being checked.

At a merge or loop head, the entry environment is supplied. Each incoming edge
must independently justify it. There is no program-invariant fixed-point
analysis or requirement to compute a least upper bound. A target may forget
information, but every binding it requires must be justified by the source.

Expressions are checked under those entry environments. A successful check of a
node alone does not establish that its environment can hold: entry and incoming
edge obligations are essential. The graph checker enumerates the actual
program, including both branch destinations, so omitted evidence cannot hide an
edge obligation.

The source compiler now consumes `SourceClaims.Function`: candidates expressed
as calculus type labels or explicit decoding failures. `SkjsSourceClaims` is an
adapter into that interface. Source annotations remain separate requirements.
Direct callers use `extractNormalizedFn`; used labels are bounds checked against
the request's own type table. The strict
[independent source sidecar](SOURCE-CLAIMS.md) now exposes the same boundary
through the CLI, with source identity, site and label validation. Both input
paths reconstruct requests for the same proved evidence consumer. Arbitrary
graph documents and TypeScript comment input remain future steps of
[the independent claim interface](CLAIM-INTERFACE.md).

### Derivations define acceptance

The declarative subtype and program rules are the acceptance specification.
The semantic model justifies those rules; it is not an oracle that the producer
must decide. A useful missing relation should lead to a sound rule extension or
an explicit feature restriction, not an open-ended search for semantic
completeness.

The current producer performs bounded expression search over a finite type
vocabulary. Its subtype search proposes finite cyclic tables and arrow
certificates, which the consumer checks. This is search for derivations, not
inference of program-point invariants. Search strategy, fuel and hints affect
whether evidence is found, never the obligations for accepting it.

The producer may be incomplete or replaced entirely. Failure means unsupported
or unjustified within that search; it does not prove that no derivation exists.
The depth limit is not a work limit: failed searches for composite closure-write
claims can be expensive. Independent checking does not run this search.
The consumer must remain usable with evidence from any producer.

The same split applies to SKJS itself. Inference may propose solutions; it does
not authorize acceptance. [Semantic contracts for SKJS
operations](#semantic-contracts-for-skjs-operations) is the path from this
model to repairing SKJS's reasoning, without taking the current implementation
as the specification.

## Semantic contracts for SKJS operations

The pipeline currently checks SKJS's *conclusions*: program-point types and
invariants, translated into the calculus. That remains the source integration.
The stronger use of the model is to give SKJS's individual operations precise
semantic contracts, so a transformation is legitimate or unnecessary relative
to those contracts rather than relative to the current implementation.

Three similar-looking kinds have different meanings:

| Kind | Semantic obligation |
| --- | --- |
| Generic parameter `T` | The body must work for **every** admissible `T`. |
| Inference variable `?T` | The checker may **choose** a type satisfying the constraints. |
| Hidden type argument of an object | There **exists a fixed type**, but the checker cannot choose or change it. |

Confusing them is a source of unsoundness. `T extends boolean` establishes
`T ≤ boolean`; it does not establish `boolean ≤ T`. A generic function
returning `T` therefore cannot return `true` merely because `T` is bounded by
`boolean`: `T` might be `false`. Likewise, an object's hidden type argument
is not an inference variable for an expected type to solve.

The distinction also holds across time. A hidden witness must retain its
identity within its scope, without identifying the hidden arguments of
different runtime objects. That is the same identity issue as escaping
skolems, closures and loops.

### Contracts

1. **Substitution preserves meaning.** Substituting type arguments into syntax
   must mean the same thing as interpreting the original syntax under the
   corresponding type assignment. Capture avoidance, parameter identity and
   composition become correctness properties rather than implementation
   details.
2. **Expansion and normalization have explicit guarantees.** An exact
   expansion preserves denotation. An approximation must establish the
   appropriate inclusion direction. A cache must preserve that guarantee under
   the state in which its answer is reused.
3. **Successful subtyping establishes semantic inclusion.** Schematically,
   `Δ ⊢ A ≤ B` implies `⟦A⟧_η ⊆ ⟦B⟧_η` for every assignment `η` satisfying
   `Δ`. The interpretation retains the model's heap and world conditions.
   `extends` constraints contribute assumptions to `Δ`; conditional types
   would need their own computation rules in addition. This inclusion is
   already the proved meaning of the independent calculus's subtype rules
   ([`Sub.sound`](POSITIVE-TYPES.md)); the bridge asks the same of selected
   SKJS operations, without treating SKJS's `isSub` as the specification.
4. **Inference cannot invalidate previous checks.** Validating a judgment
   under substitution state `ρ` is insufficient if later growth changes what
   its types mean. The options are stable commitments, a justified
   preservation argument across state changes, or revalidation of affected
   obligations.

The last contract is already a theme of the
[mathematical audit](../docs/skjs-type-soundness.tex). That model
distinguishes inference guidance from validation ("Guidance vs. Validation")
and treats stale-state reads and caches as failures of judgment stability.
Those arguments are a starting specification. They are not Lean proofs of
SKJS.

### Repair architecture

Let inference propose solutions, then validate them against an immutable,
explicit representation. The inference machinery can remain heuristic, evolve
or eventually be replaced. Its success does not authorize acceptance by
itself. Optimizations and caches then have local obligations instead of
silently becoming part of the meaning of subtyping.

SKJS implementation progress against these contracts is tracked in
[docs/skjs-improvement.md](../docs/skjs-improvement.md). That file is not a
plan to make SKJS implement this pipeline.

Extraction-only recording of selected operations must preserve SKJS
acceptance, inference and diagnostics. A rejected safe program with an
independently checked derivation is a precise incompleteness target for
improving inference. Failure to find a derivation proves neither unsoundness
nor incompleteness.

### Progression

- **First, check ground consequences of existing bugs.** A generic-inference
  bug can produce an incorrect concrete claim that the current pipeline can
  already reject. No universal generic semantics is needed to expose that
  particular failure. This is already the policy for the inference-state and
  expansion targets above.
- **Next, audit individual operations.** Export selected subtype and expansion
  judgments together with the substitution snapshot that was in force at the
  judgment, or with types already closed at that point. Check those contracts
  independently. This locates a failure closer to its cause than a later
  program-point claim does. A first slice should use committed or fully
  substituted operands in the existing primitive, cell and arrow fragment, so
  contract 3 is checkable with the current consumer and contract 4 holds by
  construction for those exports. Live inference variables are not the
  starting representation.
- **Then add bounded, first-order polymorphism:** generic aliases, generic
  function bodies checked under rigid parameters, and explicit instantiation.
  Prove substitution and instantiation soundness before tackling conditional
  types, higher-rank polymorphism or parameter-changing recursion.

Checking several concrete instantiations remains regression testing; it does
not certify a generic body universally. The [established calculus
boundary](#types-and-recursion) leaves that explicit.

### Preferred next milestone

The next model-to-checker milestone is the operation-level bridge, followed
by a deliberately small generic fragment. The aim is a reference for
repairing SKJS's reasoning, not a commitment to formalizing the current
implementation wholesale.

The first slice of the operation-level bridge is implemented: SKJS exports
closed subtype and expansion judgments from a function body, serialized under
the substitution in force at the judgment. `--check-skjs-operations` translates
those that fit the existing primitive, cell and arrow fragment and checks them
with the current subtype consumer. Live inference variables are not the
representation; clones do not contribute; a failed search is unproved, not a
disproof. See [Request protocol](REQUEST-PROTOCOL.md#closed-operation-export).

The first-order generic fragment is implemented in the model, and the identity
scheme is connected through source extraction. Rigid parameters are labels
interpreted by an assignment `η`.
Substituting `A` for `T` on the identity alias and on `Ref T` is interpreting
the original syntax under `η[T ↦ ⟦A⟧]`. The identity function inhabits
`T → T` for every value-only family `T`.

A generic body is now checked under that assignment. `HasTy` is unchanged;
every constructor has a `meaningP` soundness lemma, including branches,
callables and union split. Branch and `typeof` tests require a non-parameter
scrutinee: an opaque `T` has no shape. `function id<T>(x: T): T { return x }`
is safe at `T → T` for every admissible `T`. Instantiating and applying
`id<boolean>(true)` is specializing that theorem, not a second typing rule.

`extends` is an assumption in `Δ`. `SubP` is inclusion for every `η`
satisfying `Δ`: `T extends boolean` derives `T ≤ boolean` and, independently,
`true ≤ boolean`. It does not derive `true ≤ T`. Transport of a checked
term along `SubP` is `sub_safeP`. See
[TypeParams.lean](lean/Verification/ExperimentState/TypeParams.lean).

Source extraction of `id<T>(x: T): T { return x }` is connected: the parser
admits distinct type parameters, SKJS exports each as a rigid `param`
atom, and the adapter checks that shape against the identity theorem.
First-order generic aliases are connected too: `type Id<T> = T` and
`type Box<T> = { value: T }` are the admitted schemes, SKJS exports a
one-argument named instantiation as an `alias` application, and the adapter
substitutes using `instantiate_param` / `instantiate_ref`.
`T extends boolean` is connected as `T ≤ boolean`:
`asBoolean<T extends boolean>(x: T): boolean { return x }` transports along
that inclusion. It does not justify `true ≤ T`. Bodies that copy `T` through
`const y: T = x; return y` and extra parameters are connected along `letE_safeP` and `var_safeP`.
The source adapter also admits `U extends T` when `T` is declared earlier,
retaining distinct rigid labels. `GenericBounds.follows_sound` proves every
successful finite upper-bound traversal derives `SubP`; `SubP.sound` supplies
semantic inclusion under assignments satisfying those bounds. Annotated copies
and returns use that traversal, including chains ending at boolean. Bounds
cannot be reversed, and a widened const keeps its annotated type. The parser
and consumer reject duplicate names, forward bounds and cycles independently.
SKJS captures each function's already-installed rigid declaration bindings.
An exact dependent clause match exports the declared parameter, retaining its
identity instead of choosing one of the clause's variables. Unrelated
intersections and additional narrowing remain refused. The generic source suite
checks dependent bounds using unedited SKJS exports; no candidate signatures are
needed. The snapshot also covers parameter occurrences in entries and expressions.
Generic statement entries and variable-expression claims are mandatory inputs,
not display-only annotations. Each source site must have exactly one claim;
extra sites and extra source bindings reject. Entry types must follow from the
incoming context under the declared bounds, expression types from the checked
entry, and binding/return contracts from that expression claim. The only excluded
entry name is SKJS's implicit unavailable `this`; an asserted type for it rejects.
Production and independent consumption both reconstruct and check these
obligations. Located failures print the bounds, named environment and required
inclusion, and the report points to the entry or expression. Valid weakening is
allowed. These generic checks still run directly rather than emitting a ground
graph or serialized per-site evidence; an empty graph bundle no longer skips
body-claim validation. Both producers support this fragment. Native SKJS claims
are imported into the same typed source sidecar as TS claims, before verification
or viewer collection. Unavailable types remain explicit at their sites; native
payloads and collection history are import provenance. There is one whole-file
producer/consumer implementation, in `SourceClaimJson`. The TS exporter
preserves compiler symbol identity as a function-scoped `{param: "T"}` source
claim; the neutral consumer checks it against the source binders and bounds.
This checks variable-copy bodies; generic callbacks, source call-site
instantiation, higher-rank and parameter-changing forms remain later work.

This is independent of the mutation and loop source-fragment targets above.
Those remain the next programs to cover with the existing stateful
foundation; they are not a prerequisite for exporting and checking SKJS
operations.

## Established calculus commitments

### Types and recursion

The type language is a finite graph of positive formulas over null, boolean,
invariant references and overloaded function types. Unions may occur at type
roots and recursive operands; reference clauses retain conjunctions of contracts.
Positive normalization preserves the full recursive interpretation without
unfolding cycles or allocating new graph labels.

Recursion is guarded. Interpretation uses budget-indexed families over
admissible stratified worlds, with a fixed point constructed by agreement at
finite observation levels. Guarded occurrences in function domains are allowed.
The construction does not require a monotone operator on unindexed sets of
values. Its definitions and proofs are in [SEMANTICS](SEMANTICS.md).

Finite regular recursion is the established boundary. Parameter-changing
recursive aliases are not covered merely because they use recursive syntax.
Generics, bounds and a surface `extends` language need their own interpretation
and typing rules. The intended path is the
[operation-level bridge, then a small first-order fragment](#semantic-contracts-for-skjs-operations),
not an implicit extension of the present type language.

### Mutable storage and functions

Every allocated location carries a stable invariant contract in the world.
Heap satisfaction connects that contract to its current contents. Admissibility
requires contracts to survive future allocations; suitable writes preserve heap
satisfaction. References are invariant views of storage, not covariant containers.

Functions are closed lambdas whose substituted bodies are safe in every
admissible future world and satisfying heap at smaller budgets. Application
spends the beta step before using that guarantee. This supports allocation and
closures over mutable cells, including calls after writes through another alias.

Stable storage guarantees and retained flow refinements are separate questions.
The invariant-cell model establishes the former. It does not establish a general
policy for retaining property observations across writes or calls. Forgetting a
refinement cannot justify a write that violates another alias's storage contract.

### Control flow and binding transfer

The graph machine evaluates an expression at each node, then returns, binds its
value, discards it, or branches. Three of the [six continuations](PROGRAM-TYPING.md#checked-control-flow-graphs)
branch: on a Boolean, on a Boolean it also binds, or on a shape test of the
returned value. The two binding forms are where refinement enters. A destination carries a label and
an optional explicit slot map. Maps select source bindings simultaneously: they
can reorder, drop bindings or retain aliases. They are executable program data,
not certificate hints. Each selected binding must have a checked subtype
relation to its target slot.

Bind maps act after pushing the expression result. Effect and branch maps act
on the incoming environment. Dispatch, expression evaluation and transfer take
explicit operational steps. Global safety covers cycles without graph unrolling
or a termination requirement.

Closures currently contain expression-language bodies, not graph-backed bodies.
A graph loop surrounding closure calls is supported; a loop inside a closure
body is not thereby expressible. General branch-environment refinement is also
outside the current program rules. Graph dispatch currently supplies Boolean
and tag observations to the common immutable-slot refinement rule. Expression
typing also supports known shape answers per overload.

### Rule boundaries justified by counterexamples

Two checked counterexamples in `ModelBoundaries.lean` remain relevant to the
chosen design:

- Unrestricted intersection of arrow results is unsound here. An allocating
  function can satisfy two arrows using different invariant choices for its
  fresh location; that does not imply a result satisfying both contracts in one
  world. The maintained combination rule has a proved conservative shape
  condition.
- Eventual incompatibility of nested reference contracts does not justify
  replacing their intersection with bottom at every finite budget. The indexed
  model has a checked counterexample to that proposed rule.

These constrain rules we might otherwise add. They do not require retaining
separator searches, alternative models or a semantic-completeness project.

## What is implemented and proved

| Layer | Current status |
| --- | --- |
| Stateful positive types | Recursive normalization preservation and declarative subtype soundness are proved. |
| Subtype evidence | The checker is sound and complete for the declarative rules. |
| Program evidence | Acceptance is equivalent to closed-program derivability for the stated rules; typing implies computation safety. |
| Point claims and slot maps | Checked incoming relations preserve semantic environments under the program's binding transfers. |
| Control-flow graphs | The checker covers actual nodes and edges; accepted graphs have no stuck execution and typed returns, including cycles. |
| In-memory producer | Builds evidence from fixed point annotations; successful output passes the consumer and preserves the exact requested claims. Search completeness is not claimed. |
| Serialized requests | Requests and evidence pass through a separate JSON consumer in the existing verifier binary. Acceptance yields decoded-request safety. |
| Source-facing integration | Primitive inputs, branches, local cells and bounded expression closures reach the stateful consumer. Primitive, cell-label and function-label translations have exact interpretation theorems; source compilation remains trusted. |

Certificate completeness means **every declarative derivation has accepted
finite evidence**. It does not mean every inclusion true in the semantic model
is derivable. Nor is there a completeness theorem for graph checking or for the
producer's search.

The stateful safety results are partial-correctness results, not termination
proofs. Returned values meet the declared result type at each positive remaining
budget in an admissible world satisfied by the final heap. The exact statements
and theorem names are in [PROGRAM-TYPING](PROGRAM-TYPING.md).

The maintained proofs use no `sorry` or project-specific axioms. Printed axiom
dependencies use Lean's standard `propext`, `Classical.choice` and `Quot.sound`.
This does not remove the need to review what the definitions and theorem
statements mean.

## Source association and claim validation

`--emit-skjs-type-claims` exports file entries containing function names and
spans, claimed signatures, expression types and statement-entry environments.
The adapter compares signatures with independently parsed source annotations.
Expression lookup uses full spans; environment lookup uses statement starts
because the parsers differ on trailing semicolons. Primitive claim decoding lives
in [Claim.lean](lean/Verification/ExperimentState/Claim.lean); cell and function
contracts have separate bounded decoders. This claim language is not a second
calculus or an executable source model.

Required unsupported types cause rejection. Extra unused producer data can remain
visible in reports without becoming verified facts. Positions associate claims
with syntax; they do not authorize edits to source or establish semantic truth.
Duplicate identities, missing required claims and mismatched source signatures
are checked independently of proof search.

The extractor resolves initialized bindings to slots and checks scope-dropping
edge mappings. Because it is the only pass that sees both sides, it also records
a **source map**: for every graph node, how to describe that node and each of its
context bindings in the words of the source. Source maps are explanatory, have no
decoder, and never reach a request or certificate; they are what lets a reader
speak about `cell` rather than a slot number. See
[Obligation diagnostics](OBLIGATION-DIAGNOSTICS.md#node-and-expression-obligations). Active-name shadowing is rejected. Statements after unconditional
`return`, `break` or `continue` are outside the fragment. The graph
consumer checks every node supplied to it, even unreachable ones; that theorem
does not by itself justify changing the source adapter's policy.

## Trust boundary

### What evidence checking removes from trust

Neither SKJS's inference nor the evidence producer must be sound. The consumer
checks their proposed facts and derivations against the actual calculus program
and requested annotations. Proved normalization and checking algorithms need
not be trusted independently of their proofs.

The independent semantics still needs review: what values and programs exist,
what execution does, what types mean, and what the safety theorem concludes.
A theorem about an evaluator that never progresses would offer little assurance.
Operational examples and negative tests complement proof by testing those
modeling choices; they do not replace proof.

### What remains assumed

- The independent parser faithfully represents the supported source text.
- Source and claim translation preserve intended control flow, lexical binding,
  annotations and type meaning. Scope association cannot be recovered merely
  by checking that two slots have compatible types.
- Decoding represents the submitted program, requirements and claims faithfully.
- The calculus's execution model agrees with the supported JavaScript behavior.
- Lean's kernel, compilation infrastructure and the executed checker are correct.

For the stateful in-memory interface, `accept` checks the exact requested entry
contexts and expression-result annotations against the certificate, then invokes
the graph checker. This closes substitution of a different request *within that
interface*. It does not prove source extraction or the meaning of external JSON.

The current source adapter accepts only null and boolean primitives. Numeric
and string examples are boundary tests, not certified successes. Adding these
primitives requires checking their semantics against JavaScript, including
numeric precision, NaN and signed zero; accepting their wire encoding alone
would not settle that obligation.

### Optional: prove source-to-graph preservation

Lean has access to the current source AST and its compiled graph. Translation
trust can therefore move into proofs; it is not inherently outside Lean's reach.

1. **Structural properties.** Prove successor validity, freshness and binding
   resolution under explicit source well-formedness assumptions. Include
   declarations after returns and reads before initialization. These properties
   constrain compilation but do not alone establish execution preservation.
2. **Semantic preservation.** Define execution for the supported source AST,
   including lexical scope, initialization errors, calls and control flow.
   Prove that compilation preserves observable execution, allowing different
   step counts. Combine this with graph safety to establish modeled source
   safety from accepted claims.

The second step moves trust from the compiler algorithm to the source semantics
and its agreement with JavaScript. Parser faithfulness and Lean's infrastructure
remain outside that theorem. This concerns today's supported language and its
compilation, not equivalence with an earlier implementation or a second pipeline.
Full TypeScript formalization is not a prerequisite.

## Source integration: current slice and next milestone

[SourceExtraction.lean](lean/Verification/ExperimentState/SourceExtraction.lean)
connects independently parsed source and actual SKJS exports to the stateful
consumer. It accepts primitive or bounded callable parameters, initialized `const` declarations,
nested boolean branches, block-bodied `while` loops and returns, with variables, null/undefined/boolean literals,
plain `{ value: e }` allocation, `.value` reads and `.value = e` assignments,
and the bounded local closures and calls described below. Every syntactic exit
path must reach an explicit return; loops may diverge.
It rejects active-name shadowing, calls to named top-level functions, statements after
an explicit return, and unsupported types. This is a coverage gate for the fragment, not the intended final dead-code policy.
The identity scheme `id<T>(x: T): T { return x }` is checked under a rigid
parameter and omitted from the graph request; the same path admits variable-copy
bodies with distinct parameters and directed dependent bounds. See [GenericSource.lean](lean/Verification/ExperimentState/GenericSource.lean).
`type Id<T> = T` and `type Box<T> = { value: T }` are expanded by substitution
before that check and before ground extraction. See
[GenericAlias.lean](lean/Verification/ExperimentState/GenericAlias.lean).
`T extends boolean` is an assumption in `Δ`; returning `x` at `boolean` is
transport along `SubP`. A generic body may copy `T` through annotated `const`
bindings and extra parameters, with bounds to boolean or an earlier parameter.
See [GenericSource.lean](lean/Verification/ExperimentState/GenericSource.lean).

[SourceTypes.lean](lean/Verification/ExperimentState/SourceTypes.lean) translates
null, undefined, boolean, their singleton types, unions and bottom exactly into
four primitive labels, and interns each compound type a program mentions, an
invariant reference, a conjunction of references or a callable signature, as one row
of the request's own type table. A label exists only because something used
it, and `label_meaning` proves a labelled clause means exactly that clause over
any table holding the row; a clause the table lacks has no label rather than a
smaller one, so undefined cannot be silently discarded from an operand. Lean
proves the translation preserves primitive membership. Singleton clause and typing rules have been added with soundness
proofs; no claim is widened from a singleton to boolean.

Undefined is supported in required cell fields, primitive callbacks, explicit
returns, strict comparisons and nullish coalescing. The
[undefined fixture](tests/stateful-source/undefined.ts) checks these together with
alias writes and supplied current-content observations. Statement-entry claims
remain complete local verification boundaries. `unknown` is semantic top and a
`void` result forgets its guarantee into it, as a distinct source atom; this
does not yet cover optional-property presence, omitted arguments or a bare
`return`. Runtime
bindings named `undefined` are rejected so the source compiler cannot confuse
a shadowed identifier with the primitive value.

The compiler resolves names to initialized local slots, newest first. Each source
expression gets its exact exported result claim and its statement's claimed entry
environment. A separate synthetic node checks the saved value against any source
annotation, or the function return requirement. Incoming edges must justify the
next supplied environment. The continuation after an `if` is compiled once;
both falling-through arms point to that same entry. Explicit slot maps discard
arm-local bindings, including when an arm is empty or contains a nested branch.
The condition is evaluated once; its exact expression claim must describe only
Booleans. Dispatch pushes the actual tested value and makes its singleton type
available to that edge. The producer
cannot replace these requirements.
The consumer reconstructs the requests from AST and claims before checking the
submitted certificates. Graph safety is proved; source evaluation order and
binding preservation remain part of the reviewed compiler boundary.

The result-binding branch rule and its environment-transfer theorem are proved
in [BranchRefinement.lean](lean/Verification/ExperimentState/BranchRefinement.lean),
with mathematical rules in [PROGRAM-TYPING](PROGRAM-TYPING.md#refinement-under-an-observed-outcome).
For `if (x)`, the source compiler maps `x` to the tested value on each edge.
Its true/false singleton can therefore justify SKJS's claimed refinement.
Untested bindings still require ordinary incoming subtype proofs. This does
not infer refinements for aliases, property reads or general predicates.

Boolean equality and tag outcomes use one observation contract: every value of
the incoming type satisfying the observation must belong to the supplied target
type (`ObservedSub`). One mapped-edge checker and environment theorem handle
both. The current tag check conservatively filters whole labels and checks a
subtype certificate; this algorithm may become more precise without changing
the contract or adding another edge rule. A test proves a valid mixed-label
refinement that this algorithm cannot yet check. Boolean and tag dispatch
supply observations from execution, never from producer assertions. No arbitrary predicate framework is introduced.

The protocol makes the source parameter types an explicit input contract.
The exporter’s parameter signature is checked for matching names, order and types.
A synthetic entry edge must justify the first supplied point claim from that
contract. Lean proves safety for any typed input environment, admissible world
and satisfying heap. Source parameter slots follow declaration order, with
locals pushed ahead of them. This certifies the function body. Local expression
closures use the existing lambda/application rules; graph-backed closure bodies
and external callers remain separate integration work.

The cell-contract boundary is implemented in
[CellClaims.lean](lean/Verification/ExperimentState/CellClaims.lean). SKJS exports
a bounded record with separate read/write types per field, optionality and
object-mode flags. Synthetic index markers are recorded separately from runtime
permissions; real indexes remain unsupported. The Lean gate requires at least one
required field, distinct field names, and equal read/write contracts per field
after lowering to the same graph table. Field names come from the program; none
is privileged. A mutable Boolean
field passes; a readonly Boolean field has `never` writes and fails this
particular invariant-cell gate. Readonly objects need a different capability
interface; this rejection does not mean they are unsafe.

Theorems preserve both primitive sides of an accepted contract and show that
the chosen reference label denotes exactly that invariant. This is not
an equivalence theorem for TypeScript records and calculus references. Record
annotations cannot distinguish data properties from accessors. Establishing
plain-data allocation is the source gate’s responsibility. The parser accepts
only an explicit single `value` data property, with no getters, setters, spreads
or computed keys. Parameters are assumed at their source annotation, as part
of the caller contract, whatever their type: `RequestJson.verify_safe`
quantifies over every environment, world and heap meeting the input types. A
record parameter is therefore a reference to a location whose fields hold the
stated types, used by the same read and write rules as an allocated record;
two such references may alias, and the heap rules are stated over locations,
so nothing assumes they do not. That a JavaScript value conforming to a
structural annotation is such a plain data object, rather than an accessor or
proxy, is part of how the annotation is interpreted, exactly as a function
type is interpreted as a function respecting its contract. The interpretation
is the same trust boundary for both; it is not established by the annotation. Callable arguments can expose captured cells to an invocation; the
semantic arrow guarantee must therefore hold across admissible future heaps,
including callback effects. A producer claim that contradicts the annotation
is refused before proof search. This does not admit record-valued parameters
or establish contracts for unchecked JavaScript callers.

Object branches are exported faithfully as separate atoms in the existing union
format. [CellUnion.lean](lean/Verification/ExperimentState/CellUnion.lean) validates
all record arms before allowing a redundant arm to be absorbed by an **existing
invariant arm**. No malformed arm or unsupported field type is dropped.

Absorption widens the read requirement only at an unchanged storage invariant;
all surviving arms must be invariant contracts. The exact schema law and its
scope are in [Source claims](SOURCE-CLAIMS.md#record-alternative-absorption).
It does not give mutable observations a lifetime guarantee or prove equivalence
with SKJS's internal object semantics. Standalone observations follow the
[current-content integration plan](#current-content-assertions).

Fresh object literals carry synthetic indexes and inference-variable field
bounds internally. Export records the former and reads the latter from the
function's substitution snapshot, without changing inference. Mixed instance
and concrete-clause unions are serialized disjunct by disjunct under that same
snapshot, preserving every arm and removing only identical serialized atoms.
Only bound variables without constraints are followed, with bounded recursion;
unresolved or recursive cases remain unsupported. Tests check actual allocation
expression claims at Boolean and singleton contracts, contextual field growth,
and preservation of both aliases' contracts after a write. This export mapping
is explicit but is not a proved correspondence with SKJS's internal semantics.

Cell programs now pass through source extraction, certificate production and
independent consumption. [Fragment.lean](lean/Verification/ExperimentState/Fragment.lean)
decodes the source AST and routes record types through the contract gate. Every nested expression retains
its own supplied claim. Expression lowering saves intermediate values in
anonymous slots and evaluates the receiver before the RHS. A write uses the
existing calculus rule, then returns the saved RHS to match JavaScript assignment
semantics; temporary slots are discarded by explicit edge maps. An execution
regression checks the extracted alias-assignment graph's heap and result.

Closure contracts are decoded by
[Fragment.lean](lean/Verification/ExperimentState/Fragment.lean).
`callableType` checks ordered required-parameter signature shapes and recursively lowers primitive
and callable arguments and results, including every union and overload arm.
Bodies compose literals, variables, cell allocation, reads, assignments and
calls, including nested expression arrows.
An internal expression claim can differ from the declared result: both are
checked independently.

[ExpressionClaims.lean](lean/Verification/ExperimentState/ExpressionClaims.lean)
checks supplemental sequents for every closure-body expression, using its exact
lexical context, lowered term and supplied type. Source annotations produce
additional result obligations. The source consumer reconstructs this ordered
list, requires exactly one proof per entry, and checks each using the existing
program typing rules. `checkRequests_obligations` proves those sequents derivable;
the whole-program certificate separately supplies execution safety. These
supplemental proofs do not establish source semantic preservation: attaching
the right terms and contexts remains part of the trusted compiler.

The source closure becomes an ordinary lambda over the captured environment.
Its parameter occupies slot zero; captured bindings shift by one. Calls evaluate
the callee and argument once in that order. The existing lambda and application
rules establish safety, including future heaps after alias writes. No capture
analysis, new store model or additional semantic axiom is introduced. Real-export
tests cover capture of older slots, calls after alias writes, returned
closures, allocation and assignment inside closures, and narrower body claims.
Checked execution traces, tied to extracted graphs by equality regressions,
verify both an alias write followed by a captured read and a write inside a
closure that returns its RHS. Corrupt body, receiver, signature
and call claims are rejected by production and independent consumption.

Single-return blocks (`{ return e; }`) also use ordinary lambda terms. Their
return statement's supplied environment $H$ is checked against the captured
context and parameter $\Gamma$: for each slot $i$ with type $H_i$, supplemental
evidence must derive $\Gamma \vdash_G \operatorname{var}(i) : H_i$.
The return expression is then checked under $H$.
This checks unused claimed bindings too, and permits justified weakening.
The wrapper introduces no execution step; a graph-equality regression ties the
block form to the existing captured-read execution trace.

A closure null/undefined guard on a plain `cell.value` read may retain its
observation within branches containing only reads, primitive operations and
local consts. Extraction saves the tested read in an administrative let, refines
that immutable slot with existing tag rules, and reuses it for reads of the
same named cell. Calls, writes, allocations and nested closures anywhere in
either branch disable this lowering. Thus no observation crosses an effect or
escapes into a later invocation. Source heap assertions are checked against the
saved slot; absent such a slot, the original persistent-contract obligation
remains. Every supplied expression claim is still checked, while stronger
saved-read evidence may establish the enclosing return contract. This lowering
uses the existing term rules and adds no axioms; its correspondence with source
reads is part of the trusted adapter, not a proved JavaScript equivalence.
The repaired and stale forms this lowering distinguishes are
`captured-read-stability.ts` in the corpus, reported by `make verify-census`
rather than asserted by a suite.

Straight-line blocks also support initialized `const` declarations and expression
statements before the final return. Each statement entry uses the same checked
environment obligations. A declaration may list several bindings: the producers
state one entry for the statement and none between its declarators, so the
lowering binds them left to right under that entry, each initializer compiled in
the scope the earlier bindings extend, with the same per-binding annotation,
allocation and storage-contract obligations as a single declaration. An
unannotated `let` in a list takes its contract from the entry that follows the
whole statement, the first place every binding of the list stands in scope.
Inside a closure body a list stays gated: each lowered binding there is an
entry of its own, and the producers state none for the later declarators.

A type assertion (`e as T`, `e satisfies T`, `e!`) lowers to a node returning
its operand unchanged, typed at the assertion's own claim, which the node
proves from the operand like any other claim. `T` is recorded as an
obligation that the operand meets it. Nothing decides that the assertion is
true: a downcast with nothing known of the operand is refused, so an
assertion never establishes what a guard would.

A `const` object pattern (`const { field: name = default, … } = init`) is
lowered under the same one entry. The initializer is evaluated once and held
in an anonymous slot below the bindings; each property is read from it in
pattern order at the field type the record contract names. A default is
compiled only on the arm where that read is undefined: the read dispatches on
the undefined tag, the defined slice is one arm, the default's claimed value
the other, and both join at a node typed by their union, which each incoming
edge must establish. A property without a default binds its read. The
producers claim the initializer and the defaults, not the reads; the entry
after the statement states every binding, and the anonymous slot is dropped
before it. Nested and rest elements, `let` patterns, patterns beside other
declarators and patterns in closure bodies stay gated. Local annotations are separate obligations; bindings
retain the initializer's claimed precision. Sequential composition uses the
existing let rule, with one occurrence of the continuation. Effect results occupy
anonymous slots, preserved at their established types across subsequent named
statement environments. An execution regression checks a saved local, a write,
and a final read across these slots.

Source extraction now retains an untrusted proof recipe for each closure
expression and administrative let. The initializer's claim fixes a source let's
intermediate type. `DirectProof.render` follows that structure, adapting variable
leaves to the actual context through explicit subtype coercions. It does not
search alternative intermediate types or import the recipe's claimed context as
an assumption. Subtype obligations still use the ordinary subtype producer.

Supplemental obligations are proved first. Exact matching root proofs are reused
when producing the graph certificate; the ordinary consumer checks them again.
Recipes do not appear in the wire protocol or change the calculus's rules.
Raw calculus requests retain the general search producer. Measurements and
reproduction instructions are in [the direct-proof benchmark](benchmarks/direct-proof.md).
The term calculus also has a proved ordinary Boolean conditional rule, including
effectful conditions and checks of both arms against a supplied result type.
The separate `ifBoolVar` rule refines the directly tested immutable slot to its
Boolean singleton in each arm. Source closure blocks now support terminal
`if/else`, including nesting, where both arms return. Each statement entry still
requires evidence for every supplied binding; the enclosing result annotation
supplies the common arm type. No join is computed and no continuation is duplicated.
Closure branches whose two arms fall through now use the existing conditional
and let rules: each arm finishes with an administrative null, then one shared
continuation executes. Branch locals stay inside the arm's lets. The shared
continuation has the pre-branch immutable bindings and stable cell contracts;
its supplied entry environment must follow from those types. No branch-specific
refinement is retained. This is a sufficient, deliberately conservative join
check, not a computation of the strongest common type. Empty arms and nested
fall-through branches use the same construction. An early-return branch is also supported when one arm returns on every path
and the other contains no returns. The continuation occurs only in the surviving
arm, after a scoped sequence that drops that arm's locals. It may use the
surviving arm's checked immutable-variable refinement. Successive early-return
tests compose without copying the continuation. More general partially returning
nested arms and loops inside closures remain gated; they need a broader
control-flow translation or call/body interface. Binding identities must become
explicit before supporting hidden, shadowed bindings. Testing a mutable
field may make SKJS export unequal read/write types in an arm. Those claims are
still rejected by the invariant-cell decoder; immutable-slot refinement does
not establish retained heap refinements. Loops in top-level function bodies now
use the graph translation described below; closure loops remain unconnected.

### Current-content assertions

The design keeps persistent storage contracts and current heap facts separate.
`{ value: boolean = true }` records a Boolean storage invariant and currently true
contents. Observations are duplicable facts, not ownership permissions; they
neither narrow the world's invariant nor confer write authority.
[Semantics](SEMANTICS.md#current-content-assertions-and-postconditions) defines their
meaning, including heap satisfaction and the budget-zero boundary.
[Program typing](PROGRAM-TYPING.md#current-content-rules-semantic-layer) gives the
proved operation rules, entailment check and mathematical statements.

**Implemented:** semantic operation rules, finite heap/value facts and alias links,
checked expression postconditions and graph-edge entailment, and source consumption
through both raw SKJS claims and [sidecars](SOURCE-CLAIMS.md#current-content-assertions).
Every statement entry is an exact local interface: its supplied ordinary types
and current observations are the whole starting context. Extra derived heap/value
facts and links are forgotten there, even on single-predecessor paths, except
the distinct-location links the extractor states at every entry: a private
cell is a fresh allocation, so its location differs from every field of every
record-typed binding in scope, and the entry restates that timeless fact. The
consumer enforces this independently of the producer. Expression-result claims
are checked local obligations within a statement, where effect rules can derive
postconditions. Loop heads use supplied interfaces; every backedge must establish
them. No loop invariant is inferred.

A source ternary branches in the graph like an `if` statement, so an effect in
its condition or an arm is a node with its own knowledge. Element access reads
or writes the field the key's claimed string singleton names, after the
receiver and before any right side, and the key keeps its own obligation.
Writes establish new contents for recorded aliases, keep facts about cells a
distinct-location link separates from the written one, and discard other heap
facts; two parameters carry no such link, so a write through one forgets what
was known about the other. Ordinary calls discard heap observations and read
links. Immutable values and
slot equalities survive. Boolean guards refine current cells through checked
read links, including links carried through receiver temporaries; a strict
comparison does so when the other operand's claimed type is a singleton and
the operand is effect-free, a literal, a name or a field read, never a call. Ordinary
closure proofs require a supplied observation to follow uniformly from the
storage invariant; they cannot retain temporary facts from closure creation.
[Program typing](PROGRAM-TYPING.md#source-observation-checkpoints) owns the precise
checkpoint obligations and this conservative closure rule.

The [write-then-read witness](tests/skjs-incomplete/README.md) has a model proof
and an accepted source certificate after explicitly supplying a current-true
observation at the return entry. Its original broad entry claim does not verify.
Conversion preserves SKJS's claims; repairs are separate candidates.

The source claim language currently has no slot-equality or read-link assertion.
Those links are therefore local to a statement. Carrying them across statements
in a future fragment requires an explicit claim format and checked incoming
obligations, rather than restoring hidden cross-statement propagation.

Three constraints govern later precision improvements. Possible aliases cannot
be framed merely because their variable names differ. An immutable snapshot
survives mutation, but its former equality with a cell's contents does not. A
lambda cannot inherit a creation-time observation as a guarantee for every future
invocation. Selective retention needs proved noninterference or postconditions.
Receiver and right-hand-side effects must precede a write's new fact; getters and
concurrent interference remain outside the plain-data model.

#### Committed integration milestone

This milestone is complete.
The completion target is the original, unedited exports for `staleCapturedCell`,
`staleCompound` and `staleFlip`, together with positive write/read and snapshot
controls. Additional standalone semantic proofs or a renamed limitation message
do not complete this milestone.

The three milestones are:

1. **Graph evidence and soundness — implemented.** Separate cell/value facts,
   checked effects, read/equality links and edge entailment belong to the maintained
   graph checker. External entry facts must be justified. Graph safety is proved.
2. **Source consumption and evidence production — implemented.** Both adapters
   retain the invariant and current predicate. Source checkpoints bind observations
   to entries/results; the consumer enforces exact statement-entry interfaces and
   checks every incoming edge. Tests cover allocation, writes, guarded reads,
   merges, backedges, empty predicates and changed claims. Ordinary signatures
   retain their existing meaning. Closure observations require uniform invariant
   justification, pending graph-backed closure bodies.
3. **Original-witness diagnosis — implemented; checker witnesses since repaired.**
   The original exports exposed stale heap observations after writes and calls.
   SKJS now rejects all three singleton returns, so their partial exports no
   longer carry the old stale assertions. The obsolete failing-edge audit has
   been retired. [The current audit](tests/refinement-witnesses.mts) requires
   rejection and verifies fresh producer claims for
   [three structurally matched controls](tests/refinement-controls.ts), which
   remove only the invalidating operation. Runtime counterexamples and immutable
   snapshot controls remain tested. `writeRefinedRead` still needs an explicit
   current-true return-entry claim; its broad claim is insufficient.

The audit exposed an earlier precision loss hidden behind the first reported
failure: null tests discarded observations before the valid loop-body entry.
The existing pure-effect rule now frames heap facts through tests and pure
conditionals, backed by a reduction-preservation proof. Negated conditions swap
successors while checking the negation's own claim separately, preserving the
operand's current-read link. These are general guard mechanisms, not exceptions
for the witnesses. [Program typing](PROGRAM-TYPING.md#checked-expression-postconditions)
owns the rule and proof details.

A failed proof search remains an unproved obligation, not a semantic disproof.
Runtime witnesses independently establish the three unsoundness examples.

### Source while loops: supplied head claims and checked back edges

A `while` statement has a stable head label with its supplied entry environment.
The compiler reserves that label, compiles the body with a back-edge continuation,
and connects the head to evaluation of the condition. The completed graph is
then checked independently. An administrative null/effect node anchors the head;
it makes no source-level state change. The condition's expression graph executes
on every visit, including calls and effects, rather than retaining the previous
Boolean result.

The true edge enters the body and the false edge reaches the surrounding
continuation. Falling out of the body drops its local slots before returning to
the head. Both the initial incoming edge and every back edge must justify the
same supplied invariant. Direct immutable-variable tests use the existing
checked singleton transfer; mutable-field refinements acquire no new lifetime.
No invariant inference, type join, semantic rule or certificate format is added.

Nested loops, empty bodies and early returns are supported in top-level function
bodies. Unlabeled `break` and `continue` now have explicit checked transfers.
Labels, other loop forms, non-block bodies and loops inside closures remain gated. Even a syntactically always-true loop currently needs an
explicit continuation for its false edge. Acceptance is safety, not termination:
a well-typed loop may run forever.

The real SKJS fixture `tests/stateful-source/loops.ts` covers zero iterations,
nested early returns, and a finite loop whose condition calls a captured-cell
reader and whose body writes through a local alias. `WhileSourceTests.lean`
checks the extracted graph and proves the finite execution trace, including
repeated condition evaluation, the alias write, local-slot removal and return of
false. Integration tests reject missing head claims, unjustified narrowing,
missing back-edge evidence, escaped body locals and reused evidence for changed
bodies. Runtime samples agree on the terminating examples. These bounded checks
do not constitute a general source-to-graph preservation theorem.

### Break and continue: scoped transfer targets

Each nested loop supplies its own pair of destinations: `continue` targets that
loop's head, and `break` targets its exit continuation. Compiling a nested loop's
following statements restores the enclosing loop's targets. Neither transfer can
cross a closure boundary. Both are ordinary null/effect graph nodes: their
supplied statement environments are checked on entry, and their mapped outgoing
edges must justify the destination's supplied environment. The slot map drops
locals introduced inside the loop or branch; it does not assume destination
claims or retain an obsolete mutable-field refinement.

Already-known immutable Boolean singleton facts are preserved when forming a
branch map, rather than overwritten with an opposite-branch witness. This avoids
unnecessary rejection on impossible edges and uses existing transfer rules.
Unlabeled transfers are supported; labels, transfers outside a loop, and statements
after an unconditional transfer remain gated in the fragment.

The real `loop-transfers.ts` fixture checks writes before break/continue,
conditional transfers, and the nearest target in nested loops. Negative tests
remove transfer environments or outgoing evidence, give a false exit claim, and
try to escape a body local. `LoopTransferTests.lean` checks the extracted graphs
and proves two operational traces: an inner break reaches the outer body's return,
and continue drops a local alias before reevaluating a captured-cell condition.
These proofs use the existing machine and safety rules; no new calculus form or
certificate constructor is introduced.

### Shared local continuations: checked construction, source gate unchanged

`ContinuationSharing.lean` establishes the next construction using existing
lambda, let and application rules. Define a continuation once as a local
function, then call it from each surviving path of a partially returning branch.
`share_typed` derives the typing rule without extending the calculus or evidence
format. Direct certificate construction and serialized consumption both check.
Execution proofs distinguish early return, resume after writing a captured cell,
and resume without writing. The continuation observes the heap when called.

This is not yet a source translation. A null-argument continuation captures the
pre-branch immutable context and stable cell contracts. It cannot assume later
refinements merely because its call sites establish them. To support supplied
join claims stronger than that captured context, pass the relevant values at
checked types or provide an explicit continuation-entry interface. That is the
next integration decision; duplicating the continuation or assuming its claims
at definition time would bypass it.

The explicit-argument case is now checked too. `passed_refinement_paths` uses
one continuation of type `false → boolean`, defined before the branches. Two
surviving paths prove that their argument is false; the continuation can use its
parameter at that type. Passing the original unrefined Boolean or a different
Boolean slot is rejected. This needs an additional internal arrow label, not a
new semantic type constructor. Generalizing to several supplied entry bindings
still needs a chosen argument layout and checked binding transfer in source
lowering. The current source gates remain unchanged.

### Set-valued clause covering

Covering matches one source clause against one *single* target clause. A source
clause can be contained in the union of several target clauses without being
contained in any one of them, and no rule sees that.

The `bool` instance of this is closed. `bool` is the only clause of the language
whose inhabitants are a finite set that is not already a singleton, so it is the
only one that decomposes syntactically, and splitting a source `bool` into the
pair of singletons before matching keeps `Covers` clause-to-clause while letting
one source clause be discharged by several target clauses. The rule is specified
in [POSITIVE-TYPES.md](POSITIVE-TYPES.md). SKJS gets the same answer by
normalising `bool` to `true | false` before comparing, and does so *before it
exports claims*, so no source file can carry the distinction: the guards beside
the rule are its only possible coverage.

What remains open is the general shape. Two parts of it are known and neither
yields to a normalisation:

- An arrow clause against a union of arrow clauses, or a reference clause whose
  covering target varies by world. Closing these needs a genuinely set-valued
  covering relation, with a semantic argument per constructor. That changes the
  arity of `Covers` and re-threads `Covers.sound`, `checkClause`, its
  monotonicity and completeness lemmas, and the `Arrow` machinery.
- `Arrow.union`, whose rule is
  $\mathit{Arrow}\,L\,a\,d\to\mathit{Arrow}\,L\,b\,d\to\mathit{Arrow}\,L\,(a{+}{+}b)\,d$,
  decomposes an arrow domain by *label list*. A `bool` domain that must be
  covered by different arrows of an intersection therefore stays out of reach
  even after the split, because `bool` is a single label whose decomposition is
  into clauses rather than labels. The witness is
  $((\mathsf{true}\to\mathsf{null})\land(\mathsf{false}\to\mathsf{null}))\le
  (\mathsf{bool}\to\mathsf{null})$.

Nothing currently exercises either part, so there is no witness pressing for the
work; it is recorded so the `bool` repair is not mistaken for a general one.

### Optional: a vacuity escape for reference conjunctions

`Ref null ∧ Ref bool ≤ Ref (null ∨ bool)` is true in the model and not
derivable. A reference clause is a conjunction of contracts a single location
must meet invariantly, so contradictory operands make the source empty from
budget 1 upward, and an empty type is below everything. At budget 0 all
reference types coincide, so the inclusion holds at every budget. `Covers`'s
reference rule asks that each target operand be matched invariantly by some
source operand and has no escape for a vacuously empty source — exactly the
escape `Arrow.empty` provides on the arrow side. SKJS accepts these.

Incompleteness only, in the safe direction, and nothing in the corpus needs it.
Worth doing if the reference rule is being touched anyway.

### Optional: let the producer nest `combine`

`CertificateProducer.arrowSearch` builds arrow meets only as
`combine(.source p, .source q)`, never a `combine` whose child is itself a
`combine`. A three-way meet needing the nested shape is derivable by `Arrow` and
unreachable by the search: `--produce-stateful` rejects
$(\mathsf{null}\to\mathsf{null}\lor F)\land(\mathsf{null}\to\mathsf{null}\lor R)
\land(\mathsf{null}\to F\lor R)\le(\mathsf{null}\to\bot)$ at fuel 20000,
while `--check-stateful` accepts a hand-built certificate for the identical
request.

Nothing about the rules is wrong and nothing unsound follows; the checker is the
trusted component and behaves correctly. The consequence is methodological and
applies to every measurement made with the producer: a `reject:` means *no
derivation was found*, not *no derivation exists*, so a rejection is evidence
about the rules only once the shape needed has been ruled out by hand.

## Later feature gates

Extend coverage in response to concrete programs or unjustified claims. Each
extension should establish its rules and a positive/negative integration pair.
The soundness ledger can supply targets, but its categories are not semantic
assumptions and historical coverage counts are not an implementation plan.

| Feature | Remaining obligation |
| --- | --- |
| Flow refinement across loops and calls | State which observations survive writes and calls, and prove branch/refinement transfer rules. Stable cell contracts alone do not supply these facts. |
| Mutable structural objects | Specify field presence, width, aliasing and allowed mutation; extend beyond the current invariant cells and export their types. |
| More primitives and operators | Numbers are admitted as opaque values with singleton literal types, in closure signatures and as the storage contract of a mutable local; finite singleton comparisons are supported, and a comparison on the broad family branches both ways; arithmetic on numbers is the IEEE-754 double operation yielding the number family, with compound assignments, increments and logical assignments to fields and elements evaluating their target once, the Boolean logical forms needing a Boolean target; strings are admitted on the same terms, opaque with literal singletons and equality against a literal; concatenation, general equality and truthiness are not, and each needs its runtime behavior defined and agreement validated. Numeric current-content predicates now cover both singletons and the number family, with checked transfer across graph edges. |
| Graph-backed closure bodies | Extend the call/body interface if source functions require graph control flow internally; surrounding graph loops are insufficient. |
| Generics and bounds | The model slice is in [TypeParams.lean](lean/Verification/ExperimentState/TypeParams.lean). Source extraction of identity, `T extends boolean`, `const y: T = x`, and extra `T` parameters is in [GenericSource.lean](lean/Verification/ExperimentState/GenericSource.lean). Source extraction of `type Id<T> = T` and `type Box<T> = { value: T }` is in [GenericAlias.lean](lean/Verification/ExperimentState/GenericAlias.lean). Distinct parameters and dependent upper-bound chains in variable-copy bodies are checked using [GenericBounds.lean](lean/Verification/ExperimentState/GenericBounds.lean). Remaining: generic callbacks and source call-site instantiation, conditional types, higher-rank polymorphism or parameter-changing recursion. Generic parameters, inference variables and hidden object type arguments are not interchangeable. Checking concrete instantiations remains regression testing, not universal certification of a generic body. |
| Difference and negation | Supply sound rules or approximations: pointwise complement need not preserve admissibility. They do not follow from positive normalization. |
| Exceptions | Model abrupt completion, state at raising, and pending returns/exceptions through `finally`; ordinary graph edges alone are insufficient. |

For example, `L-LOOP-CARRIED` remains a useful integration target: a write on a
back edge must not preserve a stale narrowing at the loop head. A corrected
counterpart should verify. Reaching that target requires the chosen source
syntax, usable claims and a refinement policy, not another graph representation.
Likewise, stale captured reads and alias writes should be tested against the
established storage invariants and any newly proposed refinement rules.

## Validation and success criteria

`lake build` in `verification/lean` checks the maintained Lean developments and
regressions. Producer tests cover mapped binding transfers, cyclic control flow,
overload derivations and recursive references, with corrupted requests and
evidence rejected. The mapped captured-cell example has both an automatically
accepted certificate and an operational trace returning the changed boolean.

For the source pipeline, `make verify` exercises real exports, altered claims,
source identity checks, evidence corruption, partial collections and the reader.
[Boundary examples](tests/unsupported) must reject for an expected limitation;
they are not evidence that the verifier can analyze the unsupported feature.
The numeric-precision fixture remains a future target, with no current claim of
catching its unsound narrowing. Operational Lean examples check modeled behavior;
there is no standing test establishing exporter faithfulness to SKJS internals.

Use Lean checks for Lean development and pipeline checks for extraction or
certificate integration. The repository-wide SKJS tests concern changes to SKJS
itself; they are not evidence for an otherwise unchanged Lean model.

The eventual user-facing command must report certified success only after the
consumer accepts. `--emit-skjs-type-claims` currently emits claims without making
that guarantee. `make verify` remains the experiment's source-facing command.

### Callable integration

The existing source adapter, certificate producer, independent consumer and
reports support recursively callable arguments and results, nullable callable
unions, returned closures and captured-cell mutation. This establishes integration
of the bounded callable model with the existing pipeline. The
[protocol](REQUEST-PROTOCOL.md#expression-closures-and-calls) owns the signature
encoding and restrictions; the [Callables coverage map](tests/callables/README.md)
owns examples, adversarial checks and runtime observations. Arrow-row interpretation
is characterized by `SourceTypes.arrow_exact`; recursive source decoding and
extraction remain reviewed boundaries.

Graph-backed closure loops, multiple/optional/rest arguments, `this`, generics,
function properties and identity comparisons remain separate obligations.
Additional tests should isolate a new obligation or a credible suspected defect.
Exact executions of extracted Lean programs are deferred unless a concrete
discrepancy warrants investigation; checked Boolean results and JavaScript
witnesses do not establish TypeScript-to-calculus execution equivalence.

Source-mode search uses labels in the function's request and required-expression
sequents, plus primitive labels. Vocabulary construction includes their operand
types. This is a search restriction, not a restriction on consumer checking or
a completeness claim. A request's table holds only what its file mentions, but
enumerating every unused arrow at each subtype query was already expensive at
that size; a larger file must not silently expand every local search problem.

Zero-argument thunks use native empty argument lists and zero-parameter
descriptors. Their source pipeline checks creation, delayed captured reads,
stored replacements, and invocation through both producers.

The [argument preparation interface](SEMANTICS.md#argument-list-preparation)
now separates callee evaluation, left-to-right argument evaluation and readiness
for invocation. Its singleton case agrees with existing unary congruence rules.
`tests/callables/arity.ts` fixes the required source evaluation order with a
JavaScript witness and remains an explicitly unsupported source fixture.
Parameter binding now preserves declaration order and captures, pads missing
actuals with undefined, and discards extra values only after preparation. The
current unary beta step uses the shared binder. List-based invocation contracts
now distinguish declared parameter count from each overload's actual argument
count; the existing unary code judgment specializes them. Dispatch now connects
ready frames to the stored code and its safety contract, and preparation plus
dispatch is proved equivalent to the maintained unary application step. The runtime descriptor now carries its parameter count, and
scope, substitution,
coherence and beta use it. Unary semantic arrows constrain the supplied actual
independently of that count. List-signature callable types now lift those code
contracts to values, with dispatch safety, admissibility and guarded congruence;
the existing unary type reuses the general proofs through singleton equivalence.
Application syntax now uses a native argument list, with the old unary constructor
replaced by singleton notation. All binding and syntax-validation traversals cover
the full list. Ready native calls now dispatch arbitrary argument lists, and
`call_elim` proves their safety from list-signature membership; unary application
uses that general rule. Native operand reduction now handles any argument count:
callee first, then the leftmost unfinished actual. Its transitions are proved
equivalent to the preparation/dispatch interface, deterministic, and coherent.
Compositional call safety now covers effectful callees and argument lists; both
application typing proofs use it, preserving saved values across effects.
Graph signatures now store ordered domain lists. Their normalization and
subtyping use native callable semantics directly; the unary graph adapters and
separate unary coverage rules have been retired. Subtype search can split a union
at any parameter position. Creation typing, its evidence checker, and the
producer accept native parameter counts, requiring every overload to match the
descriptor's arity and placing all parameters before captured bindings.
The JSON protocol, source claim producers, and report rendering use the same
list-shaped signatures. A three-parameter creation/widening example goes through
production and JSON consumption; a mismatched descriptor arity is rejected.
Application typing, evidence checking, and proof search now accept full argument
lists, including zero arguments. Evidence preserves operand order and requires
one premise per actual; search requires an exact signature argument count.
Pipeline checks cover native calls and a callable cell written by one operand
and read by the next, as well as omitted, extra, and reordered operands.
Source function types now preserve all required parameters through annotations,
SKJS claim decoding, the TypeScript claim producer, and the report editor.
A two-argument function crosses a mutable cell and escapes with a narrower first
domain; forged widening or omission of its second domain fails.
Source calls and lambdas now lower native argument and parameter lists.
The callee is saved first, then actuals left to right; temporary-slot maps retain
the original bindings. Lambda bodies put parameters in source order before
captures. Union-callee elimination saves all operands before splitting the
callee's type. Zero-argument calls and closures use empty lists and arity zero;
the synthetic undefined argument and anonymous parameter have been retired.
The source suite covers effect order, a returned closure capturing the second
parameter, and a multi-argument union callee. Calls require an exact signature
argument count; optional/rest parameters and spread actuals remain excluded.

### Next callable and object milestones

Required record fields can store callbacks using the existing reference and
arrow rules. The source tests distinguish a saved callback from a replacement and
tie recursive invocation through a cell. The next milestones should expose new
behavior through actual producer claims and independent consumption:

| Milestone | Completion example | Semantic work to preserve |
| --- | --- | --- |
| Function-shape guards | Select a callable from a mixed union with `typeof x === "function"`, then invoke it. | Complete through the existing `isFun` tag rule and checked source refinements; includes mixed unions, captured guards and effectful operands. No signature is invented. |
| Required argument lists | Two arguments with effects distinguish callee-first and left-to-right evaluation, and a wrong second argument fails. | Complete through source lowering and both producers, including native zero-argument thunks. Optional/rest parameters and spread actuals remain separate work. |
| Initialized function field | A fresh arrow receives a named field, an alias observes a write, then calls the function. | Complete through both producers and the existing native callable allocation/read/write/call rules. Construction is restricted to explicitly typed `Object.assign` of a fresh arrow and a fresh object literal; its fields are named by the program. |
| ~~Multiple object fields~~ | *Done.* An object is a finite map from field names to locations, fixed at allocation; each field is invariant on its own. `make_fields_rule` allocates one location per named field, `covers_recs` composes contracts field by field, and a current-content assertion names the field it is about. | |
| Optional fields | Distinguish an absent field from a present field containing `undefined`, including reads and initialization. | Define presence separately from value type, then support the chosen presence tests and mutation policy. |
| `.call` | Explicit receiver and argument effects reach the intended function; incompatible receiver or argument claims fail. | Local source-created arrows now preserve receiver evaluation through the pipeline. Receiver-dependent methods remain pending. [call-objects.ts](tests/callables/call-objects.ts) is the boundary example: an extracted method uses a new receiver, while an arrow retains its capture. Establish the intrinsic operation rather than assuming every property named `call` is `Function.prototype.call`. |

Functions returning functions, including escaping callback parameters, already
have pipeline coverage. Partial `.bind` on local arrows now saves required
arguments through the pipeline. `.apply`, optional/rest arguments, constructors
and receiver-dependent methods extend the call interface further; they should
follow explicit argument and receiver contracts rather than be erased into free
unary calls. These milestones are not prerequisites for the completed bounded
callable-model integration.

### Negated Boolean conditions

As a value expression, `!e` lowers to `if e then false else true`. As a graph
condition, it checks that same expression claim through a supplemental ordinary
proof, evaluates the operand once and swaps branch destinations. Repeated
negations therefore preserve both immutable variable identity and justified
current-read links. Loop conditions use the same mechanism. Closure branches
use `ifBoolVar` with corresponding swapped arms. Any operand effects still occur
before dispatch; writes and calls invalidate facts through the ordinary effect rules.

Negation adds no semantic primitive or trusted typing rule. Null equality uses
the union-elimination and observed-edge mechanisms described below.
The `ifKnown` rule now establishes singleton negation results as well: its
condition proof determines the reachable arm, while preserving condition effects.

The negation integration also supplies a concrete completeness gap in the
producer: `while (!flag) { return true; } return flag;` always returns true, but
SKJS forgets the loop-exit refinement and rejects the `true` annotation. Repairing
only the exit binding and returned-expression claim makes the program verifiable
with the existing calculus rules. The regression uses the ordinary partial
export without `--keep-going`, and independently checks the produced evidence.

### Function-shape predicates

The trusted parser recognizes strict equality or inequality between `typeof e`
and the literal `"function"`, in either operand order. It lowers that syntax to
one Boolean shape test; neither a general string value nor a separate claim for
the `typeof` intermediate is introduced. The operand and the complete predicate
retain their source claims. The operand runs once through the existing tag-test
plan and graph rules.

Only a syntactic immutable variable may carry the guard's refinement into a
branch. The existing `isFun` slice retains its callable signatures and removes
other shapes; testing a call or mutable read does not refine another expression.
The TypeScript producer follows the same explicit guard edges for fixed binding
contracts and immutable captures. [guards.ts](tests/callables/guards.ts) checks
mixed unions, a returning negative guard captured by a thunk, and a call operand.
Forged polarity, variable identity and stronger result guarantees are rejected.

### Null predicates through union elimination

Inside a closure, a null/undefined guard on a captured mutable local may save
its read into an immutable temporary. The branch proof narrows that temporary;
subsequent reads and statement-entry claims use its checked type. This lowering
is restricted to branches for which `readOnly` excludes writes, calls,
allocations and escaping closures. It establishes no persistent narrowing of
the cell's storage contract and carries no observation across a back edge.
`captured-local-guards.ts` checks the supported shape; `mutable-guard-effects.ts`
checks that a write or callback prevents reusing the saved value.

For graph branches, the lowering retains the tested read through tag dispatch.
A finite null/undefined observation narrows the saved value and propagates to
its live heap read links. This permits copying a guarded local to a const and
capturing that snapshot. Writes and calls invalidate those links through the
existing effect rules. Closure creation preserves old heap facts at every arity:
it allocates fresh storage but does not execute the closure body.

`HasTy.unionVar` eliminates one variable's finite union by checking the same term
and result under every singleton-label alternative. Its soundness proof selects
the alternative containing the actual immutable value; no semantic budget enters
the rule. The ordinary evidence checker enforces complete coverage and unchanged
other bindings. Derivation-to-evidence completeness is extended with this rule.

The source adapter checks strict equality/inequality against null or undefined,
including named singleton operands, inside callbacks and with effectful operands.
Numeric singleton comparisons use the same lowering and checked tag dispatch;
the tag carries the double bits. Unknown numeric outcomes retain both branches.
Lean resolves nonliteral comparisons from the common source claims and keeps the
singleton operand as an ordinary expression obligation; the selected tag test
is justified only if that obligation checks. Both operand claims are
required and both expressions evaluate in order. Existing `ifTag` plus `unionVar`
prove the lowered predicate. Tests exercise both operand orders and polarities,
independent consumption, omitted alternatives, and forged claims.

Tag dispatch now uses the shared observed-edge checker in the graph safety proof.
Top-level null guards and loop conditions refine syntactically identified immutable
variables, including negations and either operand order. Source evaluation and all
predicate claims are preserved; a subsequent immutable lookup supplies the observed
value. No property read or call is repeated or granted a retained refinement.
`tests/stateful-source/null-guards.ts` exercises guarded returns, older bindings,
loop bodies and break. `tests/skjs-incomplete/null-loop-exit.ts` is rejected by
SKJS, but repairing its final entry and expression claims permits independent
verification of the null-tested loop exit, including `continue`. This proves
type safety, not termination for the null input.

Closure null guards now use existing union elimination and known-tag conditional
rules. The original condition is evaluated and saved before splitting the tested
immutable slot. Each primitive label checks the selected arm; supplied arm-entry
and expression claims are still independently required. This adds a source-directed
proof recipe, not another typing rule or graph-backed closure body. Parameters,
captures, negation and effects in the selected arm are covered. Retained property
refinements and closure loops remain outside this slice.


### Compositional unions at the source boundary

`Fragment.translate` now decodes each union atom through its existing primitive,
cell or function decoder, then canonicalizes the combined labels. It rejects the
entire type if any arm fails. This needs no new graph label or semantic rule:
label lists already denote unions. Required cell fields and arrow arguments and
results admit primitive/callable unions through `Fragment.callableType`;
nested records remain outside this fragment.

Locally allocated nullable cells and optional checked-closure results exercise
the extension. External cell parameters remain rejected: annotations alone
cannot exclude accessors. Arrow parameters are assumed at their annotation. A
regression checks that adding null to a cell parameter does not evade this
boundary. The
null-guard examples include local annotation checks and functions that return
null on one path and a locally created cell or closure on another.

Source ternary expressions now share the closure conditional proof construction.
They require their own result claim and each operand claim, rather than a
synthetic statement-entry environment. This supports dynamically chosen local
nullable cells and callbacks without changing the external-value boundary or
adding a typing rule. Effectful conditions and selected-arm effects retain their
ordinary sequential evaluation.

Null coalescing uses the same existing null-tag and union-elimination rules:
save the left operand once, evaluate the fallback only for null or undefined,
otherwise return the saved value (including false). The fallback may allocate,
write or call. For an immutable variable operand, moving its name to the saved
slot exposes its nullish refinement; reads and calls confer no retained alias.
Both operand claims remain required. Examples use named cell/callback fallback
contracts because the current exporter can leave compound inferred alternatives
unsupported; the consumer does not approximate them.

Boolean short-circuit operators reuse the existing conditional rules and source
proof builder. Statement guards use checked graph paths and retain the complete
condition claim as a separate obligation; no condition type is discarded by
lowering. This extends syntax without changing refinement semantics or adding
truthiness. See [derived forms](PROGRAM-TYPING.md#derived-source-forms),
[AST encoding](REQUEST-PROTOCOL.md#expression-closures-and-calls), and the
[regression index](tests/README.md) for their respective details.

The [compound-write witness](tests/skjs-unsound/README.md) connects that syntax
to known issue #598. SKJS now rejects its stale singleton returns; its partial
first-error export cannot certify the whole source. The runtime counterexample
and repaired status are documented with the fixture. The captured-call witness
now also rejects, and its obsolete diagnostic candidate and failing-edge audit
have been retired. A boundary rejection is not evidence of unsoundness.

### Initialized callable field

`function-field.ts` carries one invariant mutable `value` field on the same
object as a free call signature. The exporter preserves both in a `callable`
atom; the source gate lowers their conjunction to the existing graph callable
clause. It does not treat the components as union alternatives.

The trusted parser recognizes only standard `Object.assign` with two explicit
type arguments, a fresh arrow, and a fresh object literal. It rejects
shadowing of `Object`. The adapter checks both annotations and fuses the
unexposed arrow and temporary object allocations into one initialized callable
allocation, preserving initializer evaluation. This is part of the reviewed
source extraction boundary, not a theorem about arbitrary JavaScript builtins.
Explicit type arguments avoid SKJS's current inference of `never` for the
unannotated construction. Named/multiple/optional fields, general expando
assignment and receiver-dependent functions remain separate milestones.

### Local arrow receiver calls

The source gate recognizes `.call` only on fresh arrows, the restricted callable
field initializer, and immutable lexical aliases of those values, including
captures. It checks lexical bindings rather than relying on a type's call
signature: an arbitrary function parameter or call result could have its own
`call` property. The supported source fragment cannot write that property or
mutate the standard function prototype. As with `Object.assign`, identification
of the standard intrinsic belongs to the trusted source boundary.

`receiver-call.ts` exercises a function with a field and a captured nullary arrow.
Both producers verify its claims. Lowering saves the callee, evaluates and checks
the receiver, then evaluates actuals left to right. The native call receives only
the actuals. The receiver's effects persist even though arrows ignore its value;
a JavaScript control that omits the write changes the result. The independent
consumer rejects changed receiver evidence, false receiver claims and wrong
actual counts. Ordinary `this`-dependent methods still require receiver semantics.

The captured receiver test also covers SKJS's optimized local-object assignment
path. That path records the receiver's pre-write type for export without routing
it through the ordinary variable-read operation, which would freeze object
growth. The dedicated `assignment-receiver` export snapshot preserves this
collection obligation independently of the `.call` source lowering.

### Bound arrow arguments

`bound-arguments.ts` distinguishes saved argument values from a target's live
cell capture and returns a fully bound nullary function. The parser restricts
`.bind` to the same source-established arrow provenance as `.call`; a bound
result retains that provenance. Receiver and prefix expressions run once at
binding time, in source order. Lowering saves them in native lets and constructs
an ordinary closure that calls the saved target with the saved prefix followed
by its new parameters. No new runtime operation or semantic axiom is introduced.

The claimed result signature determines the proposed remaining parameters, but
does not authorize them: the independent consumer checks their concatenation
with the saved prefix against the original callee contract, then checks the
result. Incorrect arity, prefix type and result claims fail independently.

SKJS deliberately rejects bound arguments. Preserve that behavior: this is an
[SKJS incompleteness example](tests/skjs-incomplete/bound-arguments.ts), whose
original export does not verify while TypeScript's claims do. The suite asserts
SKJS's rejection and separately checks the tsc candidate; it never silently
repairs the original export or changes SKJS to accept the program.

The tsc producer expands an instantiated fixed tuple-rest signature into its
required parameter list. TypeScript uses this representation for `.bind` results,
including an empty tuple for full binding. Tuple element flags and length must
establish that every element is required; optional and variadic tails are refused.
This does not admit rest-parameter syntax through the source gate.
