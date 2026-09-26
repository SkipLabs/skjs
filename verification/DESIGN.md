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

| Next target                                                                                                                                                                                                                                      | What the verifier should expose                                                                                                                                                               | Work and boundary                                                                                                                                                                                                                                                                                                                                                          |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **1. Both directions of alias writes — `L-MUT-ALIAS`, deep dive H.** [Corpus report](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/narrowed-alias-stale-write.md).                       | A narrow alias cannot promise Boolean contents while another alias may legally write null; conversely, writing through a wide alias cannot preserve the original view's non-null read fact.   | Reduce to locally allocated `{ value: null \| boolean }` cells and explicit aliases. The calculus already has shared locations and invariant references. Expect an unjustified alias contract in the first direction and a stale read in the reverse direction; pin the actual failing obligation. Do not introduce covariant mutable views to accept the original export. |
| **2. A closure reads under its creation-time narrowing — `L-STALE-READ`, deep dive F.** [Corpus report](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/stale-closure-reads-narrowing.md). | A reader created while a cell is non-null cannot promise a Boolean result after another write stores null. This differs from a callback that writes and leaves the caller's refinement stale. | Use the report's field-level variant, a local primitive cell and a unary null-argument reader. No mutable lexical binding or external object parameter is needed. Exercise the arrow guarantee over every admissible future heap: a creation-time observation is not a permanent captured invariant.                                                                       |

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
      if (second) {
        return saved;
      }
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
[SourceExtraction.lean](lean/Verification/Model/Source/SourceExtraction.lean).
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

An unannotated `let` has the contract TypeScript declares for it, the
initializer's type widened (`let x = 1` stores `number`, not `1`): the
producer states it as the binding's claim at the next statement's entry, and
Lean checks the initializer and every write against it, as for a written one.
A declaration ending its block, which nothing reads afterwards, takes its
initializer's claim. `let x: T;` is `let x: T | undefined = undefined`, what
JavaScript binds there; TypeScript's definite-assignment verdict is not
consulted, since reading the cell at `T` needs the current-content fact that a
write of a `T` value establishes on every path to the read. A closure reads
the cell at its contract: it may run before the write, which TypeScript does
not check (`invalid-captured-unassigned-let.ts`). The rules are in
[Program typing](PROGRAM-TYPING.md#mutable-bindings-and-module-constants).

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

A closure's result annotation may likewise be omitted, as TypeScript lets an
arrow's result be inferred. The closure's type is then only the producer's
claim at the closure: every arrow it claims has its own body derivation at that
arrow's parameters and result, which is what the creation rule already
requires ([source closures](PROGRAM-TYPING.md#source-closures-and-their-annotations)).
An annotation adds a requirement, the body at the annotated signature, and
bounds the claimed parameters; omitting it removes that requirement and never
a check, so the trusted surface is unchanged. The Fragment says which: its
`result` is the annotation or `null`. A closure whose result the source leaves
out still needs the annotation where a path takes its result type from the
source: a block returning from a branch (refused by the parser), a closure
collecting a rest array, a quantified one and one inside a generic body
(refused by Lean). Which result the producer claims is a proposal: the body's
type widened, as TypeScript infers it, or, for a literal expected at one
signature taking at least its parameters, that signature's result (its
contextual return type) where the body's type fits it. So `() => "hello"` at
`{ fn: () => "hello" }` keeps its literal result, which widening would lose
and invariance of the mutable field would then refuse, and `async () =>
"hello"` at `() => Promise<string>` is claimed at the promise the context
names (`closure-contextual-result.ts`). Lean checks the body at the claimed
result either way (`invalid-closure-contextual-result.ts`).

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
later writes; its initial value claim alone is not that contract. Its absence
is explicit: the producer refuses an unannotated `let` initialized with `null`,
`undefined` or `[]` rather than inferring a lifetime union or treating the
initializer as a permanent invariant.

### Valuable later targets and the traps they introduce

| Target                                                                                                                                                                                                                           | Why keep it on the list                                                                                                                                                                           | Why it follows the mutation targets                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Incomparable function signatures are not disjoint — `L-INTER-BOT`.** [Witness](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/tfun-inter-incomparable-not-disjoint.md). | Directly exercises the positive calculus's function intersections. Begin with a calculus witness: one checked constant-null closure inhabits both a null-domain arrow and a Boolean-domain arrow. | Source integration needs richer callable claims and a sound identity/comparison story to reproduce the equality branch. Extensional arrow membership does not establish JavaScript function identity. Do not add intersection completeness or unrestricted arrow-result merging as a prerequisite.                                                                                                                                                                                                                                                                                                                                                |
| **Numeric false disjointness — `L-LIT`, deep dive G.** [Witness family](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/beyond-precision-numeric-literals.md).             | Distinct decimal spellings can denote the same binary64 value, making a claimed unreachable branch live. It tests runtime grounding independently of mutation.                                    | The calculus now models numbers opaquely, and a literal's identity is the bit pattern of the double it denotes, with source literal type `0` denoting both signed runtime zeros. Runtime literals and arithmetic preserve the sign, which division observes; strict equality still equates the zeros. Other decimal spellings of one value share their bit singleton. Strict equality against a numeric singleton now filters finite singleton unions using Number::equal; a test on the broad number family is typed as a Boolean and both branches retained; arithmetic is the double operation yielding the family; truthiness remains absent. |
| **Callability/absence, getters and void.** `F-CABSENT`, `ACCESSOR-METHOD`, `L-SEQ`.                                                                                                                                              | The corpus has concrete reachable-never and non-callable-call witnesses.                                                                                                                          | They require object-shape guarantees, accessor execution, or an explicit distinction between void as a typing convention and undefined as a value. Object parameters are assumed at their annotation as part of the interpreted caller contract, which is not the same as trusting a structural declaration to exclude accessors at runtime; do not treat void as a disjoint runtime tag.                                                                                                                                                                                                                                                         |
| **Inference-state and expansion failures.** `MR-1`, `C-FREEZE-CACHE`, `L-SUB-TSINST`, `E-EXPKEY`.                                                                                                                                | Wrong inferred types remain valid verifier targets even when their cause is a cache or substitution bug.                                                                                          | Select a concrete escaping wrong claim whose ground types fit the calculus. This pipeline should check that consequence, not model SKJS caches, rollback or its entire generic inference algorithm. Once a ground consequence is in reach, export the responsible subtype or expansion judgment with the snapshot in force at that judgment and check that operation's contract independently. Universal generic certification needs separate rules; checking one ground instance does not supply it. See [Semantic contracts for SKJS operations](#semantic-contracts-for-skjs-operations).                                                      |

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

The pipeline currently checks SKJS's _conclusions_: program-point types and
invariants, translated into the calculus. That remains the source integration.
The stronger use of the model is to give SKJS's individual operations precise
semantic contracts, so a transformation is legitimate or unnecessary relative
to those contracts rather than relative to the current implementation.

Three similar-looking kinds have different meanings:

| Kind                              | Semantic obligation                                                        |
| --------------------------------- | -------------------------------------------------------------------------- |
| Generic parameter `T`             | The body must work for **every** admissible `T`.                           |
| Inference variable `?T`           | The checker may **choose** a type satisfying the constraints.              |
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
[mathematical audit](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/skjs-type-soundness.tex). That model
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

### Operation bridge and generic milestone

The operation-level bridge and deliberately small generic fragment provide a
reference for repairing SKJS's reasoning, without committing to formalizing
the current implementation wholesale.

The first slice of the operation-level bridge is implemented: SKJS exports
closed subtype and expansion judgments from a function body, serialized under
the substitution in force at the judgment. `--check-skjs-operations` translates
those that fit the existing primitive, cell and arrow fragment and checks them
with the current subtype consumer. Live inference variables are not the
representation; clones do not contribute; a failed search is unproved, not a
disproof. See [Request protocol](REQUEST-PROTOCOL.md#closed-operation-export).

The first-order generic fragment is implemented in the model. Generic function
declarations use the rigid-parameter source path, and local quantified closures
use the separate scheme path described below. Rigid parameters are labels
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
[TypeParams.lean](lean/Verification/Model/Types/TypeParams.lean).

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
semantic inclusion under assignments satisfying those bounds. Copies and
returns use that traversal, including chains ending at boolean. An unannotated
immutable copy retains the checked initializer type; a producer cannot choose
a stronger binding type. Every declarator sees the preceding checked copies. Bounds
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
This checks variable-copy bodies. Calls to generic function declarations,
generic callbacks, higher-rank and parameter-changing forms remain later work.
Local quantified closures are the separate source form below; their call sites
carry checked scheme eliminations and do not add declaration-call inference to
this path.

[TypeSchemes.lean](lean/Verification/Model/Types/TypeSchemes.lean) provides
semantic rules for the next callable extension. A scheme denotes one callable
value satisfying its signatures under every admissible assignment of its bound
parameters; the assignment is fixed outside those binders and must satisfy the
declared bounds. Callable shape is required even if no assignment satisfies the
bounds. Introduction therefore proves a universal property of the same value,
not just safety of different evaluations at a sample of type arguments.
Elimination specializes that property, and `scheme_call` uses the existing
operand-effect and future-world call rule. `make_scheme_fields` performs one
allocation with fixed field contracts before quantifying over the callable's
signatures. `invocation_of_scheme_body` checks all instantiations against the
same captured environment and world. Scheme meanings are admissible closed-value
families, so semantic higher-order composition uses the existing type universe.

The source interface now connects a deliberately narrow executable slice of
these rules. One immutable local quantified closure is admitted per containing
function. A binder may be bounded by an earlier binder or any ground type; every
parameter and the result name one of those binders, unions mentioning them, or
function types over them; and the body is a variable, a primitive literal, an
assignment to a captured cell, a call to a callback known over the binders, or
a closure whose parameter annotations name the binders, checked under them like
the outer body and whose claim must be exactly that annotation, its result
annotation or, where the source leaves the result to inference, the result of
the closure's own claimed arrow, which the body is then checked against. A captured cell
keeps its declared contract at every instantiation; a write of `T` into it is
refused as an obligation. Scheme
introduction checks that body once under rigid binders, independently of which
calls happen to appear. At least one call-site claim must then supply a complete
ground substitution. Each substitution must satisfy every substituted bound at
its call, and is then compiled to an ordinary arrow used by the existing graph proof; several calls may choose different
ground types without rechecking the body at each type.

The scheme itself is a source-claim form and semantic layer, not a new positive
graph clause. No scheme certificate is serialized yet: introduction is checked
directly during source request construction, while the compiled eliminations
produce ordinary graph evidence. Bounds to an earlier binder or to any ground
type, the source's `boolean`, `string | number` or `{ length: number }` as
well as a source-imported graph type such as `Json`,
callbacks over the binders, captured fixed-contract writes and returned closures
that retain an outer binder are implemented. Nested quantified closures,
general closure bodies, calls to generic declarations, recursive scheme nodes
and higher-rank schemes remain outside. Recursive schemes additionally need
layer congruence and contractiveness; admissibility of a fixed scheme does not
establish that extension.

Graph evidence for those eliminations is an intermediate result. The accepted
source path converts every `FunctionPlan` exhaustively to `CertifiedPlan`;
direct generic variable-copy plans carry a checked `GenericCertificate`.
Schemes built from immutable or captured-cell reads, nested closures and callback calls
additionally carry a `ClosureCertificate`:
its soundness theorem establishes the universal invocation premise in the same
captured environment and world, independently of observed calls. Nested closure
allocation and effectful calls use the existing semantic rules. Captured cell
slots carry their source-declared invariant, and reads use `bag_read`; an ordinary
variable proof cannot expose the private cell. Writes inside a quantified body
still need a certificate constructor. `checkJson_safe` concludes
calculus safety for every graph request, semantic safety for every direct
generic certificate, and universal invocation safety for every admitted scheme.
The graph evidence for a scheme never replaces its universal certificate.

### Generic bodies are graph requests over parameter rows

A generic function's body is checked by the graph checker, the one every other
body goes through, with each binder read as a **parameter row**: a row that
means whatever the graph's assignment gives it. The unit is then an ordinary
graph request, and its evidence is certified at every assignment of those rows.
Records, tuples, arrays and field reads and writes over a binder, literals,
`??`, `if`, `let`, `typeof`, calls of other generic functions at a binder:
everything the graph mechanism checks for ground types, it checks over a
binder, with no rule of its own. A second typing mechanism (records and heap
operations in the direct checker) was the alternative, and was not taken.

**Parametricity.** The graph's assignment is semantic only; no check reads it.
`Parametricity.accept_reassign` proves this for the whole checker:

$$
\mathsf{accept}(G[\mathit{env}:=\eta],R,P,\mathit{claims},C,s,\vec I)
=\mathsf{accept}(G,R,P,\mathit{claims},C,s,\vec I)
\qquad\text{for every }\eta .
$$

Most checkers are definitionally independent of the assignment; the lemmas are
for the recursive ones (arrow, clause and subtype certificates, edges,
evidence trees), whose unfolding the kernel does not do on its own, and the
checkers built on them. Safety of accepted evidence is proved for every graph,
so it holds at every reassignment (`Parametricity.accepted_at`,
`RequestJson.verify_safe_at`). `checkJson_safe` now concludes, for every graph
request,

$$
\forall\eta.\;\mathsf{EnvOk}_{G[\eta]}(\vec I,\rho)\Rightarrow
\mathsf{SafeGraph}\bigl(P,\llbracket R\rrbracket^{\eta}\bigr),
$$

which at a request without parameter rows is the old statement, and at a
generic body is safety at every instantiation of its binders: the inputs and
the result are read at the same $\eta$. A new checker is covered by adding its
`_reassign` lemma next to its callers'; a checker that read the assignment
could not be given one.

**Extraction.** The OCaml producer names each binder's row in the claim table,
`{"param": l, "name": "T", "kind": "value"}`, one per spelling, wherever a
claim mentions the binder inside a graph type (`Box<T>`, `{ value: T }`,
`T[]`). Lean reads a generic unit's binders as those rows (`binderRows`: the
table's one value parameter row of that name that no scheme binds, or a new
one), substitutes them for the binders in the unit's claims and in its source
annotations (`Function.atRows`, `annotationAtRows`), and extracts the unit as
any other. A call of a generic module function at a binder names the instance
at the binder's row, which that function's own certificate, at every
assignment, covers.

**Bounds.** A binder bounded by a ground type of clause rows is read as the
meet of its parameter row and its bound, `T extends { length: number }` as
$p_T\sqcap\{\mathit{length}:\mathsf{number}\}$, whose values are the
assignment's values of $p_T$ within the bound. The body is certified at every
assignment; at one within the bound, which is every instantiation TypeScript
admits, the meet is the binder itself, so no admissibility premise is needed.
A core table covers a meet row through its clauses
([POSITIVE-TYPES](POSITIVE-TYPES.md#core-tables)), which is how `x.length`
reads through the bound, and nothing is below the meet but itself and its
subtypes, so `{ length: 1 }` is not a `T`. The producer reserves the meet row
through the intersection wire (`meets`, operands the binder's row and the
bound), and Lean fills it, and reads the unit's binder as it, from the same
operands. A bound over another binder (`U extends T`) leaves the parameter
row alone: the body is certified at every assignment, stronger than
TypeScript's statement and still true, and a body using that bound finds no
derivation.

#### Generic classes

A generic class's binders are in scope in its members, which the parser
desugars as a non-generic class's are: one constant per method, a closure over
the instance type `C<T>`, then the class value, construct-only code allocating
the instance. The binders belong to the code unit that runs the declaration,
the module's initialization unit: it is a generic unit like a function, its
binders read as parameter rows (a bounded one as the meet of its row and its
bound), one row per spelling for the whole top-level code, so two classes may
share a binder's name only with the same bound, and an application over a
class's binder and one over a function's binder of the same spelling are one
row (the producer keys its reserved applications by their argument rows). The unit is certified at every
assignment of those rows: each constructor and method body at every
instantiation of its class. The instance type `C<T>`, whose methods' receiver
is the application itself, has no finite expansion in claim form; it is the
application row at the binder's row, in the producer's claims and in the
source annotations alike. A member read through a bounded binder inside a
method reads the bound's member (`throughBound`).

A unit that uses the class reads it as a generic module value: each `new`
names its instance, and the slot holds the constructor at those instances, read
from the class's constructor type with the binders fixed. That reading relies
on the class value meeting its constructor type at every assignment, which the
initialization unit's certificate states one assignment at a time; linking
units, as for every module value, is outside the proof.

A generic method with binders of its own, a closure over a class's binders
that declares more, is refused: typing it needs scheme introduction in the
program typing, a closure at a scheme row whose body is checked at every
reassignment of the scheme's binders, which the graph does not yet have.
A generic class neither extends a class nor is extended: the base part's
construction would be a generic application the derived constructor states.

**The direct checker.** A generic unit goes to the direct rigid checker
(`GenericSource`) first, for the variable-copy bodies and dependent bounds it
states located obligations for; a failed obligation stands. A body outside its
forms, a refusal, goes to the graph checker. The direct checker is kept only
because it still covers dependent bounds (`U extends T`) and located
obligations for variable-copy bodies; once the graph path reads those it is
retired. Its types have no parameter rows: a claim or annotation over a
binder's row (`SourceTypes.reachesParameter`) is refused there, so the unit
goes to the graph checker rather than having the row read as a ground type. Nested generic closures (a closure with binders of its own inside a
generic body) are refused on the graph path: their binders need scheme
introduction in the program typing, which the graph does not yet have.

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

### Writable string index signatures

A mutable index signature, `{ [key: string]: T }`, lets TypeScript code holding
the dictionary add keys and overwrite values at `T`. TypeScript also treats it
covariantly and lets a readonly one pass as a mutable one. Lowering it to the
readonly view would be unsound in practice: an external writer handed a
dictionary of `true` at `{ [key: string]: boolean }` could store `false` where
the program still reads `true`. So it lowers to a **writable index contract**
(`dictCellT`, [POSITIVE-TYPES.md](POSITIVE-TYPES.md#records)): every present
string-keyed field's location holds exactly `T`, as an invariant field's does,
and covering keeps it invariant. A writable index is also a readonly one, and
reads use that. Consequences:

- A mutable dictionary of `true` is not one of `boolean`, and a readonly
  dictionary is not a mutable one: both are refused, as mutable arrays and
  fields already are (the choice follows the one for arrays: soundness over
  TypeScript's covariance).
- A write through an existing key at `T` is a calculus step that keeps every
  alias's guarantee, because the location's contract is `T`.
- The calculus has no step that adds a key to an existing object; no program
  rule writes through an index. That code outside the unit (an import, a
  callback, the caller) adds keys at `T` to a dictionary it holds at a writable
  index, only keys the index's class admits ([Index signatures](#index-signatures)),
  is assumed, not modelled. Every capability the checker grants on such
  an object is implied by the writable contract, so a key added at `T` keeps
  them: covering a writable index requires every index and optional field of
  the source over its keys to admit `T`. This argument is informal.

An empty literal, `{}`, is admitted by the source gate. It has a type only
through a contract: a dictionary, whose writable index a fresh literal meets
through its exact own keys ([Fresh literals have exact keys](#fresh-literals-have-exact-keys)),
or a record with no required field.

### Fresh literals have exact keys

**Principle.** A fresh object literal's own keys are exactly the keys it
writes, fixed at allocation, and it has no prototype. That, not its record
type, is what makes it a dictionary (`{ input1: …, input2: … }` at sum.ts's
`Inputs`, an interface extending `NamedInputDefinitions`' index signature) or
a record lacking an optional field it leaves out (`runService`'s options
without `no_cors`). An existing record type is open: a value of it may hold
further keys at any type, so it meets neither, and TypeScript's acceptance of
it (implicit index signatures, width subtyping into optional fields) is
refused.

**One mechanism.** `alloc` already types a literal at a record whose own-key
bound, $\mathsf{among}$, lists exactly its names (`ownKeysT_slots`). Two coverage rules read the
bound: an optional field, when the bound excludes its key and the prototype
key (`CoversOptional`), and index contracts, when the prototype key is not in it
and every key of it is a field or view within each index view and a field
equivalent to each writable index (`CoversKeys`, `covers_keys_sound`). The
dictionary allocation rule `allocDict`, which typed a literal at a pure
dictionary by giving every location the index contract, is the special case
of `alloc` then `CoversKeys`, and is removed; with it `make_dict_rule`,
`recT_fresh_dict` and `recT_fresh_cell`.

**Producer.** The OCaml producer claims a literal at its exact record (the
semantic atom `Exact`, a refs clause with that one bound) where its contract
has an index or an optional field; elsewhere at the open record as before, so
no other claim changes. The literal's use is then an ordinary subsumption,
checked where the literal flows, and a literal claimed at a dictionary is no
longer accepted: a claim names the record allocation gives. Each key the
contract names is built at its member's type, any other at the index. At a
generic call, an actual whose parameter mentions none of the callee's type
parameters has that parameter as its contract, as at a call without them
(TypeScript types it contextually too): the options literal passed to the
generic `runService` of the sound binding leaves out `no_cors` by its exact
keys (`generic-contextual-literal.ts`); a record held in a variable does not
(`invalid-generic-contextual-literal.ts`). An actual at a parameter that
mentions one is typed on its own and informs inference, as before.

**A union contract is discriminated first.** Where the contract is a union of
several records (or several arrays), no one arm is the literal's contract, and
widening its members gives a record no arm admits: `{ kind: "a", n: 1 }` at
`{ kind: "a"; n: number } | { kind: "b"; s: string }` widened is
`{ kind: string; n: number }`, and a mutable field's contract is invariant.
The producer selects, as TypeScript discriminates a contextual union by an
object literal's properties, the arms that admit the literal: every key it
writes is a field of the arm (or the arm has an index), every required field
of the arm is written, and every member written as a primitive literal is
admitted by the arm's field. For an array literal, an arm's length bounds and
positions admit it alike. Where exactly one arm remains, the literal is built
at it; otherwise its members are built as with no contract. This is a construction hint and adds
no trust: the allocation names the record the members are checked against,
and the literal's use is the ordinary subsumption into the union
(`literal-union-discrimination.ts`; a literal no arm admits,
`invalid-literal-union-record.ts`, `invalid-literal-union-tuple.ts`).

**Inference through a union with a binder.** The producer's call inference
(`Inference.infer`) gives a binder in a union with ground atoms, `A | null`
(inline, through an alias `Maybe<A>`, or as a construct signature's
instance), the atoms the actual holds beside those, as TypeScript infers `A
:= string` from `string | null`. The instance is
a proposal: Lean checks the actual against the substituted parameter and the
result where it is used (`nullable-binder-inference.ts`,
`invalid-nullable-binder-inference.ts`). A tuple at an array of any length
gives the binder each of its positions (`[string, number]` at `readonly T[]`,
as `%Iterate%`'s parameter is: `for...of` over a tuple yields the union of
its positions, `for-of-tuple.ts`), and a join of primitives that only widens
the literals an explicit bound names (`number` at `K extends 0 | 1`) is not
proposed over the bound.
Two more choices follow TypeScript's inference at a bounded binder. A fresh
object literal at a binder whose bound has one dictionary arm, `T extends
Json`, is built at that arm, so with its exact keys (TypeScript checks the
fresh literal against the constraint; a record held in a variable stays open
and does not meet it). And primitives below a declared bound instantiate the
binder rather than the bound, and so does an array of primitives below a
bound with an array arm (`S extends number[] | string` at `[1, 2, 3]` is
`number[]`): `check<Y extends boolean | string>` at
`"hello"` is `"hello"`
(`generic-bound-literals.ts`, `invalid-generic-bound-literal.ts`).

**An unannotated constant's fresh array is built at its first use.** SKJS
leaves `const values = [1, 2]` uncommitted until a use fixes it
(`const pair: [number, number] = values`, `takesLiteralTuple(values)` at
`[1, 2]`, `const view: Mixed[] = arr` and then `arr[0] = { x: 42 }`), where
TypeScript widens it at the declaration and refuses those uses. The
allocation's contract is the producer's to propose, and the one the first
use expects is as true of the fresh array as TypeScript's: the producer finds
the first use in the statements after the declaration and, where it is the
whole value expected at an array type (an annotated constant's initializer, a
returned value, an argument of a call to a function of one plain signature),
builds the literal there; any other first use (`values[0]`, `values.push`)
leaves it as TypeScript types it. Lean checks the elements against that
contract and every use against the binding (`array-first-use.ts`;
`invalid-array-first-use.ts`, committed to `number[]` and then used as a
pair).

**Tables relate included labels.** Relating a record to an interface compares
each field's contract with itself; a core table needed a row for each such
pair and for everything it reaches, so the search built one over the whole
pool. A table's relation now also holds, with no row, where every label of
the source is one of the target's: the meaning of a label list is the union of
its labels', so it is sound with no induction step (`Rel`, `mixed_subset`).
The search tries a table over the types two operand steps from the pair
(`nearPool`) before the whole pool. Neither adds trust.

**Search cost.** Measured, not guessed: on `sum-main` most of the search went
to walking the type table, a list, for every row read, then to core tables over
the whole pool for pairs no table can relate. Three changes, none to a rule:

- The graph of a type table reads its rows from an array built once with the
  graph (`RequestJson.tableGraph`), not by walking the list per read.
- The rows a type reaches are gathered once each: each step reads only the rows
  the previous step added (`readsFrom`), not every row found so far.
- A core table holds only rows that could be valid (`rowFeasible`): each source
  clause covered by some target clause with every subtype and arrow premise
  granted. Coverage is monotone in both, so a row failing this fails under
  every table. Pruning would remove it in its first round, and what pruning
  reaches, the largest table within the candidates whose rows are all valid
  under it, is the same without it.
  The same test on `(A, B)` itself refuses a pair before any table is built.
  Search output is unchanged; on every case the evidence is byte-for-byte what
  it was.

On `reactive-sum-sound`, the whole module, the search took about 41 s, 38 s of
it in 146 inclusions of 26 distinct pairs, nearly all spent building
prototype instances (`protoInstances`) for every array of the pool against
every method the pool names, about 0.2 s a call, 1.7 s where the pool holds
an iterable. Two orderings of the untrusted search, no rule:

- Instantiating a scheme row (`instProof`), which applies only when the
  source is one, is tried before prototype instances. Most of those calls were
  a generic method's scheme below the arrows of its read, which failed the
  prototype step first.
- Prototype instances are sought over the types near the pair (`nearPool`)
  before the whole pool, as core tables are.

The search now takes about 6 s of CPU on the module; the other `sum` cases
are unchanged or faster.

On `sum-sound-binding`, the whole module under the sound binding, the search
first took about 23 s, measured per program node and per inclusion: 7 s in
`await main()`, whose callee, `%Await%` at a fixed signature, was first
coerced to every variadic signature of the pool (`merge`, `slices`), each
failing only after a table over the pool; and 7 s after the last node, in
re-checking the evidence and printing 32 MB of it with `Json.pretty`. Two
changes, no rule: a callee read from a slot is tried at the slot's own type
first, variadic then fixed, before the pool's types, in the same order as
before; and the evidence is written with `Json.compress` (9.5 MB). The
search takes about 13 s; the check, about 4 s.

Profiled again, nearly all of both went to checking instance tables
(`TableOk`): `EagerCollection.map`'s instances carry tables of 1,200 entries,
checked 66 times in the check and some 200 times in the search, about 60 ms
each, because `entryImg` looks each image up in the whole table, so a table's
check is quadratic in its size. Three changes, none to a rule or to what is
checked:

- The compiled table check groups the entries by context once and looks each
  image up among its context's entries only (an entry's lookups are all under
  its own context or the one it enters), checks each context's rows against
  the domain once rather than once per entry, and looks a row's free rows up
  once per row (`TableOkFast`, `FreeOkFast`). `@[csimp]` theorems
  (`TableOk_eq_fast`, `FreeOk_eq_fast`) prove each equal to the definition the
  proofs use, and the compiler runs it in its place.
- Rendering a closure's direct proofs keeps the subtype searches already done,
  by source and target type, for the obligations after it
  (`DirectProof.SubtypeCache`): nested obligations coerce the same types
  again. The graph and the pool are fixed for the cache's life; search only.
- The search hints' closure over the type table (`searchLabels`) stops at its
  fixpoint instead of taking one step per type.

The evidence is byte-for-byte what it was. The search takes about 4 s of
CPU; the check, about 2 s. On `reactive-sum-sound` the search went from about
6 s to 2 s, and over all the `sum` cases the verifier's CPU from 34 s to 14 s.

Each external step of a case (parser, producer, search, check) keeps a
wall-clock limit (`stepTimeoutMs` in `check.mts`); a step that exceeds it is
reported as `timeout: <step> did not finish within <limit>`, an error, never a
verdict.

## What is implemented and proved

| Layer                      | Current status                                                                                                                                                                                                                     |
| -------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Stateful positive types    | Recursive normalization preservation and declarative subtype soundness are proved.                                                                                                                                                 |
| Subtype evidence           | The checker is sound and complete for the declarative rules.                                                                                                                                                                       |
| Program evidence           | Acceptance is equivalent to closed-program derivability for the stated rules; typing implies computation safety.                                                                                                                   |
| Point claims and slot maps | Checked incoming relations preserve semantic environments under the program's binding transfers.                                                                                                                                   |
| Control-flow graphs        | The checker covers actual nodes and edges, handler edges included; accepted graphs have no stuck execution, typed returns and closed throws, including cycles.                                                                   |
| In-memory producer         | Builds evidence from fixed point annotations; successful output passes the consumer and preserves the exact requested claims. Search completeness is not claimed.                                                                  |
| Serialized requests        | Requests and evidence pass through a separate JSON consumer in the existing verifier binary. Acceptance yields decoded-request safety.                                                                                             |
| Source-facing integration  | Primitive inputs, branches, local cells and bounded expression closures reach the stateful consumer. Primitive, cell-label and function-label translations have exact interpretation theorems; source compilation remains trusted. |

Certificate completeness means **every declarative derivation has accepted
finite evidence**. It does not mean every inclusion true in the semantic model
is derivable. Nor is there a completeness theorem for graph checking or for the
producer's search.

For the rigid/scheme source fragment, decision completeness is now stated and
proved against explicit declarative judgments, independent of the algorithms.
[POSITIVE-TYPES](POSITIVE-TYPES.md#rigid-inclusion) states inclusion under
declared bounds, `RigidJudgments.Sub`; `Ty.leUnder` decides it on well-formed
parameter lists (`leUnder_iff_Sub`), every list `parametersOf` builds is
well-formed (`parametersOf_wellFormed`), and the judgment is semantically sound
on its own (`Sub.sound`). [PROGRAM-TYPING](PROGRAM-TYPING.md#decision-completeness-of-the-direct-checker)
states typing of calculus terms (`CertificateJudgments.Typed`, equivalent to
the existence of an accepted certificate: `check_iff_Typed`) and of lowered source bodies
(`SourceJudgments.HasTy` and `Checked`, decided by `exprTyB` and
`bodyClaimsB`). The operational closure condition remains in force: each
positive example crosses the exhaustive `CertifiedPlan` boundary, and each
negative control fails its specified obligation.

Three counterexamples were found and repaired on the way, without weakening a
rule. The structural fuel of `Ty.leUnder` could not decide an inclusion through
a callable bound (`RigidJudgments.counterexample_derivable`, kernel-checked
against the old fuel). `GenericSource.check` refused a declaration returning
a call because its certificate compiler accepted only variables; declarations
and closures now share one compiler. Returned primitive literals lacked a
proof constructor; `Proof.lit` now expresses them. Its safety case, and so
`Proof.check_safe`, now assume
`GenericCertificate.Primitives`: the graph's first four rows are the
primitives. Every decoded table has them, and `FunctionPlan.certify`
establishes it for each certified plan, so the headline theorem is unchanged
in strength. These are component completeness results: there is no theorem
yet that `GenericSource.check` or the complete CLI accepts every source body
admitted by the source judgment. Annotation lowering, signature/site checks,
and certificate generation remain additional boundaries. In particular,
`HasTy.assign` can type a captured-cell write, but `closureProof` still has no
write constructor. OCaml substitution inference and graph proof search are
also outside these results.

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
in [Claim.lean](lean/Verification/Model/Types/Claim.lean); cell and function
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
- For imported and local types, TypeScript's checker decides which declaration
  each name denotes, in the file's configured project
  ([`declaration-graph.mts`](tools/declaration-graph.mts)); the parser checks
  that TypeScript read the same client bytes it parsed. Code the graph uses
  must be code TypeScript accepts: an error TypeScript reports in a collected
  declaration, or on an import or export statement the resolution passes
  through, refuses the graph. This trusts TypeScript's
  resolution and assumes the project's `tsconfig.json` (its `paths`, links and
  standard-library set) reflects the real build. Declaration equations are
  parsed from the checker's own source trees; there is no separate declaration
  or module-mapping byte check. Fixture hashes in the tests detect changed
  inputs, but are not premises of the Lean theorem.
- An enum member's value is the one TypeScript's checker computes
  (`getConstantValue`), which is the value its emit writes; a `const enum`
  read is the one TypeScript binds to the member and replaces by it
  ([Enums](#enums)).
- A computed type (`typeof x`, `keyof T`, `T[K]`, a template literal type, an
  intersection of primitives, a mapped type's keys) means the type
  TypeScript's checker computes for it, which the reader states exactly or
  refuses ([Computed types](#computed-types)): TypeScript's evaluation is
  trusted as its resolution is.
- A value from a declaration or the library owns its stated string-keyed fields as enumerable data properties, which a spread copies ([Object literals](#object-literals)); the overlay's `Error` holds its non-enumerable `message` on a prototype the model gives it.
- A spread does not copy an own enumerable symbol-keyed property JavaScript copies; its result states no symbol key and is open, so nothing typed reads one.
- The model keeps the array store key `[]` and every name in double brackets (the prototype key, a class's prototype key) for itself: no source key spells one, and an object the program receives (an import, the library, `JSON.parse`) is represented with its own keys apart from them, so `Array.isArray`, `in` and `instanceof` never find one on it. No operation of the fragment reads a prototype object itself, so a class's prototype is never the operand of `instanceof` ([Guards](#guards)).
- Source and claim translation preserve intended control flow, lexical binding,
  annotations and type meaning. Scope association cannot be recovered merely
  by checking that two slots have compatible types.
- Decoding represents the submitted program, requirements and claims faithfully.
- The calculus's execution model agrees with the supported JavaScript behavior.
  For the operators this includes that Lean's compiled `Float` operations are
  the IEEE-754 double ones and `Float.pow` is C's `pow`, which `binop` corrects
  where JavaScript's `**` differs; node's values for the edge cases are
  checked in `Tests/SourceExtractionTests.lean`.
- `Array.prototype` meets `ArrayProto`: the engine's native array methods,
  invoked on an array, behave as TypeScript's declarations of `ReadonlyArray`
  and `Array` state them, as filtered by the overlay
  ([`array-prototype.mts`](tools/array-prototype.mts)): only its members, at
  its receivers, without its dropped parameters and overloads. Nothing checks
  the native code. The assumption enters every result as a premise: a unit
  that allocates arrays has an input slot `[[Array.prototype]]` at `ArrayProto`,
  and the safety theorem holds for every environment meeting its inputs, as
  for an imported value's declared type.
- `Object.prototype`, `Array.prototype` and `Function.prototype` hold no own
  string key but those `inKeyRefusal` lists (node's
  `Object.getOwnPropertyNames` of each): `key in o` for any other key is the
  model's own-key test ([Guards](#guards)). A realm that adds a key to one of
  them would answer `true` where the model answers `false`.
- `String.prototype`, `Number.prototype`, `BigInt.prototype` and
  `Boolean.prototype` meet `StringProto`, `NumberProto`, `BigIntProto` and
  `BooleanProto`, each read from TypeScript's `String`, `Number`, `BigInt`
  and `Boolean` through the same overlay: only the listed members, each an
  own property of that prototype, at the primitive as receiver, without the
  dropped parameters. A unit reading a primitive's
  member has the input slot `[[String.prototype]]` (and so on) at that
  contract, a premise as `[[Array.prototype]]` is. The realm's
  `String.prototype` and `Object.prototype` own no numeric key, so a
  string's index that is not an array index reads `undefined`
  ([Primitive members](#primitive-members)). `String.prototype` owns no
  `[Symbol.split]` or `[Symbol.replace]`, so `split` and `replace` of a
  string pattern run no client code.
- `Set.prototype`, `Map.prototype` and `Date.prototype` hold the natives the
  interface overlay lists ([Library collections and dates](#library-collections-and-dates)):
  a value the host constructs as a `Set`, `Map` or `Date`, invoked through
  a listed member, behaves as its reviewed signature states. A unit using
  them reads them through its values' declared types and the stated
  constructors, premises as a global's selection is.
- An ambient declaration the module writes, `declare function f(...): R`,
  `declare const x: T` or `declare class C`, holds of the value the running
  environment supplies under that name (**Ambient declarations** in
  [Modules and code units](#modules-and-code-units)): nothing in the module
  defines it and nothing checks the code that does. It enters every result as
  a premise, as an imported value's declared type does, and the declaration
  document lists it with the specifier `ambient`. A function declared with
  overloads, ambient or imported, is assumed to meet every overload.
- A global value the module reads, such as Node's `process`, meets its
  declaration at the members and call signatures the module selects
  (**Global values** in [Modules and code units](#modules-and-code-units)),
  and no code the module does not see reassigns it. A standard library global
  meets its reviewed overlay entries
  ([Library globals](#library-globals), [`library-globals.mts`](tools/library-globals.mts)):
  `BigInt` returns a bigint or throws; `Symbol`, `Symbol.for` and
  `Symbol.keyFor` return what they declare; `String` converts a primitive;
  `console.log` returns `undefined` without running client code; `Object.keys`,
  `Object.values` and `Object.entries` return fresh arrays of own enumerable
  string keys, values and pairs. `Object.keys` calls no getter; the other two
  read each value, which runs a getter of an accessor property: the fragment
  writes none, and a host object's is assumed to return. Nothing
  checks the native code; the selection enters every result as a premise, the
  global's input slot, as for an imported value's declared type.
  `new Array()` returns a fresh empty array and `new Error(m)`, with a string
  `m`, an object owning `message` at it, as their stated signatures say;
  `new Set(xs)`, `new Map(es)` and `new Date(…)` a fresh set, map or date;
  `JSON.parse` a value or a `SyntaxError`; `JSON.stringify` of a
  `JsonValue` a string, calling nothing, since `Object.prototype` has no
  `toJSON`; the generic `Object.values` and `Object.entries` of a
  dictionary its values at their index type.
  `Array.isArray` is no premise but the calculus's test $\mathsf{isArray}$:
  what is assumed is that the global `Array`'s `isArray` is the native one,
  and that the objects owning the array store key are JavaScript's arrays,
  which holds of every object the model allocates and is assumed of every
  object a program receives. `e instanceof Array` is the same test, which
  assumes further that every array a program receives is of its realm and
  that no object but an array inherits from `Array.prototype`.
- In the SKJS test environment ([Global values](#modules-and-code-units),
  "The SKJS test environment"), SKJS's import stubs describe the modules a
  test imports, and `skjs-environment.d.ts` the host's `process`,
  `__SKJS_show` and `__SKJS_show_expanded`, as SKJS's builtins stub declares
  them. These are premises of a coverage result only; `check.mts` on its own
  uses the project it is given.
- A value whose trusted declaration types it `Function`, an imported one or a
  library member's, has call or construct code
  ([Library types](#library-types)). TypeScript also admits an object that
  merely has `Function`'s members; a program's own such value is refused, an
  assumed one is not checked.
- `async` and `await` are trusted steps
  ([Async functions and await](#async-functions-and-await)): awaiting a
  `Promise<T>` yields a `T`, other jobs running meanwhile as during any call;
  an async function's promise settles to the primitive its body returns, or
  to `undefined` when the body completes. Awaiting a rejected promise throws
  its reason, which the safety theorem admits as an outcome
  ([Throws](#throws)). Nothing models the job queue or a promise that never
  settles. The assumption enters every
  result as a premise: a unit that awaits or returns from an async body has
  input slots `%Await%`, `%AsyncReturn%` and `%AsyncComplete%` at their
  declared signatures, and the safety theorem holds for every environment
  meeting them, as for an imported value's declared type. `Promise.resolve`
  meets the last two, and `Promise.all` meets `%PromiseAll%`: an array of
  promises gives a promise settling to the array of their values
  ([Library globals](#library-globals)). `Promise.reject` meets
  `%PromiseReject%`, a promise that rejects, and `new Promise` meets
  `%NewPromise%`: it calls the executor at once with functions that settle
  the promise to the primitive given, or reject it.
- A `for...of` loop over an array steps the array's iterator
  ([Loops over arrays](#loops-over-arrays)): `%Iterate%` at its declared
  signature is an input slot of every unit with such a loop, yielding each
  element below the array's current length in turn, then `null`.
- A `for...in` loop visits keys, each a string, of any value
  ([Statement forms](#statement-forms)): `%ForIn%` at its declared signature
  is an input slot of every unit with such a loop.
- **Trusted steps may throw.** A trusted step's contract is a safety
  promise, and safety admits a throw ([Throws](#throws)): an imported or
  ambient function, a library global or prototype member, `%Await%`,
  `%AsyncReturn%`, `%AsyncComplete%`, `%Iterate%` and `%ForIn%` are assumed to
  return a value of their declared result *or throw*, never to return a wrong
  value. This assumes less than before, when a trusted step was assumed not
  to throw; `await` of a rejected promise throws, as JavaScript's does. A
  thrown value is assumed to be a value, of any type: a handler binds it at
  `unknown`.
- Code outside a unit adds keys to a dictionary it holds at a mutable index
  signature only at that signature's contract; the calculus has no step that
  adds a key ([Writable string index signatures](#writable-string-index-signatures)).
- The runtime with a sound service binding
  ([`upstream-sound`](ocaml-producer/upstream-sound/tsconfig.json)) meets its
  declarations, like any imported value's: `runService` passes `createGraph`
  an `InputCollections` whose `get(definition)` returns the input collection
  the runtime built from that definition, at its key and value types (the
  runtime's `as EagerCollection<K, V>`), and throws for a definition the
  service does not declare. A client can write that call, with a definition
  it constructs itself (`inputs.get(new InputDefinition<string, number>())`):
  it type-checks and throws, which is an outcome, not a value at a wrong type.
  Reading an undeclared input of the service, `this.inputs.input3`, does not
  type-check. It also constructs each resource class with the request's
  parameters, a `Json`, and calls `instantiate` with what `createGraph`
  returned, as `ResourceClass<ResourceInputs, Json>` states.
- Lean's kernel, compilation infrastructure and the executed checker are correct.

For the stateful in-memory interface, `accept` checks the exact requested entry
contexts and expression-result annotations against the certificate, then invokes
the graph checker. This closes substitution of a different request _within that
interface_. It does not prove source extraction or the meaning of external JSON.

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

## Source integration

[SourceExtraction.lean](lean/Verification/Model/Source/SourceExtraction.lean)
connects independently parsed source and actual SKJS exports to the stateful
consumer. It accepts primitive, object and bounded callable parameters, initialized `const` declarations,
nested boolean branches, block-bodied `while` loops and returns, with variables, null/undefined/boolean literals,
plain `{ value: e }` allocation, `.value` reads and `.value = e` assignments,
and the bounded local closures and calls described below. Every syntactic exit
path must reach an explicit return; loops may diverge.
It rejects active-name shadowing, calls to named top-level functions, statements after
an explicit return, and unsupported types. The parser drops dead code it can
prove unreachable before Lean sees it ([Statement forms](#statement-forms)).
The identity scheme `id<T>(x: T): T { return x }` is checked under a rigid
parameter and omitted from the graph request; the same path admits variable-copy
bodies with distinct parameters and directed dependent bounds. See [GenericSource.lean](lean/Verification/Model/Source/GenericSource.lean).
A declaration applied to an argument over the function's rigid binders is
expanded from its source equation before that check: parameters, functions and
arrays become rigid forms, and parameter-free parts lower to graph rows (see
[DeclarationGraph.lean](lean/Verification/Model/Source/DeclarationGraph.lean)). This
is one path for every declaration, local or imported; a record over a rigid
binder stays outside the rigid checker. Generic declarations applied to ground
arguments use the same graph meaning as other declarations. The declaration document retains each
parameter's source bound and trailing default. Application fills omitted
arguments in declaration order, substitutes earlier arguments into later
defaults and bounds, and checks each resulting inclusion with a
`PositiveCertificates` proof before deriving the instantiated graph clause
from the source equation. The OCaml producer may propose a matching row, but
cannot supply the equation or waive a bound. A generic application with
methods, which recursion goes through, is one row per declaration and
arguments for the module ([one row per application](#one-row-per-application)),
so a recursive family of applications is a finite graph; this finite-ground
path does not prove a universally quantified imported declaration body.
An interface's `extends` clauses are retained as source reference edges, each
resolved by TypeScript like any other reference. Lean interprets the
local and inherited contracts together (`inheritRows`): an interface is the
meet of its own clauses with each base's, the conjunction heritage means,
with its own members first, so a member it overrides is the one read. Object
clauses meet on one object ([POSITIVE-TYPES.md](POSITIVE-TYPES.md#conjunction-and-normalization)):
their first invariant operands are one record, and the meet is a dictionary
when either side has an index,

$$
\mathsf{inherit}(c_o,c_b)=c_o\wedge c_b,\qquad
\mathsf{Obj}(\varphi_o\vec\varphi_o;\psi_o;\overline{D_o};\ldots)\wedge\mathsf{Obj}(\varphi_b\vec\varphi_b;\psi_b;\overline{D_b};\ldots)
=\mathsf{Obj}((\varphi_o\varphi_b)\vec\varphi_o\vec\varphi_b;\psi_o\psi_b;\overline{D_o}\,\overline{D_b};\ldots).
$$

The dictionary's index views constrain every present field, the named
ones included, which is TypeScript's requirement that an interface's members
meet an inherited index signature; `interface Collections extends
NamedEagerCollections` is such a dictionary, whose named collections the read
rules see. The same meet is a source intersection's meaning (`meetRow`), so
`Serializable<T> = T & { readonly [k: string]: Json }` applied to a record is
one dictionary of the record's members (see
[Record values as `Json`](ocaml-producer/README.md)). TypeScript
also gives a type literal an implicit index signature, so it accepts a record
type where such an interface is expected; nothing here does, since a record's
contract states nothing of its other keys (`invalid-sum-collections`,
`invalid-sum-record-json`). OCaml's
view of inherited fields and intersections is a candidate hint only: it merges
disjoint fields and at most one index signature, and refuses or approximates
the rest. The acceptance path never trusts an OCaml-flattened
interface equation.
Supported interfaces and aliases declared in the checked file now enter that
same source declaration graph as imported declarations. A local root names its
declaration directly; an import root names the declaration TypeScript binds the
imported name to. General ground aliases
feed the same Lean graph lowering. Admitted identity and mutable-box aliases
use specialized substitution for ground and rigid applications alike, derived
from the source equation with no parser-authored alias body. Function
annotations are written in the same source type terms as declaration bodies,
read by one parser ([type-term.mts](tools/type-term.mts)); a reference in an
annotation names the declaration TypeScript resolved. Lean converts each
annotation once, in `DeclarationGraph.prepare`, to the claim form the source
readers take, and a claim-shaped annotation in the source tree is refused.
Declaration location itself has no separate type meaning in the admitted
fragment.
`T extends boolean` is an assumption in `Δ`; returning `x` at `boolean` is
transport along `SubP`. A generic body may copy `T` through annotated or inferred `const`
bindings and extra parameters, with bounds to an earlier parameter or any
ground type: `DeclarationGraph.prepare` lowers a ground bound, whatever its
source form, to graph rows once, and the checker reads it as a ground direct
type. Parameters and results may be unions mentioning a binder, `string | T`,
and a body may fall off its end, returning `undefined`. Annotation and claim
alike reach the checker through `Ty.mkUnion`, which only reorders, flattens,
removes duplicates, merges the ground members' labels and absorbs a member
`unknown`, each of which keeps the union's meaning; it is part of the trusted
annotation lowering, not a judgment. Records, tuples and
object literals over a binder stay outside. The direct type language has no
record; and graph evidence certifies a body at the graph's own assignment of
its parameter rows only (`meaning G S = mixedValues G G.env S`), while callers
rely on every admissible assignment, which would need the evidence checker
proved independent of that assignment (`accept {G with env := η}` is not
definitionally `accept G`, and no theorem relates them yet). This is a
source-checker coverage limit, not a restriction of the rigid-bound semantics.
See [GenericSource.lean](lean/Verification/Model/Source/GenericSource.lean).

[SourceTypes.lean](lean/Verification/Model/Source/SourceTypes.lean) translates
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
`return`. A `readonly` field is a view: a read capability at a sound upper
bound on the location's contents, which withholds writes through that view and
never retypes the backing invariant, so another alias may still mutate the
object. Runtime
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
in [BranchRefinement.lean](lean/Verification/Model/Programs/BranchRefinement.lean),
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
[CellClaims.lean](lean/Verification/Model/Programs/CellClaims.lean). SKJS exports
a bounded record with separate read/write types per field, optionality and
object-mode flags. Synthetic index markers are recorded separately from runtime
permissions; real indexes remain unsupported. The Lean gate requires at least one
required field, distinct field names, and equal read/write contracts per field
after lowering to the same graph table. Field names come from the program; none
is privileged. A mutable Boolean
field passes; a readonly Boolean field has `never` writes and fails this
particular invariant-cell gate. Readonly objects need a different capability
interface; this rejection does not mean they are unsafe.

This restriction is specific to the invariant-cell translation of SKJS record
claims. The source fragment and OCaml producer separately support a readonly
string index signature as a dictionary view: every present property must meet
the value contract, while a missing property reads as `undefined`. This view
does not justify writing through the index.

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
is refused before proof search. Object-valued parameters, including nested
objects in callable operands, use this same interpretation; this does not
establish contracts for unchecked JavaScript callers.

Object branches are exported faithfully as separate atoms in the existing union
format. [CellUnion.lean](lean/Verification/Model/Types/CellUnion.lean) validates
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
independent consumption. [Fragment.lean](lean/Verification/Model/Source/Fragment.lean)
decodes the source AST and routes record types through the contract gate. Every nested expression retains
its own supplied claim. Expression lowering saves intermediate values in
anonymous slots and evaluates the receiver before the RHS. A write uses the
existing calculus rule, then returns the saved RHS to match JavaScript assignment
semantics; temporary slots are discarded by explicit edge maps. An execution
regression checks the extracted alias-assignment graph's heap and result.

Closure contracts are decoded by
[Fragment.lean](lean/Verification/Model/Source/Fragment.lean).
`callableType` checks ordered required-parameter signature shapes and recursively lowers primitive
and callable arguments and results, including every union and overload arm.
Bodies compose literals, variables, cell allocation, reads, assignments and
calls, including nested expression arrows.
An internal expression claim can differ from the declared result: both are
checked independently.

[ExpressionClaims.lean](lean/Verification/Model/Programs/ExpressionClaims.lean)
checks supplemental sequents for every closure-body expression, using its exact
lexical context, lowered term and supplied type. Source annotations produce
additional result obligations. The source consumer reconstructs this ordered
list, requires exactly one proof per entry, and checks each using the existing
program typing rules. `checkRequests_obligations` proves those sequents derivable;
the whole-program certificate separately supplies execution safety. These
supplemental proofs do not establish source semantic preservation: attaching
the right terms and contexts remains part of the trusted compiler.

The source closure becomes an ordinary lambda over the captured environment.
Its receiver occupies slot zero and its parameter slot one; captured bindings
shift by two. Calls evaluate
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

`e as const` is the same node with no annotation (cast kind `const`): it
asserts nothing, and asks for the operand's literal types, which TypeScript
gives it and the producer claims. The producer builds the operand at its
*const type* and claims the cast there:

$$
\mathsf{const}(\ell)=\{\ell\},\qquad
\mathsf{const}([e_1,\ldots,e_k])=\mathsf{readonly}\;[\mathsf{const}(e_1),\ldots,\mathsf{const}(e_k)],
$$
$$
\mathsf{const}(\{f_1:e_1,\ldots\})=\{\mathsf{readonly}\;f_1:\mathsf{const}(e_1),\ldots\},\qquad
\mathsf{const}(x)=\Gamma(x),\qquad
\mathsf{const}(e\;\texttt{as const})=\mathsf{const}(e),
$$

for a literal $\ell$, and refuses any other operand, as TypeScript does. Lean
checks the operand's allocation at that claim and the cast's claim from the
operand's, so the const type is a proposal like any other: a readonly tuple
is not the mutable tuple of its elements (`invalid-as-const-readonly`), and
an element is its literal (`as-const`).

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
before it. Patterns nest, take holes and an array rest, and bind parameters;
[Patterns](#patterns) states the whole form. `let` patterns and patterns beside
other declarators stay gated. Local annotations are separate obligations;
bindings retain the initializer's claimed precision.

Arrays and tuples use an object with an internal store of element locations.
Writable tuple positions require the backing invariant exactly. Readonly tuple
positions require only that the backing invariant implies their read type,
so a readonly array can widen element types without changing any location.
The readonly outer store field prevents replacing the store through that view;
the readonly inner contract independently prevents element writes. Neither
permission may be recovered by coercing a view to a writable contract.

A source numeric key must be proved to be one valid array-index singleton.
An arbitrary number could name an ordinary property, which the current store
model omits. Known indices support reads, writes, growth and shared alias
identity. The internal store field cannot be accessed through a source key.
Array destructuring reads positions of any array value: the array's own
iterator is `Array.prototype`'s, the trust `%Iterate%` states for `for...of`,
and each of its steps reads the current length and the next index, which is
the read of that position where its element is bound ([Patterns](#patterns)).
A non-array iterable is refused.
Required, optional and rest positions have distinct store contracts; a missing
optional/rest position reads undefined. Source arrays in this slice are plain
data arrays, without inherited indexed properties or accessors; supporting
those requires the general property-operation contracts.

Sequential composition uses the
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
cell is a fresh allocation, so its location differs from every field that each
record of an older binding named when the cell was allocated (whatever a later
test narrowed the binding to), and from every field of a later cell or of a
constant bound to an object literal allocated after it; the entry restates
that timeless fact. An object a later call returned may be any object, so no
link to it is stated. The consumer enforces this independently of the
producer. Expression-result claims
are checked local obligations within a statement, where effect rules can derive
postconditions. Loop heads use supplied interfaces; every backedge must establish
them. No loop invariant is inferred.

A source ternary branches in the graph like an `if` statement, so an effect in
its condition or an arm is a node with its own knowledge. Each arm starts in
the condition's refinement of its context, and an immutable binding the arm
reads before any branch of its own holds what the producer claims that read
at: the edge from the condition checks it as it checks a statement entry's
claims (a tag slice, a field slice, a present key). Where paths meet at a
point that states no requirement, what each knows of one location is joined
(`HeapKnowledge.meet`); every edge is still checked. Element access reads
or writes the field the key's claimed string singleton names, after the
receiver and before any right side, and the key keeps its own obligation.
On a receiver claimed only at records (no array store, no primitive), a
number singleton key names the field its `ToString` spells, since
`ToPropertyKey` converts it so: `o[0]` reads `o["0"]` and `o[2.5]` reads
`o["2.5"]`, and the two zeros spell `0` (`keyField`, with `numberToString`,
JavaScript's `Number::toString`). A key of several singletons names several
fields and is refused.
Writes establish new contents for recorded aliases where the value written is a
known primitive, keep facts about cells a distinct-location link separates from
the written one whatever is written, and discard other heap facts; two
parameters carry no such link, so a write through one forgets what was known
about the other. Ordinary calls discard heap observations and read
links: a callee may write any location its operands reach, a cell no closure
captures included only if some value reaches it, and the model does not state
which locations a value reaches (its record types admit objects with fields
at any location, so a fresh cell cannot be shown unreachable from them). Immutable values and
slot equalities survive. Boolean guards refine current cells through checked
read links, including links carried through receiver temporaries; a strict
comparison does so when the other operand's claimed type is a singleton and
the operand is effect-free, a literal, a name or a field read, never a call,
or is a union of singletons tested one at a time
([strict equality](#strict-equality-and-tag-narrowing)). Ordinary
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
Source labels, `do…while` and loops inside closures remain gated; `for...of`
over an array reuses this head, its step a trusted intrinsic
([Loops over arrays](#loops-over-arrays)), and `for` adds an update run on the
way back to it ([Statement forms](#statement-forms)). Even a syntactically always-true loop currently needs an
explicit continuation for its false edge. Acceptance is safety, not termination:
a well-typed loop may run forever.

The supplied head is the OCaml producer's proposal, and what it claims a cell
holds there is found, not assumed: the producer runs the body (discarding what
the run claims) from a candidate head, starting at the entry, and joins what
the update leaves for the head with the entry, until the head is stable (a few
rounds; otherwise, and wherever the condition or the body may write a cell
unseen, each assigned cell is claimed at its contract). The update
runs from the join of the body's end and its `continue`s, and the loop is left
from its head or by a `break`, with the join of those. So `y = b; y = a` in a
body leaves `y` holding `"a"` at the head (`loop-head-contents.ts`). Lean checks
the head against the entry and every back edge, so a wrong proposal is refused
there (`invalid-loop-head-contents.ts`); no rule or trust is added.

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
claims or retain an obsolete mutable-field refinement. It finds each binding the
destination keeps by its descriptor (name and span), and by name only where no
descriptor matches: a parameter may hide a module constant of its name, and
the constant keeps its own slot while a test narrows the parameter's
(`shadowed-module-constant.ts`). The map is a proposal the edge check
validates.

Already-known immutable Boolean singleton facts are preserved when forming a
branch map, rather than overwritten with an opposite-branch witness. This avoids
unnecessary rejection on impossible edges and uses existing transfer rules.
Unlabeled transfers are supported, and a `break` carrying the label of an
enclosing labeled block, which only a lowered `switch` makes; source labels and
transfers outside a loop remain gated, and statements after an unconditional
transfer are dropped as dead code ([Statement forms](#statement-forms)).

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

Covering matches one source clause against one _single_ target clause. A source
clause can be contained in the union of several target clauses without being
contained in any one of them, and no rule sees that.

The `bool` instance of this is closed. `bool` is the only clause of the language
whose inhabitants are a finite set that is not already a singleton, so it is the
only one that decomposes syntactically, and splitting a source `bool` into the
pair of singletons before matching keeps `Covers` clause-to-clause while letting
one source clause be discharged by several target clauses. The rule is specified
in [POSITIVE-TYPES.md](POSITIVE-TYPES.md). SKJS gets the same answer by
normalising `bool` to `true | false` before comparing, and does so _before it
exports claims_, so no source file can carry the distinction: the guards beside
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
  decomposes an arrow domain by _label list_. A `bool` domain that must be
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
applies to every measurement made with the producer: a `reject:` means _no
derivation was found_, not _no derivation exists_, so a rejection is evidence
about the rules only once the shape needed has been ruled out by hand.

## SKJS is frozen

Past the tag `skjs-frozen`, the parser → OCaml producer → Lean pipeline is the
one that moves. The SKJS producer, the claims converted from it, the
TypeScript-checker claims and the suites built on their fixtures stay as they
were at the tag and are revisited later; `verification/run.sh` runs them only
with `--suite all`. What changes first is arrays: past the tag an array holds
`Array.prototype`, and a producer that still builds the old array type is
refused, since its table reserves no row for `ArrayProto`.

## Modules and code units

A source file is a module, and the module is the unit of verification. A file
used to be a list of functions, each a closed program over its parameters.
That stops at the first sibling call, and module code and classes are not
functions at all.

**Structure.** JavaScript instantiates a module's function declarations
before anything runs, then evaluates its other top-level code once, in order.
The Fragment follows that: `functions` are the hoisted declarations, and
`init` is the ordered top-level code (constant bindings and expression
statements; class declarations later, since a class binding is initialized
where it is written, not hoisted).

**Code units.** Obligations stay per code unit, so a failure points at one
place: each function, the module initialization, and later each constructor
and method. A unit is checked against its signature in the module's scope: a
module function at its annotated signature (a source-fixed slot no producer
claims and no assignment reaches), a module constant at its annotation or,
without one, at the initialization unit's claim for its initializer, which
that unit checks where it binds the constant. Claims
are per unit, keyed by source identity.

**A module with no function.** A module whose only code is its
initialization, constants, classes and top-level statements, is a program
like any other: verifying it is checking its initialization unit, the one
unit it has. With $F$ the module's functions, $I$ its initialization code and
$\Gamma_M$ the module's scope,

$$
\frac{\forall f\in F.\;\Gamma_M\vdash f\quad
      (I\neq[\,]\Rightarrow\Gamma_M\vdash I:\mathsf{undefined})\quad
      F\neq\emptyset\lor I\neq[\,]}
     {\vdash M}\ \textsc{module}
$$

where $\Gamma_M\vdash I:\mathsf{undefined}$ is the initialization unit's
check, a body with no parameters that completes with `undefined`, with its
initialization order (below). A module with neither runs nothing and states no
claim; it is refused (the parser's gate refuses it first, "no functions in
file"), so an acceptance always checked some code. A class's methods are
closures its initialization allocates, so a class-only module's methods are
checked in that unit. Before this, a module needed a function, and a
module of constants or classes was refused whatever its code.

**Generic module values.** A generic module function is certified for every
admissible instantiation by its own unit, and a generic class by the
initialization unit that declares it ([generic classes](#generic-classes));
a generic imported value is assumed at its declared type. A unit that calls
or constructs one gives its slot the instances its calls name. Each call's type arguments must be ground and name exactly its
binders; the signature and bounds are then read from the source terms with the
binders fixed to those arguments, so a declaration applied to a binder is an
ordinary ground application, and each bound must hold by the graph's certified
subtyping. An intersection in the signature whose operands are ground once
the binders are fixed, `deepFreeze<T>(value: T): T & DepSafe` at `T := Todo`,
is the graph's meet of those operands (`meetRow`, distributing over DepSafe's
arms), the meaning every intersection has; one still over a binder at a
non-record operand is refused. Explicit type arguments on the call fix its
instance ("Explicit type arguments", below).

An array literal passed where a binder bounded by a tuple is expected,
`exact<K extends [0, 1]>(x: K)` called with `[0, 1]`, is built at that tuple,
as TypeScript types it by the constraint, so the binder is instantiated at the
tuple and not at `number[]`. The bound is only the literal's contextual type:
the instance is checked against it like any other (`invalid-tuple-constraint`).
Other actuals at a binder are typed on their own, as before, since typing them
at the bound would change the instances the Skip runtime's calls infer. The slot holds the instances as one callable with several
signatures. Each instance holds of the value, so their conjunction does. A
`new` with explicit type arguments, `new InputDefinition<string, number>()`,
names its instance: the parser records the arguments, the producer proposes
the instantiation they name, and it is checked as any other; Lean's term does
not carry them.

As rules over the unit's context, with $\llbracket T\rrbracket$ the graph type a
declared term lowers to and $T[\vec p:=\vec U]$ the term with its binders fixed
to ground types:

$$
\frac{x\ \text{imported, declared at}\ T\ \text{with no binders}}
     {\Gamma(x)=\llbracket T\rrbracket}\ \textsc{import}
\qquad
\frac{\begin{array}{c}
x\ \text{declared at}\ \forall\vec p\le\vec B.\,T\quad
\text{(certified by its own unit, or imported)}\\
\forall k.\;\vec U_k\ \text{ground},\ |\vec U_k|=|\vec p|,\quad
\forall i.\;G\vdash\llbracket U_{k,i}\rrbracket\le\llbracket B_i[\vec p:=\vec U_k]\rrbracket
\end{array}}
{\Gamma(x)=\bigwedge_k\llbracket T[\vec p:=\vec U_k]\rrbracket}\ \textsc{instances}
$$

where $\vec U_1,\ldots,\vec U_m$ are the type arguments the unit's calls of $x$
name and the conjunction is one callable carrying every instance's signatures
(`Scheme.moduleInstances`). The first rule is an assumption the result is
relative to; the second is sound because each instance holds of the value.

**Bigints and symbols.** The calculus has bigint and symbol values. A bigint
is its integer, which the binary operators compute with
([Numeric operators and bigints](#numeric-operators-and-bigints)); a symbol is
an opaque identity: bound, passed, stored and shape-tested, never computed
with. The graph has their families and the bigint singletons, and `bigint`,
`symbol` and bigint literal-type annotations lower to them. The heap's property keys are strings or symbols (`PropKey`), so a
symbol-keyed field is its own key: no string-keyed access reaches it and a
string index signature does not constrain it. A declaration's member `[x]: T`, where `x`
resolves to a `const x: unique symbol`, is a field keyed by that symbol. The
declaration document lists each such constant once, in `symbols`, and a key
`{"symbol": i}` is the i-th: distinct declarations are distinct symbols, as
TypeScript assumes, and that is part of the declarations' contract.
A program reads such a field as `e[k]`, where TypeScript binds `k` to a
`unique symbol` constant: evaluating the constant has no effect and yields
that symbol, so the parser writes the read as the named read of its key, a
`read` whose field is `{"symbol": i}`, and the declaration document lists the
constant. Any other element key is an index, as before. The constant may be
imported, or declared by the client, `declare const k: unique symbol`: it
runs nothing, and names a symbol rather than binding a value. A symbol-keyed write is
not in the fragment.

A client's own constant `const k: unique symbol = e` is a binding like any
other, whose value is a symbol (the annotation `unique symbol` reads as
`symbol`: which symbol it is, is the key's identity, not a type of the
value), and it names a key. Distinct declarations are distinct symbols only
where each makes its own: TypeScript also types `Symbol.for("k")`, the
registry's symbol for "k", which every constant made so holds, and any value
asserted to be one, a unique symbol. So the key's identity is what made it:
`Symbol()`, a fresh symbol, is its declaration's own; `Symbol.for` of a string
literal is that string's, shared by every constant made from it; any other
initializer is refused, since which symbol it holds is not known
(`symbolOf`; `unique-symbol-constants.ts`, `unique-symbol-registry.ts`;
`unique-symbol-shared-refused.ts`: two constants from one string are one key,
so a type naming both names it twice). A declared constant or property is
assumed to hold its own, as before. The model's value of `k` is the symbol
its initializer made, and `o[k]` reads the key; no dynamic symbol-keyed access
exists that could relate the two differently. A computed key in an
annotation's type literal, `{ [k]: T }`, is read like a declaration's
(`symbolNames` of `collectDeclarations`).

**Imported values.** A value import joins the module's scope at the type its
declaration states: a function's annotated signature, an annotated
constant's annotation, or, for a class, its construct signature, which `new`
meets.
TypeScript resolves the declaration; nothing here checks the imported code.
The declaration document lists these values, so a module's result is
visibly relative to them.

**Overloads.** A function declared with overloads, $S_1,\ldots,S_n$ with
$n>1$, is callable at exactly those signatures: an implementation's own
signature, when the declaration has one, is not callable from outside, and
TypeScript relates it to the overloads only loosely. The value meets every
overload, so its type is their conjunction, one callable carrying each
signature, as a global's selected method is (**Global values**, below):

$$
\frac{x\ \text{declared with overloads}\ S_1,\ldots,S_n\ (n>1),\ \text{none generic}}
     {\Gamma(x)=\bigwedge_i\llbracket S_i\rrbracket}\ \textsc{overloads}
$$

Lean checks each call against the conjunction, so a call is typed by any
overload whose parameters admit its actuals; TypeScript's choice of the first
such overload is not needed, since each holds of the value. A generic
overload is refused: a declared value's binders quantify one signature.

**Ambient declarations.** A statement the module writes with `declare` states
a value's type and defines nothing: the environment the module runs in
supplies the value. It runs nothing, so it is neither a unit nor part of the
module's initialization, and the value is in scope everywhere, as an import
is. It joins the module's scope exactly as an import does, read from its own
declaration (the `ambient` roots of `collectDeclarations`,
[`declaration-graph.mts`](tools/declaration-graph.mts)), and the declaration
document lists it with the specifier `ambient`:

- `declare function f(...): R`, at its signature, or its overloads' conjunction;
- `declare const x: T`, at its annotation; `declare const k: unique symbol`
  names a symbol instead and binds no value;
- `declare class C`, at its construct signature, which `new` meets, while
  `C` as a type is its declared instance type, as for a local class.

A name that is also an interface or type alias, `interface P` beside
`declare const P`, denotes the value in a value position and the other
declaration in a type position. With $D$ the declarations TypeScript binds
$x$ to:

$$
\frac{x\ \text{bound by ambient declarations}\ D\ \text{of the module}}
     {\Gamma(x)=\llbracket\mathsf{type}(D)\rrbracket}\ \textsc{ambient}
$$

where $\mathsf{type}(D)$ is what `import` and `overloads` read from an
imported declaration, and a generic function's binders are instantiated per
call by `instances`. The rule is an assumption the result is relative to
([What remains assumed](#what-remains-assumed)).

`declare let` and `declare var` are refused where they are declared. Such a
binding is module storage that code outside the module may write at any
time, during a call the module makes included, so a read after a call may
see a value other than one a test established. The fragment has no module
storage (a module-level `let` is refused for the same reason), and reading
the binding as an immutable assumption would let a refinement survive a call
that invalidates it.

**The standard library.** Library contracts are TypeScript's own
declarations, read like any library's: a type name the module neither imports
nor declares, such as `Promise`, is a root when TypeScript binds it to a
global declaration. Reading them needs the forms those files use:

- An interface declared several times is one interface with every
  declaration's members, identified by the first, as TypeScript merges it.
  The parts must agree on their type parameters and name no member twice.
- A well-known symbol key such as `[Symbol.iterator]` is a symbol key: the
  `readonly iterator: unique symbol` property of `SymbolConstructor` is its
  identity.
- A declaration's `any` is `unknown`. What the library returns at it is
  assumed to be anything, and what it accepts at it may be anything.
  TypeScript's `any` also converts to every type, and nothing here inherits
  that; the checked module's own annotations may not write `any`.
- A generic application with methods is one row for the module, whatever
  names it: `finally(): Promise<T>` in `Promise<T>`, a producer's reserved
  row, a method's annotation and its class's declared instance type
  ([one row per application](#one-row-per-application)). A claimed parameter
  or result type is still compared by meaning, identical rows or inclusion in
  both directions by certificates the proved checker accepts, since a claim
  may name another row with the same clauses, or a narrower type.

A claimed type $C$ is within the annotation's $A$ (`within`) when

$$
\frac{\operatorname{canon}_G(C)\subseteq\operatorname{canon}_G(A)}{C\sqsubseteq_G A}
\qquad
\frac{\operatorname{check}(G,C,A,p)=\mathsf{true}}{C\sqsubseteq_G A},
$$

and $C\sqsubseteq_G A$ implies $\llbracket C\rrbracket_G\subseteq\llbracket A\rrbracket_G$
(by `check_sound` for the second rule; the first compares rows with identical
clauses, which denote the same type). A top-level function's claimed
parameter and result types are the annotation's (`sameMeaning`):

$$
\frac{C\sqsubseteq_G A\quad A\sqsubseteq_G C}{A\simeq_G C},
$$

and $A\simeq_G C$ implies $\llbracket A\rrbracket_G=\llbracket C\rrbracket_G$, so
the claim may replace the annotation. A closure's claimed signatures, a
method's among them, and a class's claimed construct signatures need only be
within the source's: each claimed parameter $D_j\sqsubseteq_G A_j$ for the
annotation's $A_j$ (for a closure, at the positions it takes). The body is
checked at each claimed signature's own types, so this comparison is not what
makes the claim sound; it keeps a producer from advertising a signature the
source does not state. Comparing by meaning rather than by label is what lets
a claim name the producer's own row for a declared application.

#### One row per application

A generic application with methods, $D\langle\vec U\rangle$ where $D$'s
equation mentions its receiver, is one row for the whole module: the memo
$\rho$ (`Memo.applications`) maps a declaration and its arguments' key to the
row. Rows with identical clauses denote the same type, so arguments are
compared by $\mathsf{key}$, each label its row's clauses, except an
application's row or an empty row, reserved and not yet filled, which is its
label:

$$
\mathsf{key}(\vec U)=\bigl(\{\,k(l)\mid l\in U_i\,\}\bigr)_i,\qquad
k(l)=\begin{cases}l & l\ \text{an application's row, or empty}\\ G(l) & \text{otherwise.}\end{cases}
$$

A producer's reserved row for $D\langle\vec U\rangle$ (`"applications"`) is
in $\rho$ from the start, so the declarations' own equations name it too. That
holds for a reserved application without methods as well: a recursive alias
the module names (`type A<T> = { next: B<T> }` with `type B<T> = { prev: A<T> }`)
closes at its row, where before it was refused.
Otherwise the first lowering to meet the application gives it a fresh row
$r$, records it, and lowers $D$'s equation at $\vec U$ with $r$ for the
receiver, **from an empty visit**: no enclosing declaration and no enclosing
method's binders (`groundApplication`):

$$
\frac{\rho(D,\mathsf{key}(\vec U))=r}{\llbracket D\langle\vec U\rangle\rrbracket=[r]}\ \textsc{app}
\qquad
\frac{\rho(D,\mathsf{key}(\vec U))\ \text{undefined}\quad
      |\mathsf{reach}(\vec U)|\le 32\quad r\ \text{fresh}}
     {\rho(D,\mathsf{key}(\vec U)):=r\quad G(r):=\mathsf{lower}_\emptyset(\mathit{eq}_D[\vec U,\mathsf{self}:=r])}\ \textsc{app-new}
$$

Every row of $D\langle\vec U\rangle$ is the lowering of one equation at one
argument list, so every mention denotes the same type. Lowering from an empty
visit makes that lowering a function of the application and the memo, never
of the path that met it first: a recursive family of applications
(`EagerCollection<K2ᵃ, V2ᵃ>`'s `map` returning `EagerCollection<K2ᵇ, V2ᵇ>`, and
back) closes into a finite graph where each application has its whole
equation, and two applications that differ by a renaming of binder rows are
related by an instance table ([instances of a scheme row](POSITIVE-TYPES.md#instances-of-a-scheme-row)),
which closes because its contexts are finitely many. Before this, lowering
unfolded a declaration at most three times along a path, so the scheme's
result and the type it was compared with were cut at different depths and
could not be matched.

The unfolding terminates. Binder rows are finitely many (colours, below), and
$\mathsf{reach}(\vec U)$ is the rows the arguments reach, an application's
row reaching its arguments rather than its equation, a declaration's,
primitive's or binder's row nothing further (`reach`): a function of the
arguments. Arguments that keep growing (`Pair<T>`'s `m<U>(): Pair<[T, U]>`)
pass the bound, and the application is refused; the method that named it
stays opaque. A declaration without methods is expanded inline, unless it
reaches itself through references (`recursiveDeclaration`,
`type List<T> = null | { head: T; tail: List<T> }`): then its application is a
row of its own, given before its equation is lowered, as an application with
methods is, so `List<number>` and `List<T>` are finite. A recursion through
declarations is otherwise refused after three expansions within one
application's equation (`applicationDepth`). A source annotation applying a
recursive declaration to a generic unit's binder has no finite claim-form
expansion; it is the application row at the binder's parameter row
(`SourceTypes.binderRow`), which only the graph checker reads
([generic bodies](#generic-bodies-are-graph-requests-over-parameter-rows)).

A declaration's row is a name, not a representative for its clauses: the row
for a type is the first row with exactly its clauses that is not a
declaration's (`useRow`), so `number` is the producer's `number` row wherever
it is lowered, whether `type int = number` has been filled yet or not. A
source annotation's ground type arguments are lowered as declarations' terms
are, so an annotation names the application its declaration names.

**Global values.** A value name the module neither imports nor binds is a
global when TypeScript binds it to a global variable, such as Node's
`declare var process: NodeJS.Process`. A name the module binds anywhere, as a
parameter, variable, function or class, is not looked up, so a shadowed
global stays unbound. Its contract is the project's own type
packages, as the program's build has them: the upstream fixture names
`types: ["node"]`, as Skip's shared tsconfig does, and installs `@types/node`
at the version Skip's lock pins (`upstream/package.json`; `test.mts` pins the
two files `process` is read from). No overlay restates them. Like an import, a
global joins the module's scope as an assumption the result is relative to,
and the declaration document lists it among the values, with the specifier
`global`.

A runtime's global interface is large, and most of it reaches declarations
the fragment cannot state (`NodeJS.Process` has about a hundred members), so a
global is read only at the members the module's references select
(`selectGlobal` in `declaration-graph.mts`):

- Every reference reads a member by name, `process.m`, or is called,
  `BigInt(v)`. Any other use, such as `const p = process`, is refused.
- An interface of the variable's name, `interface BigInt` beside
  `declare var BigInt: BigIntConstructor`, is the name's type meaning, which
  a value reference does not denote; any other declaration of the name is
  refused.
- A call of the global is the call signatures of the annotated interface
  TypeScript resolves the module's calls to, read as a method's overloads
  are, with no receiver. A generic one is refused.
- TypeScript resolves each name on the interface the variable is annotated
  with, through its merged declarations and its heritage, a namespace-qualified
  annotation included.
- A method is the overloads TypeScript resolves the module's calls to, and its
  reference must be called: methods are host-relative. A `this` result is the
  selection itself. A generic, optional or modified method is refused.
- A property is its signature as declared, read as any declaration's is
  (`process.env` is `ProcessEnv`: a writable string index from `Dict<string>`
  beside the optional field `TZ`).
- A member declared in a generic base interface is refused, since reading it
  would bind that base's parameters.

The selection is a definition of its own, keyed by the variable's first
declaration, and the global's type is a reference to it. With $I$ the
annotated interface, $M$ the names the module's references read, $O_m$ the
overloads TypeScript resolves the calls of method $m$ to, and $C$ the call
signatures it resolves the calls $x(\ldots)$ to:

$$
\frac{x\ \text{a global variable annotated}\ I\qquad
      M=\{m\mid x.m\ \text{occurs}\}\qquad
      \text{every occurrence of}\ x\ \text{is some}\ x.m\ \text{or a callee}\qquad
      O_m\subseteq\mathsf{overloads}_I(m)\qquad
      C\subseteq\mathsf{calls}_I}
     {\Gamma(x)=\llbracket\mathsf{sel}_{M,O,C}(I)\rrbracket}\ \textsc{global}
\qquad
\llbracket I\rrbracket\subseteq\llbracket\mathsf{sel}_{M,O,C}(I)\rrbracket .
$$

The inclusion is why the rule assumes no more than the declaration does: a
record says nothing of the keys it does not name; a value meeting every call
signature of $I$ meets those in $C$; a method member meeting every
overload of $I$ meets the overloads in $O_m$; a method's receiver is its host
([Method members are host-relative](#method-members-are-host-relative)), so
leaving members out narrows no receiver; and a `this` result is the host, which
is in $\llbracket I\rrbracket$. Which overloads TypeScript picks decides only
how weak the assumption is: Lean checks each call against the selected
overloads, with the declarations' `any` read as `unknown`. So
`on(event: string | symbol, listener: (...args: any[]) => void): this`, the
overload a `string` event resolves to, calls its listener with unknown
arguments, and a `(code: number) => undefined` listener, which TypeScript
accepts through `any`, is refused (`invalid-sum-process-listener.ts`). A
literal event such as `"SIGHUP"` resolves to `on(event: Signals, listener:
SignalsListener): this`, whose listener takes the signal's name
(`sum-process.ts`). The project's type packages and TypeScript's member and
overload resolution join the trusted front end; the selection itself adds no
meaning Lean does not check. A global both called and read through a method
in one module, `Symbol()` beside `Symbol.for(k)`, is a callable object with
methods, which the graph has no clause for; Lean refuses it. A global the
standard library declares is read through a reviewed overlay
([Library globals](#library-globals)).

**The SKJS test environment.** SKJS checks its own tests (the corpus
[SKJS-COVERAGE.md](ocaml-producer/SKJS-COVERAGE.md) measures) with
`--import-stubs import-stubs`: a bare import specifier resolves in that
directory, and its builtins stub, `import-stubs/@types/skjs/index.d.ts`, is
the global environment in place of TypeScript's library. The pipeline gives a
test the same environment through a project,
[`ocaml-producer/skjs-environment`](ocaml-producer/skjs-environment/tsconfig.json),
which the coverage run extends once per derived file:

- `paths` sends every bare specifier to `import-stubs/*`, so an import from
  `"@skipruntime/core"` or `"for-tests"` is the stub's declaration, read as
  any import is (**Imported values**, above).
- The builtins stub cannot be loaded beside TypeScript's library, which it
  replaces (it redeclares `Iterable`, `ReadonlyArray`, `Function`), so the
  library stays, and `skjs-environment.d.ts` restates the stub's globals the
  library lacks, each a global variable annotated with an interface, read by
  **Global values** at the members and calls a module selects: `process` at
  SKJS's stub type for it, and `__SKJS_show`, `__SKJS_show_expanded`; and
  its two type aliases the library lacks, `StringRecord<V>` as the stub
  states it and `Closed<T>` (below).
- `__SKJS_show(e, "T")` is SKJS's test assertion that it infers `T` for `e`,
  a statement about SKJS's inference rather than about the program. As a
  value it is a host function taking any value and an optional string and
  returning `undefined`: an ordinary call, so it may have effects, and a
  narrowing a call ends ends there too (SKJS exempts it; the pipeline does
  not need to). What it asserts is not read.
- `Closed<T>` is SKJS's closed object type, every key `T` does not name
  absent, a meaning SKJS's checker gives the reserved `SKJS_Closed`. It is
  read as `T`, the identity SKJS states as its reading for tsc. That promises
  less than SKJS's meaning and is true of every closed value, so a program is
  never admitted on a key's absence: `Closed<{ x: number }>` is not a
  `{ [k: string]: number }` (`invalid-skjs-environment.ts`), though SKJS
  accepts it.

As rules, with $\mathsf{stub}(s)$ the stub module a bare specifier $s$
resolves to and $E$ the environment file's declarations,

$$
\frac{x\ \text{imported from}\ s\ \text{bare}\qquad
      x\ \text{declared at}\ T\ \text{in}\ \mathsf{stub}(s)}
     {\Gamma(x)=\llbracket T\rrbracket}\ \textsc{stub}
\qquad
\frac{\mathtt{declare\ const}\ x{:}\,I\in E}
     {x\ \text{is a global variable annotated}\ I}\ \textsc{env}
$$

where $\textsc{env}$ feeds $\textsc{global}$. Both are assumptions the result
is relative to ([What remains assumed](#what-remains-assumed)).

**Generic methods.** A declaration's generic method `m<U>(...)` lowers to a
scheme row whose binders are parameter rows. Its signatures mention the
declaration's applications at its own binders (`Promise<T>`'s `then<R1>`
returns `Promise<R1>`, whose `then` binds another `R1`, ...), so binder rows are
shared, by name, and the unfolding closes up. A method's binders take the
least **colour** not free in the arguments of the application it belongs to:

$$
\mathsf{colour}(m, \vec A)=\min\{\,c<\mathit{budget}\;\mid\;c\notin\mathsf{colours}(\mathit{fv}(\vec A))\,\},
$$

and binder $k$ of $m$ at colour $c$ is one row, whoever lowers it.
`Promise<R1ᵃ>`'s `then` then binds `R1ᵇ`, `Promise<R1ᵇ>`'s binds `R1ᵃ`, and the
application memo finds `Promise<R1ᵃ>` again. A binder never takes a colour free
in what its signatures mention from outside, so no binder captures one of
another scope; the instance tables of `Sub.inst` tell the scopes that share a
binder row apart. Past the colour budget, at arguments that keep growing
([one row per application](#one-row-per-application)), and for an F-bounded
binder, the method stays an opaque member: sound, and what it was before. A rest typed
by one of the method's binders makes it a pack parameter (`...params:
Params`), which a construct type's rest may share (`new (...params: Params) =>
M`): the scheme row's variadic signature has the binder for its rest, the
binder's `Params extends E[]` bound is the element pack, and a call's
instance is the tuple of its further actuals. Two rows of one type that
differ only in the binder rows their schemes use are one type up to renaming
(`Sub.table`).

**Binders as type arguments.** A method's value binder $p$ may be an argument
of a declaration with a bounded parameter (`map<K2 extends Json, …>` returns
`EagerCollection<K2, V2>`, whose `K extends Json`). Its instances lie within its
own declared bound $B_p$, so it establishes the parameter's bound $B$ through
that one, as TypeScript's constraint does; a declared bound that is ground,
naming no parameter or binder, is the same for every scheme sharing $p$'s row:

$$
\frac{p\ \text{a value binder}\quad B_p\ \text{ground}\quad G\vdash_c B_p\le B}
     {p\ \text{establishes}\ B}\ \textsc{binder-bound}
$$

A meet row of $p$ (below) is below $p$, so it establishes what $p$ does.

**Binders met with ground types.** An intersection of a value binder with
ground types, `V & DepSafe` in `EagerCollection<K, V>` at `map`'s binder `V2`,
is a **meet row** $p\sqcap\vec c$ (`RequestJson.Row.meet`): the values of $p$
within the clauses $\vec c$ of the ground operands' meet. Lowering an
intersection $A_1\mathbin{\&}\cdots\mathbin{\&}A_n$ (`meetRow`):

$$
\frac{A_k=[p],\ p\ \text{a value binder}\qquad
      \forall i\ne k.\ A_i\ \text{of clause rows}}
     {\llbracket A_1\mathbin{\&}\cdots\mathbin{\&}A_n\rrbracket=
      [\,p\sqcap\mathsf{meet}(A_{i\ne k})\,]}\ \textsc{binder-meet}
\qquad
\frac{\forall i.\ A_i\ \text{of clause rows}}
     {\llbracket A_1\mathbin{\&}\cdots\mathbin{\&}A_n\rrbracket=
      [\,\mathsf{meet}(A_1,\ldots,A_n)\,]}\ \textsc{meet}
$$

where $\mathsf{meet}$ is `meetLists` of the operands' clauses folded from the
right, $\mathsf{meetLists}(G(A_1),\mathsf{meetLists}(G(A_2),\ldots))$, and
any other intersection (two binders, a scheme, a union holding a binder) is
refused rather than an operand without clauses being dropped. At an instance
$p:=U$ a meet row means the meet of $U$ with its clauses, which an instance
table checks as $\mathsf{meetLists}(G(U),\vec c)$ in either order
([instances of a scheme row](POSITIVE-TYPES.md#instances-of-a-scheme-row),
`meetOk`): for the binder first, as the runtime's declarations write it
(`T & DepSafe`), that is exactly what lowering the intersection at `T := U`
gives, so the image is the row the ground application already has. The meet
row is the one mechanism for every place a binder is intersected: a
declaration's parameter substituted by the binder and the binder's own
occurrences alike.

This replaces a stopgap that gave such a binder the ground operands as
conjuncts of its scheme bound and read $p\mathbin{\&}\vec D$ as $p$. That was
sound but not TypeScript's reading: `map` could not be instantiated at a value
type outside `DepSafe`. Now it can, as TypeScript allows: at
`V2 := readonly number[]` its result's values are the array's meet with
DepSafe (`sum-map-array.ts`), and at `V2 := [number, number]`, sum.ts's
`AddIndex`, `.map(AddIndex, 0)` is typed.

What the meet of a tuple with DepSafe is follows the model, not TypeScript's
guess about inhabitation: primitives meet no array, and `Managed`, a record
with a symbol key, meets the array shape as one object: the store, the
prototype view, the own-key bound and `Managed`'s key. An array owns no key
its prototype provides and may own others
([Arrays may carry other own keys](#arrays-may-carry-other-own-keys)), so that
object is inhabited, as Skip's runtime makes it by tagging frozen arrays; the
meet row does not depend on the array bound. Such a value is used exactly as
either side gives (`sum-values-tuple.ts`: its elements, `sort` and `reduce`
through the prototype, and `Managed`), and not as a number, which DepSafe
admits but the tuple does not (`invalid-sum-values-tuple.ts`). `toArray()`'s
writable array of the meet is not a writable array of tuples
(`invalid-sum-values-array.ts`), though TypeScript's covariant arrays accept
it. A record's meet with DepSafe is not empty either, since an object type
names only the keys it constrains (`sum-values-record.ts`).

With it, sum.ts's `.map(AddIndex, 0)` is typed (`sum-add-index.ts`), and so is
`map` to Serializable records (`sum-serializable-map.ts`). Every class of
`reactive-sum-sound.ts` and its `main` over an `AnySkipService` verify; the
module stops at `runService(new Service(), …)`, where sum.ts's `Service` is
not an `AnySkipService` (the service boundary, next).

**The service boundary.** `runService` takes an `AnySkipService`, the
runtime's `SkipService` at the erased collections: `createGraph` over any
`NamedEagerCollections`, resources instantiated at any `SharedCollections`.
sum.ts's `Service` is a `SkipService<Inputs, Collections, Collections>`: its
`createGraph` takes `Collections`, which require `input1` and `input2`, and
its resources' `instantiate` reads `cs.input1`. Method parameters are
contravariant ([Method members are host-relative](#method-members-are-host-relative)),
and `NamedEagerCollections` is not `Collections`, so the class is not an
`AnySkipService` at either member; TypeScript accepts it through its
bivariant method parameters. Each point is refused on its own
(`invalid-sum-any-service-graph.ts`, `invalid-sum-any-service-resource.ts`),
and a class whose members take what the erased type passes is one
(`sum-any-service.ts`): the class-instance coverage (methods as fields,
`CoversByFunction`, a dictionary of construct signatures, a writable
dictionary at the readonly optional `externalServices`) needs nothing more.

The refusal is right at the type level: a value of the erased type may be
handed any named collections. What makes sum.ts safe is a fact about the
runtime, not the type: it calls `createGraph` with one eager collection for
each key of the service's own `inputs`, and instantiates resources with what
`createGraph` returned. The generic reading SKJS's stubs give `runService`
(`runService<I, C, R>(service: SkipService<I, C, R>)`) is not that fact:
it links neither `C` to `I`, so a service whose `inputs` is `{}` and whose
`createGraph` reads `c.input1` would be accepted and fail at run time. A
sound trusted contract relates the inputs' keys and `InputDefinition<K, V>`
types to `createGraph`'s parameter, a type-level map (`{ [k in keyof I]: … }`)
the calculus does not state. Under today's binding, `runService(new
Service())` over sum.ts's `Service` stays refused, the blocker of
`reactive-sum-sound.ts`. The trusted `ResourceClass<R, never>` is related:
the runtime constructs a resource with the request's `Json` parameters, while
`never` promises it never does; a class whose constructor needs more than
`Json` would be admitted.

**A sound binding needs no type-level map.** The link can be stated
instead by the value that carries it: `createGraph` receives an
`InputCollections` whose `get<K, V>(definition: InputDefinition<K, V>):
EagerCollection<K, V>` returns the collection the runtime built from that
definition, so a collection's types are its definition's, and a service can
ask only with a definition it holds. `SkipService<InputDefs, ResourceInputs>`
then has no free collections parameter; `runService` is generic over the
concrete service, whose `createGraph` result and resources' `instantiate`
parameter are the one `ResourceInputs`, compared without bivariance; and
resources are `ResourceClass<ResourceInputs, Json>`, what the runtime does.
That runtime is checked in beside the snapshot
([`upstream-sound`](ocaml-producer/upstream-sound/tsconfig.json)), with
sum.ts as its client (`sum-sound-binding.ts`), which verifies whole: the
call's `InputDefs` and `ResourceInputs` are inferred from the service's
fields and `createGraph` as `Inputs` and `Collections`, its bounds checked
(`Inputs` ≤ `NamedInputDefinitions`, `Collections` ≤ `SharedCollections`),
and the service's instance meets `SkipService<Inputs, Collections>`
member by member. The resource bivariance TypeScript still admits under it
(a resource needing a collection `createGraph` does not return) and a
constructor needing more than `Json` are refused
(`invalid-sum-sound-binding-resource.ts`,
`invalid-sum-sound-binding-constructor.ts`). What the runtime does with
`get` is trusted ([What remains assumed](#what-remains-assumed)).

A producer names an intersection it meets without computing it: its reserved
row, in the claims' `"meets"`, is filled by Lean with `meetRow` of the
operands ([SOURCE-CLAIMS.md](SOURCE-CLAIMS.md)).

**Explicit type arguments.** A method call may state its instance,
`o.m<A₁,…,Aₖ>(…)`. The arguments are an annotation, so a requirement: the
call is typed at that instance, even where inference would find another that
fits. They instantiate the member's binders in order, its own leading, as its
declaration lists them; binders past them (for a member of `ArrayProto`, the
element binder `T`, listed last) are fixed by the receiver and actuals as at
any call. The producer proposes the read's claim at that instance; Lean reads
the member's scheme row $S$ from the receiver's contract (its own field or
view, or its prototype's), finds the instance map $\theta$ relating $S$ to
the read's claimed arrows $M$, checks it (`checkInstArrs`, whose soundness is
`Inst.mixed_sound`), and requires each explicit argument to mean what
$\theta$ gives its binder:

$$
\frac{o:O\quad \mathsf{field}_G(O,m)=S=[\forall\vec p.\Sigma]\quad
      \mathsf{checkInstArrs}(G,S,M,\theta)=\mathsf{true}\quad
      \forall i\le k.\;\theta(p_i)\simeq_G A_i}
     {o.m\langle A_1,\ldots,A_k\rangle(\vec a)\ \text{is called at its stated instance }M}.
$$

The rule only refuses. Acceptance rests on the read's own `Sub.inst` proof
and the call's typing, as without type arguments, so safety does not depend on
it; what it adds is that a stated instance is honoured. A declaration's
defaults for method binders are not read: binders a shorter list leaves are
inferred and checked like any call's, where TypeScript would fix them at their
defaults. Type arguments on an element call remain outside the fragment.

A plain call and a `new` state their instance the same way, `f<A₁,…,Aₖ>(…)`:
the parser records the arguments on the `apply` (or `new`) node, the producer
uses them instead of inference, building each actual at its instantiated
parameter, and Lean compares them with the instance the call is claimed at.
The callee is a generic module value, whose call names its instance
$\sigma$ (below), or a local quantified closure, whose elimination does; in
both, binder $p_i$ of the callee, in declaration order, must receive a type of
the same meaning as $A_i$ (`Scheme.explicitInstance`):

$$
\frac{f\ \text{generic over}\ p_1,\ldots,p_n\quad
      \text{the call's claimed instance}\ \sigma\quad
      k\le n\quad
      \forall i\le k.\;\sigma(p_i)\simeq_G\llbracket A_i\rrbracket}
     {f\langle A_1,\ldots,A_k\rangle(\vec a)\ \text{is called at its stated instance}\ \sigma},
$$

where $\simeq_G$ is inclusion both ways by the graph's certified subtyping.
The instance's bounds are then checked as for any call, so an explicit
argument outside its bound is refused (`invalid-explicit-type-argument-bound`,
TypeScript's TS2344), and an instance TypeScript accepts only by array
covariance is refused where the actual meets the invariant parameter
(`invalid-explicit-type-argument-covariance`). A local closure's substituted
bounds are checked by the same certified subtyping as a module value's.

**Constructors in the calculus.** A function's code says which of
JavaScript's internal methods it has (`Invoke`: `call` or `construct`), and
`new` is a term of its own (`construct`). So a class value, construct-only
code, is a first-class value: a plain call of it is stuck, as JavaScript
throws, and `new` on an arrow is stuck likewise. Its type is a construct
signature (the `ctors` clause, `ctorsT`), which `ctorE` gives a class whose
body is safe at each signature, and which `construct` consumes. The
promise is about the body `new` enters, one level down, so a construct
signature's variance is used only below the current level, as a call
signature's is. `[[Call]]` (`CallCode.callable`) is what the call semantics
require, so no class inhabits a call type and no arrow a construct type.

**Argument packs.** A rest parameter typed by a type parameter, as in
`map<P extends DepSafe[]>(f: new (...params: P) => M, ...params: P)`, says
the whole argument list is one thing. That thing is not a runtime value: an
argument list has its own contracts, over lists of values, and the `pack`
clause is one of them: tuple contracts on the list, each position checked at
the current level (`clauseArguments`, `ArgumentContracts.Fits`). A pack clause
has no runtime-value members. Coverage is covariant position by position
within the length bounds (`CoversPack`). A variadic signature's fixed
parameters admit the first actuals and its rest the remaining list
(`ArgsRest`), so `...xs: E[]` admits any list of values at `E` and
`...xs: [A, B]` exactly those positions, one mechanism for both. Allocating the
rest store is a step, so it consumes the approximation level the contract
itself does not (`RestCalls.argument_alloc_safe`). A spread into a rest, a rest
compared with fixed positions, and binding a variadic target read an element
rest (`restElem`). [Same-level argument contracts](#same-level-argument-contracts)
gives the semantics.

**Classes.** A class declares its instance type in the declaration graph,
and its value is a statement of the module initialization, in order. The
parser lowers it to method closures allocated once, its prototype object
holding them (`C.[[prototype]]`, a name no source binding spells, allocated
once), and its constructor, which allocates the instance, as construct-only
code (`ctor`). A prototype holding nothing of its own that `instanceof`
does not test is not allocated: nothing tells it apart from its base's, or
from none ([Guards](#guards)). A class is a value like any other, at its construct signature:
`new C(args)` (`new`) runs that code, and a plain call cannot, since calling a
class without `new` throws. An instance holds the prototype object under the
prototype key (`[[proto]]`, which no source key spells: `Fragment.sourceKey`),
as JavaScript's does, so its own keys are its fields and a method is read
from the prototype (`Step.readProto`, `memberT`'s second arm): a spread
copies the fields and not the methods, as JavaScript's does
([Object literals](#object-literals)), and `key in instance` finds a method
along the chain ([Guards](#guards)). The instance's allocation is claimed at
its exact keys, the prototype key among them: that bound says a method is
not its own, so the class's type, whose methods are host-relative members,
covers it through the function-typed fields of its prototype chain
(`CoversByProto`, [POSITIVE-TYPES](POSITIVE-TYPES.md#clause-coverage)). No
write reaches a prototype or a method.

**Class members.** The instance type (`classInstance`) states each member as
what it is at run time. `public`, `private` and `protected` are TypeScript's
alone: the member is an ordinary property, so the type states it as any other
(a `#x` member is a private slot, not a property, and stays outside). A field
`f: T`, `f!: T` or `readonly f: T` is a required field or view; `f?: T` an
optional field, of the exact meaning optional fields have
([Optional fields](#next-object-milestone)); a parameter property
`p: T` a field and `p?: T` the optional field `p?: T | undefined`, which is
what TypeScript declares. Construction then has to make the instance meet
that type, and Lean checks it does: fields are JavaScript class fields, so a
field without an initializer holds `undefined` from the instance's creation
until the constructor assigns it. `f!: T` is TypeScript's unchecked promise
that the constructor does; here the allocation is checked like any other, so
the promise holds exactly when the constructor assigns `f` on every path
(`invalid-class-definite-field.ts`), and `f?: string` left unassigned is
refused, since it is present at `undefined` (`invalid-class-optional-field.ts`;
SKJS's own tests write `f?: string | undefined` for this reason). That the key
is always present does not change the type: TypeScript lets any value with
the class's shape have it, a literal lacking the key included.

The constructor is lowered as follows. With $\varphi_0$ the entries, in
member order, of the prototype key ($\texttt{[[proto]]} \mapsto C.\texttt{[[prototype]]}$,
for a class with methods), the initialized fields ($f \mapsto e_f$), then the
parameter properties ($p \mapsto p$), $U$ the fields
without an initializer and $T_f$ each field's annotation, the constructor
`constructor(x̄) { s̄ }` is $\mathsf{class}(\vec x).\,\mathcal{C}(\vec s,\varphi_0,\varnothing)$
where

$$
\begin{aligned}
\mathcal{C}(\varepsilon,\varphi,A) &= \mathsf{alloc}(\varphi,\ \overline{f\mapsto\mathsf{undefined}}^{\,f\in U\setminus A})\\
\mathcal{C}(\texttt{this.}f\texttt{ = }e;\ \vec s,\varphi,A) &= \mathcal{C}(\vec s,\ \varphi,f\mapsto e,\ A\cup\{f\})
  && f\in U\setminus A\\
\mathcal{C}(\texttt{if (}c\texttt{) }\{\vec t\}\texttt{ else }\{\vec u\},\varphi,A) &=
  \beta(\varphi)\,;\ \mathsf{if}\ c\ \mathsf{then}\ \mathcal{C}(\vec t,\varphi',A)\ \mathsf{else}\ \mathcal{C}(\vec u,\varphi',A)
  && \text{last, assigns a field}\\
\mathcal{C}(s;\ \vec s,\varphi,A) &= \beta(\varphi)\,;\ s\,;\ \mathcal{C}(\vec s,\varphi',A)
  && \text{otherwise}
\end{aligned}
$$

and `this` occurs in no $e$, $c$ or $s$ (a statement reading `this` could
observe the instance before it is complete, `class-constructor-reads-this.ts`,
and a field assignment elsewhere reads it). $\beta(\varphi)$ binds each entry
$f\mapsto e$ that is not a literal or already bound as
`const this.f: T_f = e`, in order, a name no source binding can spell, and
$\varphi'$ reads `this.f` there: every value is evaluated where JavaScript
evaluates it, initializers first, and a statement between two assignments runs
between them. Without statements $\mathcal{C}$ is the one allocation of all the
entries. An arm without `else` is empty. Each arm of the last `if` allocates
its own instance, so the fields they share are the same expressions reached
on two paths; the producer claims such an expression once when both paths
agree on its claim. A constructor's parameters are required or optional (a
closure's `x?: T`, which binds `T | undefined`); defaults and rests are not yet
read.

**Class inheritance.** `class D extends B`, with `B` a class declared earlier
in the file, is lowered from the same parts, with the one addition JavaScript
makes: `super(ā)`, a statement of `D`'s constructor's own body, runs `B`'s
constructor on the actuals, and `D`'s instance holds the fields that made,
then its own over them. The model allocates at the end, so the base part is
`B`'s fresh instance, bound to a name no source spells, and `D`'s instance is
the allocation from parts ([Object literals](#object-literals)) that copies
it ([the lowering](PROGRAM-TYPING.md#derived-source-forms)). JavaScript runs
the same things in the same order: the statements before `super`, the
actuals, `B`'s initializers and body, then `D`'s initializers and statements;
the copy reads the base part after `D`'s own statements, and nothing else
holds it. `this` before `super(...)` throws a `ReferenceError` in JavaScript;
a throw is an allowed outcome, but the instance is allocated at the end, so
no term stands for the uninitialized binding, and it is refused (TypeScript
refuses it too). A class without a constructor has JavaScript's implicit one,
`constructor(...args) { super(...args); }`: it takes its base's parameters,
at their types, and passes them on; an actual past them reaches no
parameter of the base's constructor, which binds exactly its own, and has
no `arguments` object to read it.

- *The base part is exact.* `B°` (`B.[[class]]`) is `B`'s constructor, bound
  as the class value itself is, and claimed also at the fresh instance it
  allocates: its fields and prototype key, exactly
  ([Fresh literals have exact keys](#fresh-literals-have-exact-keys)). Its
  body is checked at that signature too (`ctorE`). So `D`'s allocation knows
  its own keys exactly, and its type covers `D`'s methods through its
  prototype, as a base class's does.
- *The prototype links to its base's.* `D.[[prototype]]` holds `D`'s own
  methods and, under the prototype key, `B.[[prototype]]`, as JavaScript's
  `D.prototype` links to `B.prototype`. A read of an inherited method, and
  `in`, walk the chain (`Step.readProto`, `keyInChain`), and `D`'s type
  covers a method as many prototypes up as it is found (`ProtoHolds`); an
  `instanceof B` of a `D` finds `B`'s prototype there. A class without
  methods of its own, which `instanceof` does not test, has no prototype of
  its own: its instances hold its base's.
- *`super.m(ā)`* is `B.m`'s closure (the one `B`'s prototype chain holds,
  `B`'s own or inherited) called with this method's receiver: `B.m.call(this, ā)`.
  The receiver is a `D`, which is a `B` by `D`'s declared type.
- *An override must be sound.* `D`'s declared type is its own members and
  `B`'s ([interface heritage](#source-integration), `inheritRows`): an
  overridden method is two member signatures, and `D`'s allocation meets both
  only where the override's parameters are at least as wide and its result
  at most as wide. TypeScript's bivariant method parameters admit a narrower
  one; that allocation is refused (`invalid-class-override.ts`).
- *Refused bases.* A class declared later, a library class (`extends Array`
  keeps its reason, [Library types](#library-types)), an ambient or imported
  class, a class value from an expression: nothing in the file says what
  their constructors allocate.

**Static members.** A static member is a property of the class value, which
the fragment types by its construct signature alone. It is lowered as a
module binding of its own, `static C.x`, a name no source binding can spell,
after the class: the static methods, then the static fields in order, as
JavaScript defines them once the class value exists (so an initializer may
read the class and its methods, and a static field read before its
initializer is refused as any constant is). A read `C.x` is that binding
exactly where TypeScript binds it to the static member `x` of the file's
top-level class `C` (`staticReads`, resolved by the checker as symbol keys
are), so a parameter named `C` is not the class. The lowering is exact
within the fragment: the class value's type names no member, so no other
access reaches the property, and no write to it is expressible, which makes a
binding the property's only value only because a static field is required
to be `readonly` (a mutable one is module state, `class-static-mutable.ts`).
A static method's receiver is whatever its call passes, `C` for `C.m()` and
`undefined` detached (TypeScript types it as the class, and a detached call
reading a member through it throws). One whose body does not read `this` is
the same function under either, so it is an ordinary function and `C.m()` a
plain call; one that reads `this` is outside the fragment
(`class-static-this.ts`). Its annotation is its signature, which a function
reading it uses. A static block is outside the fragment.

**Initialization order.** A module constant has no value until its
declaration runs. The initialization unit refuses a call, direct or through
other module functions, that can read a constant not yet initialized. Module
functions are therefore only ever run where every constant they read holds a
value of its annotated type (or its initializer's checked claim), which is
what their units assume.

**The module result.** A module verifies when every unit's certificate checks
and the units compose: initialization is safe, and afterwards every module
function is a value of its signature. Composition is a step-indexed argument
over the mutually recursive function values; until it is a Lean theorem, a
unit's result is relative to the signatures it reaches, and the report says
so.

**Selection.** The verifier checks the whole module, or one unit of it with
`--function` (the module initialization will be a unit too). A tool never cuts
the tree down: the rest of the module is the selected unit's scope.

**Reader.** The viewer still shows one unit at a time. Its selector lists the
module's units as an outline (module initialization, each function, each
class's members), and a module line states whether the module as a whole is
verified.

## Later feature gates

Extend coverage in response to concrete programs or unjustified claims. Each
extension should establish its rules and a positive/negative integration pair.
The soundness ledger can supply targets, but its categories are not semantic
assumptions and historical coverage counts are not an implementation plan.

| Feature                                | Remaining obligation                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| -------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Flow refinement across loops and calls | State which observations survive writes and calls, and prove branch/refinement transfer rules. Stable cell contracts alone do not supply these facts.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Mutable structural objects             | Specify field presence, width, aliasing and allowed mutation; extend beyond the current invariant cells and export their types.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| More primitives and operators          | Numbers are admitted as opaque values with singleton literal types, in closure signatures and as the storage contract of a mutable local; finite singleton comparisons are supported, and a comparison on the broad family branches both ways; arithmetic on numbers is the IEEE-754 double operation yielding the number family, and on bigints the integer operation yielding the bigint family (a division by zero and a negative exponent throw), relational comparison of numbers, bigints and strings yields a Boolean, and `-`, `+` and `~` are the binary operators with a constant ([Numeric operators and bigints](#numeric-operators-and-bigints)), with compound assignments, increments and logical assignments to fields and elements evaluating their target once, the Boolean logical forms needing a Boolean target; strings are admitted on the same terms, with literal singletons and equality against a literal, and `+` concatenates a string with any primitive but a symbol, converting it by `ToString` exactly, template literals included ([String concatenation, templates and `void`](#string-concatenation-templates-and-void)); truthiness is JavaScript's `ToBoolean` ([Truthiness](#truthiness)); general equality is not, and needs its runtime behavior defined and agreement validated. Numeric current-content predicates now cover both singletons and the number family, with checked transfer across graph edges.                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| Graph-backed closure bodies            | Extend the call/body interface if source functions require graph control flow internally; surrounding graph loops are insufficient.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| Generics and bounds                    | The rigid model slice is in [TypeParams.lean](lean/Verification/Model/Types/TypeParams.lean). Source extraction of identity, `T extends boolean`, annotated and inferred immutable copies, and extra `T` parameters is in [GenericSource.lean](lean/Verification/Model/Source/GenericSource.lean). Declaration applications over rigid binders are expanded from their source equations in [DeclarationGraph.lean](lean/Verification/Model/Source/DeclarationGraph.lean); [GenericAlias.lean](lean/Verification/Model/Source/GenericAlias.lean) now only expands alias atoms in SKJS's exported claims. Distinct parameters and dependent upper-bound chains in variable-copy bodies are checked using [GenericBounds.lean](lean/Verification/Model/Types/GenericBounds.lean). Every other generic body is a graph request over its binders' parameter rows, certified at every assignment of them ([Generic bodies are graph requests over parameter rows](#generic-bodies-are-graph-requests-over-parameter-rows)). [TypeSchemes.lean](lean/Verification/Model/Types/TypeSchemes.lean) gives quantified callable semantics; source extraction connects the narrow unbounded local-closure slice described above, checks introduction universally, and compiles checked ground eliminations to graph arrows. Remaining: calls to generic declarations, generic callbacks, bounded or nested local schemes, general quantified closure bodies, conditional types, higher-rank polymorphism and parameter-changing recursion. Generic parameters, inference variables and hidden object type arguments are not interchangeable. Observing several calls is not universal certification; the separate introduction check is. |
| Difference and negation                | Supply sound rules or approximations: pointwise complement need not preserve admissibility. They do not follow from positive normalization.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| Exceptions                             | A throw is an outcome of the calculus and of graphs, with handler edges and `finally` compiled on each way out ([Throws](#throws)). Remaining: a `break`/`continue` through a `finally`, `try` inside a closure body, a generic closure that throws, `new Error(…)` and the `Error` hierarchy, `JSON`, `Promise.*` overlay entries.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |

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
owns examples, adversarial checks, runtime observations, and the
[callable surface](tests/callables/README.md#the-callable-surface): which
TypeScript callable forms are supported, where each unsupported one stops, and
the order in which they are to be taken. Arrow-row interpretation is
characterized by `SourceTypes.arrow_exact`; recursive source decoding and
extraction remain reviewed boundaries.

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
separates callee evaluation, left-to-right argument evaluation and readiness for
invocation, and dispatch connects a ready frame to the stored code and its safety
contract. Preparation plus dispatch is proved equivalent to the unary application
step, deterministic and coherent. Parameter binding preserves declaration order
and places parameters before captures, pads missing actuals with undefined, and
discards extra values only after preparation. A runtime descriptor carries its
parameter count; invocation contracts distinguish that declared count from each
overload's actual argument count.

Argument lists are native throughout. Operand reduction takes the callee first
and then the leftmost unfinished actual, at any argument count. `call_elim`
proves a ready call safe from list-signature membership, and compositional call safety covers effectful callees
and argument lists, preserving saved values across effects. Graph signatures store
ordered domain lists whose normalization and subtyping use native callable
semantics, and subtype search can split a union at any parameter position.
Creation typing, its evidence checker and the producer require every overload to
match the descriptor's arity. The JSON protocol, source claim producers and report
rendering use the same list-shaped signatures; application typing, evidence
checking and proof search accept full argument lists including the empty one, with
one premise per actual in operand order. Source calls and lambdas lower those
lists: the callee is saved first, then actuals left to right, and union-callee
elimination saves all operands before splitting the callee's type. Source
function types keep every required parameter through annotations, SKJS claim
decoding, the TypeScript producer and the report editor. The unary type,
judgment and application step remain, specialized from the general proofs through
singleton equivalence. A call may omit a trailing position whose contract admits `undefined`, which is
the value the machine binds there; `x?: T` is carried as `T | undefined`, so
optionality needs no second arity record. A parameter may instead carry a
default: its position admits `undefined` for the same reason, and the lowering
binds the raw slot anonymously and the parameter's name to the value that
replaces an omitted argument. One closure may advertise several signatures and
is checked once per signature, each a separate obligation on the same body,
from the interior claims its producer states per signature — the mechanism
compiled scheme eliminations already use. A rest parameter whose contract is a tuple of
required positions is those positions in the signature and one fresh array in
the body, allocated where the parameter is bound — a store and the object that
holds it, the same two steps an array literal takes. A spread writes the
elements of such a tuple in place of the last arguments, read after every
earlier argument, which is where a call reads them. A rest parameter whose
contract is a mutable `T[]` makes the closure's code variadic
(`CallCode.variadic`): invocation binds the fixed parameters and yields a term
that allocates the array of the remaining actuals with the ordinary store and
allocation steps, so invocation still changes no heap. A function type does not
say which code a value has: it promises which actual lists a caller may write
and what the call then guarantees (`Safety.callsT`, `restsT`), and the code's
own contract is proved once, where the value is created. So a variadic value
meets a fixed signature whose positions it admits, one value may carry fixed and
variadic signatures, and a call clause holds both. A spread among the actuals
of a variadic call is a `spread` term, replaced by its store's elements once
every earlier actual is a value — `undefined` at a hole, as iteration answers.
Typed arrays are dense (below), so a spread of `T[]` into a `T[]` rest needs
nothing more. A spread followed by an actual that runs code is copied where it
is written, and the call spreads the copy.

The common [behavioral equation](SEMANTICS.md#one-meaning-for-callable-contracts)
defines these call contracts independently of the binding descriptor, and the
[callable milestone status](tests/callables/README.md#closure-status-for-milestones-14)
records Part 4's closure, including quantified rest. The universal certificate
checks its body over arbitrary element families and proves fresh rest-store
allocation and its wrap; independently checked substitutions supply the surrounding graph's
variadic signatures. Observed call specializations cannot replace that proof.
Direct generic declarations now consume the same invocation certificates as
local schemes, including argument collection, and validate every operand claim.
Tuple-pack and argument-sequence inference remain later extensions.

### Same-level argument contracts

[`ArgumentContracts.lean`](lean/Verification/Model/Semantics/ArgumentContracts.lean)
separates contracts on argument lists from contracts on runtime values.
Grouping already evaluated arguments is not an execution step, so an argument
list is checked at the level at which its actuals are:

```text
Fits([A₁, …, Aₖ], n, W, [v₁, …, vₖ]) ⇔ ∀ i, Aᵢ(n, W, vᵢ)
All(E, n, W, vs)                    ⇔ ∀ v ∈ vs, E(n, W, v)
```

This matters for fixed-to-tuple-rest conversion. Were the positions checked
only below the current level, primitive contracts could hide the difference
but object and callback contracts could not: a callback returning `true`
where `null` is required meets a shallow approximation, but fails at the
level at which a fixed constructor requires it. With same-level membership,
exact tuples and fixed parameters admit the same lists for arbitrary families
(`fits_exact`), and a fixed signature covers a variadic one whose rest is one
exact tuple, whatever its positions (`FixedCallsPack`, `FixedCoversPack`).
One tuple shape also supplies both argument membership and an array-storage
interpretation: position-wise inclusion in an element bound proves the
argument bound and the readonly array view (`array_bound`), without changing
any location's write contract.

**One interpretation.** A graph row means a family of runtime values, and a
type also means a family of argument lists. Both come from one guarded fixed
point over (assignment, label), `qDenoteWithArgs G (mixedParameters G)`. An
assignment gives each binder a family over the tagged sum `Val ⊕ List Val`
(`MixedAssignment`); this is a semantic sum, not a calculus value. A binder
reads the component its kind selects (`selectParameter`). A pack clause
contributes no runtime values. The list component is derived from the value
component at the same level, never unfolded again:

```text
mixedValues G η S    = ⋃_{i ∈ S} qDenoteWithArgs G (mixedParameters G) (η, i)
graphArguments G η X S n W vs ⇔ ∃ i ∈ S.
    (kind i = arguments ∧ η(i)(n, W, inr vs))
  ∨ (∃ c ∈ G i. clauseArguments X c n W vs)
mixedMeaning G η S (inl v)  ⇔ mixedValues G η S v
mixedMeaning G η S (inr vs) ⇔ graphArguments G η (mixedValues G η) S vs
```

A graph's `meaning` and `argMeaning` read this at its own assignment,
`G.env`. The fixed point is admissible and non-expansive for arbitrary
admissible approximations, and argument interpretation preserves agreement
at the same level (`ArgumentNonExp`), so no extra delay is needed.
`ParameterSpace` keeps the assignment algebra (reassignment, shadowing, bound
restriction) independent of the carrier.

**Subtyping proves both components.** The core certificate relates two value
types or two argument-list types on every edge (`SameKind`); value `top` does
not admit argument lists. Coverage is proved once over the mixed meaning at
any assignment:

```text
FamLeAt G η A B n    ⇔ ∀ W v. mixedValues G η A n W v ⇒ mixedValues G η B n W v
ArgsLeBelow G η R n  ⇔ ∀ j < n. ∀ A B. R A B ⇒ mixedArgs G η A j ⊆ mixedArgs G η B j

Covers G R a b    ∀ j < n. R ⊆ FamLeAt G η · · j    ArgsLeBelow G η R n
──────────────────────────────────────────────────────────────────────  Covers.sound
                  mixedSem G η a n ⊆ mixedSem G η b n

Core G S T
──────────────────────────────────────────────  Core.mixed_sound
∀ η. FamLe (mixedMeaning G η S) (mixedMeaning G η T)
```

The induction at level `n` first proves value inclusion from both components
below `n`, then list inclusion at `n` from value inclusion at `n`
(`core_arguments_of_values`). `Sub.mixed_sound` extends this to every
structural rule: instantiation (`inst_mixed_sound`, with bounds checked on both
components), renaming tables (`table_row_mixed`), and generalization, whose
binders are independent of the type's free rows (`agree_freeWith`,
`mixed_respectsFree`). `Sub.sound` and `Sub.args_sound` are its two
projections at `G.env`.

**Substitution.** A checked instance table maps rows to rows. Under its
context an entry's row means its image in both components (`table_row_mixed`):
the value image first, from both components below the level, then the list
image at the level (`table_row_arguments`). The executable `instKinds` check
connects the wire's kinds to the selected components
(`mixed_assignment_substitution`); a scheme binder's bound is checked as
inclusion of mixed meanings, so a pack bound constrains lists.

**Programs.** Variadic calls and constructors consume `ArgFam`, a predicate on
lists (`restsT`, `ctorRestsT`), from `argMeaning`. A rest store is allocated
from same-level actuals (`restStore_safe`), and a variadic call's plain parts
at the positions of an exact tuple form a list its rest admits
(`restParts_pack`). The source-to-safety theorem `checkJson_safe` keeps its
statement; `meaning` in it is the mixed value meaning.

**Producer.** The OCaml producer separates `ty` from `pack`, with tagged
value/pack substitution arguments; `Args` is not a value-type atom. Its
traversals refuse cross-kind uses, preserve nested binders, and share element
traversal between pack shapes and arrays. Both source readers classify binder
roles structurally and scope-aware; the emitted parameter row keeps its kind,
and the wire requires it. `NormalGraph.params` is derived from
`parameterKinds`. Instantiation and substitution-table checks reject
substitutions of the wrong sort, including mixed unions.

**Controls.** `object-pack-method-value-import.ts` instantiates a pack
parameter at a tuple of objects, which a class's constructor takes, and
verifies; `invalid-object-pack-method-value-import.ts` rejects a wrong object
field. `pack-method-value-import.ts` and its invalid variants cover the
primitive case, arity and bounds. The semantic controls in
`ArgumentContractsTests.lean` instantiate a value result and a pack shared by
a constructor and trailing arguments in one substitution, and an object-valued
pack captured by a returned generic callable.

**Open.** A source binder used both as a pack and as an array value still
leaves its method opaque, pending a coherent collected-array view: using a
binder as a rest and using its collected array must not choose unrelated
contracts. The imported framework calls need `Params = []` for
`Plus`/`Minus` and `[number]` for `AddIndex`, with
`Params extends readonly DepSafe[]`; their other gaps are tracked with the
framework client. The rigid generic-body semantics (`TypeParams`) treats a
rigid parameter as a value parameter, admitting no argument list; production
generic plans go through `GenericCertificate`, which reads homogeneous rests
directly (`All`).

### Method members are host-relative

**Principle (D0).** A method member's contract is relative to its host:
reading `m` from `o` and invoking it **with receiver `o`** and admitted
actuals behaves as typed. It promises nothing for any other receiver. This is
self-application, as in Abadi and Cardelli's object calculus. Method-call
syntax already lowers to exactly this shape: read the member from the saved
object, then invoke it with that object as receiver.

Formally, with `M = (f, L, S)` a member named `f` with fixed signatures
`L = [(Ps, R)]` and variadic signatures `S = [(Ps, P, R)]`, none of which
carries a receiver:

```text
methodT(M)(k, W, v) ⇔ v's location ℓ for f has contract c, and for every j < k and
    every world U extending W|j, every u with c(j, U, u) satisfies
    callsT [({v}, Ps, R) | (Ps, R) ∈ L](j, U, u) ∧ restsT [({v}, Ps, P, R) | (Ps, P, R) ∈ S](j, U, u);
  or v lacks f, and v's prototype location holds, in the same sense, an object
    whose location for f has such a contract, still with receiver {v}
```

The receiver family is the singleton `{v}`: the host, fixed when the member is
read. The implication is required only in worlds extending the current one. A
method body reads its host's fields, which an unrelated world need not hold with
their contracts, so no real method would meet the unrestricted form; a member
is read in the current world and invoked in a later one, so nothing more is
used (`MethodMembers.methodT`, `read_view_rule_ext`). Arguments may mutate the
host before the invoke, but every field keeps its location contract, so the
pair (value read, host) keeps its contract under world extension. An own member is read from the object's location, so its
location contract implies the host-relative family. A library member (the
array prototype) is read from an ambient, immutable library object.

**Forced consequences.** Each of these follows from D0 and soundness; none is
a choice.

- *A method is not a function-typed property.* `m(): R` is host-relative;
  `f: () => R` is a function valid for any receiver. The property covers the
  method, never the reverse:
  ```ts
  class C { x = 1; m() { return this.x; } }
  const p: { m: () => number } = new C();   // refused (TypeScript accepts)
  const g = p.m; g();                        // TypeError at run time
  ```
- *Extraction gets nothing from the member contract.* `const f = o.m`,
  `xs.forEach(o.m)` and `p.then(this.handle)` call the method on another
  receiver. The supported forms are `o.m.bind(o)`, whose bound descriptor
  makes the member valid for any receiver, and class-field arrows
  (`handle = () => { … }`), which capture `this` lexically.
- *Method parameters are contravariant.* TypeScript's method bivariance is
  refused:
  ```ts
  interface Handler<T> { handle(x: T): void }
  const h: Handler<Dog> = { handle(d) { d.bark(); } };
  const ha: Handler<Animal> = h;   // refused (TypeScript accepts)
  ha.handle({});                    // TypeError at run time
  ```
- *Interfaces with method members are covariant in results.* The receiver no
  longer occurs contravariantly, so `Iterable<Dog> ≤ Iterable<Animal>` and a
  class instance below an interface it structurally meets are derivable.
- *Arrays meet `Iterable<T>` semantically.* The prototype's `values()`,
  invoked on its host array, reads that array's store, whose read view gives
  `T`. On another receiver the claim is false: `{ length: 1, 0: "x" }` yields
  `"x"`.
- *Class method bodies are checked for every receiver in the instance type.*
  That implies the host-relative member, so inherited methods need nothing
  more.
- *Objects passed to library code carry a library obligation.* Our guarantee
  covers the library invoking a member on its host. Each trusted library entry
  states that it does: GetIterator for `for…of` and spread, `JSON.stringify`
  calling `toJSON`, the Skip runtime calling `mapEntry`.

**Decisions.**

- *Method members are read-only views.* A write to a method member is refused,
  so interface method signatures and class methods are views, and a view's
  variance is covariant. This refuses the bind-in-constructor idiom
  (`this.onClick = this.onClick.bind(this)`), monkey patching and prototype
  mixins; the class-field arrow replaces the first.
  *Possible extension:* writable method members with host-indexed location
  contracts. The location's contract would depend on its owning object, which
  needs an ownership invariant (each location belongs to one object) in the
  heap semantics.
- *Extraction stays refused.* A library member is receiver-independent only
  where its trusted specification says so; no member is assumed to be.
- *Mutable arrays are invariant.* `Dog[]` is not an `Animal[]`; the accepted
  language asks for `readonly Animal[]` where only reads happen. This follows
  from the store semantics and is not relaxed by inference. A readonly target
  only reads, so it takes any list whose elements present are within its
  positions: a tuple `[number, number]` is a `readonly (Json | null)[]`, as
  sum.ts's `AddIndex` needs for `V2 extends Json`, but not a `number[]`.
- *An explicit `this` parameter* in a member (`m(this: Window)`) is
  receiver-quantified over its declared type, which implies the host-relative
  member.
- *Only a member named by a known key is a member call.* `o[k]()` with a
  dynamic `k` determines no member, so no member contract applies.
- *A class method taking fewer parameters than an interface's is claimed at
  the longer signature, not widened by subtyping.* `class Add { instantiate(cs)
  … }` meets `Resource.instantiate(collections, context)` in sum.ts: a call
  through the member passes a `context` the code ignores. A type-level rule
  letting `(C) → R` stand for `(C, X) → R` would be unsound, since a value of
  the class's instance type may hold a longer method (a subclass, or any
  object of that shape) that reads the second actual. What is true is a fact
  about this class's code, which the calculus already states: a closure's
  claim may offer more parameters than its code takes (`offersArity`), the
  extra actuals discarded at binding. So where a class value is expected at a
  construct signature whose instance has such a method, the producer claims
  the method's closure at the longer signature as well, with its own receiver,
  and the class value at a construct signature giving that instance beside its
  own (the construct rule checks the constructor's body at each). The instance
  it allocates holds the method as a field whose signatures cover the
  interface's member (`CoversByFunction`). This is the offer mechanism a named
  closure passed where more parameters are offered uses, reached from a class
  value instead of a call; there is no arrow-widening subtyping. A named
  closure, annotated or not, is offered such a signature wherever it flows
  at one (an annotated binding, a return, a field), not only as an argument,
  and an annotated binding of it is then the closure at all its signatures,
  which Lean checks against the annotation; a closure literal expected at one
  is offered it where it is created (`closure-offer-flows.ts`). A closure
  whose code binds the extra position is offered nothing, so TypeScript's
  unsound `(a, b?: string) => …` held at `(a) => …` and used at
  `(a, b: number) => …` stays refused (`invalid-closure-offer-flows.ts`). A
  module function is not offered: its slot is its annotated signature,
  checked by its own unit, and offering it would make that slot a claim. The
  constructor is offered alike: a class value expected at a construct
  signature passing more actuals than its constructor binds is claimed there
  too, beside its own, and `ctorE` checks the body at the signature's first
  parameters, as the creation rule does a closure's (`new` discards the rest).
  So sum.ts's resource classes, which take no parameters, are
  `new (params: Json) => Resource<Collections>`, the construct signature the
  runtime uses (`class-constructor-offer.ts`, `sum-sound-binding.ts`); source
  extraction required each claimed construct signature to have exactly the
  constructor's parameters, and now requires its first ones to be within them,
  as for a closure. A narrower
  parameter is still refused (`invalid-class-fewer-parameters.ts`), as
  TypeScript's bivariant method parameters admit it. At a generic call the
  expected construct signature is known only at the call's instance
  (`cs.input1.map(Plus)`, where `map`'s parameter is
  `new (...params: P) => Mapper<K, V, K2, V2>`): the class value is offered
  the parameter at the inferred instance, and inference reads the class's own
  construct signature, its first, since the ones it is offered give the
  interface's instance and fix no binder (`sum-resource.ts`,
  `invalid-sum-resource-mapper.ts`).

**Representation and rules.** The `refs` and `dict` clauses have a method
component (`MethodMembers.Sig`): members with receiver-free fixed and variadic
signatures, whose operands are rows as in `arrs`. Conjunction concatenates
methods. The declaration reader turns a non-optional method signature of an
interface or class, one or several with receiver `self`, into a member; an
optional method (`return?`) and a generic one (a scheme) stay fields for now.

A target method is covered (`CoversMethods`) by a source method of the same
key, parameters contravariant and results covariant (`CoversSig`), by a
function the source holds in a field or view whose signatures take a receiver
the source's own type is within (`CoversByFunction`), or, when the source's
own keys exclude the key, by such a function its prototype holds
(`CoversByProto`, [The array prototype](#the-array-prototype)). The second form is how a
class instance, allocated with its methods as function-typed fields whose
receiver is the instance type, meets that type: coverage takes the source type
of the pair as `self`, and `Core`'s induction on the level supplies that the
host is in it below the level.

A method call `o.m(args)` reads the member and binds it to its host in one
term, `bindMember`, before the actuals run; the bound value is then called as
any function. Nothing types a member read on its own, so extraction has no
rule. The controls `method-members.ts`, `invalid-method-extraction.ts`,
`invalid-method-as-property.ts`, `invalid-method-bivariance.ts` and
`invalid-method-result.ts` exercise each consequence.

### The array prototype

**Principle.** An array reaches `Array.prototype` through a hidden field, as
in JavaScript: a property read on an object that lacks the key continues at
the object's prototype. The prototype is a library object. Its members'
contracts are trusted specifications, generic over the receiver
(`map : ∀T U. (this: readonly T[], f: (x: T, i: number, a: readonly T[]) => U) => U[]`),
and one type, `ArrayProto`, describes it for every array.

**Calculus.** A reserved key `protoField`, like the store key, holds the
prototype; no source property names it. One step delegates a read:

$$
\frac{\mathit{fs}(k)=\varnothing\quad\mathit{fs}(\mathsf{proto})=l\quad h(l)=p}
     {h,\ \mathsf{readAt}\;k\;(\mathsf{obj}(\mathit{fs},c))\ \to\ h,\ \mathsf{readAt}\;k\;p}\ \textsc{readProto}
$$

and `readMissing` now requires $\mathit{fs}(\mathsf{proto})=\varnothing$. A
computed string-key read delegates the same way (`indexProto`, and
`indexMissing` requires no prototype). A chain is followed one step per link.

Arrays get the prototype at allocation. A literal is
`makeAt [store, proto] [arrLit es, P]`, where `P` is the ambient
`Array.prototype`, a trusted import at `ArrayProto`. The calculus no longer
builds the rest array: variadic invocation binds the rest *store* to slot 0,
and the body wraps it with the prototype it captured, as a literal does. So
every array is one store and one object, as in JavaScript.

**One array shape.** `PositiveNormalization.arrayClauseOf` is the only
definition of an array type, generic in its store and prototype operands. The
graph's array types (`SourceTypes.arrayClause`, at row `arrayProtoLabel`, where
`ArrayProto`, listed first, always lands), the generic layer's `Ty.array` and
the rows producers reserve all read it. A producer states only the store's
tuple contract and reserves the array's row (`"arrays"` in the claims); it
never spells the store or prototype keys, the bound or `ArrayProto`'s row.

**Types.** Two additions make a delegated read typable:

- *An own-key bound.* A record clause may bound its object's own keys: among
  $K$, $\mathsf{keys}(v)\subseteq K$, or outside $N$,
  $\mathsf{keys}(v)\cap N=\varnothing$ (`KeyBound`). Record types are open, so
  without a bound `xs.map` could find an own `map` and never reach the
  prototype. An array type owns none of `ArrayProto`'s keys
  ([Arrays may carry other own keys](#arrays-may-carry-other-own-keys)); a
  fresh literal's own keys are among its names. Keys are fixed at allocation,
  so a bound holds in every world. Meet collects bounds, and a target's
  bounds must follow from the source's (`CoversBounds`).
- *A prototype view.* An array type holds the prototype as a readonly view at
  `ArrayProto`: `T[]` is
  $\mathsf{Ref}(\{\mathsf{store}{:}S\};\{\mathsf{proto}{:}\mathsf{ArrayProto}\};\mathsf{outside}\,N)$
  with $N$ the keys `ArrayProto` provides, and `readonly T[]` holds the store
  as a view too.

$$
\frac{\Gamma\vdash e:\mathsf{Ref}(\ldots;\beta)\quad \beta\nvDash k\quad
      (\mathsf{proto}{:}P)\ \text{a field or view}\quad
      (k{:}A)\ \text{a field or view of}\ P}
     {\Gamma\vdash\mathsf{readAt}\;k\;e:A}\ \textsc{readProto}
$$

A method call `xs.map(f)` reads `map` through the prototype and invokes it
with receiver `xs`. The member's receiver-quantified signature admits `xs`,
so this needs no member contract of its own. Coverage of a host-relative
target member by a prototype member (`readonly T[] ≤ Iterable<T>`)
instantiates the member's scheme at the source's element type with the array
as receiver. The instance is a *known row* of the core table: proved by the
instance check, and given as the scheme row with the arrows it is below, not
as a type of the graph, since an instance has no row of its own
(`CoversByProto`, `Sub.core`). A member's meaning reads it where JavaScript's
lookup finds it, on the object or on its prototype, so a method call on an
`Iterable` that is an array reads the member through the prototype
(`MethodMembers.memberT`, `member_read_safe`).

A fresh literal where an `Iterable<X>` is expected is claimed as
`readonly X[]`, its elements at `X`: the producer finds `X` as TypeScript
does, through `[Symbol.iterator]().next()`'s unfinished results, and Lean
proves the literal below the expected type. A mutable array meets `Iterable`
only through a `readonly` form of its type, which the graph must hold; a
literal needs none.

Inside a closure body, extracted as a direct proof rather than a graph, an
array literal and an element read use the same rules (`arrLit`, `alloc` with
the captured prototype, `elem`, `elemOpt`). Element writes and destructuring
there are not yet extracted. A method call there, `xs.reduce(f, 0)` in a class
method, reads the member as the top level does: a key the object's own fields
and views do not name, outside its bound, is read by `readProto` at the
prototype member's scheme, and the call's claim at the instance is below it
(`inst`, POSITIVE-TYPES.md). The call is then the ordinary `app` on that
instance with the saved object as receiver, so a chain such as
`xs.sort().reduce(f, 0)` is two such calls. No rule is added: the closure
extraction only proposes the `readProto` node that the graph's local check
already admits. An optional field read there, `this.tag` in a method of a
class with `tag?: string`, is likewise the top level's `readOptional`, at the
field's type or `undefined`.

**Consequence.** Optional fields and index views read an absent key as
`undefined`, which is true only without a prototype. So `optT` requires no
prototype field of an object lacking one of its optional keys, writable or
readonly, and `dictViewT` of every object. A required field or a view covering
an optional one owes nothing, since its key is present. No array is below an
index signature, or below an optional field its keys lack. The store and
prototype keys are reserved: no source property or declared member may use
them.

**Trust.** `ArrayProto` states what the library's members do. It is assumed,
like an imported value's declared type, and each member's specification
includes the receiver it admits. It enters as the unit's input slot
`[[Array.prototype]]`, which literals and rest arrays read their prototype
from and generic closures capture; the safety theorem is relative to that slot
holding a member of `ArrayProto` (see
[What remains assumed](#what-remains-assumed)).

**Where `ArrayProto` comes from.** TypeScript's own declarations are the
source: `ReadonlyArray<T>` and `Array<T>` from the standard library files the
project uses, read by the declaration reader like any library. Nothing is
vendored. A checked-in overlay holds only what those declarations do not say
and soundness needs, one entry per member:

- *An allowlist.* Only members the overlay lists are part of `ArrayProto`; any
  other member is refused, not trusted by default.
- *The receiver.* TypeScript leaves `this` implicit. A member declared on
  `ReadonlyArray` takes `this: readonly T[]`; one declared only on `Array`, a
  mutator such as `sort`, takes `this: T[]`, since mutable arrays are
  invariant. Each member is quantified over its own binders, then `T`, so an
  explicit type argument list names its own binders first.
- *Dropped parameters.* `thisArg?: any` is dropped: only calls that omit it
  are admitted, which the real function accepts.
- *Weakened results.* A result may be stated as a supertype of the declared
  one: `[Symbol.iterator]` declares `ArrayIterator<T>`, which extends
  `IteratorObject<T, BuiltinIteratorReturn, unknown>`, an `Iterator`; the
  overlay states `Iterator<T>`, the result `Iterable<T>` asks for, and trusts
  no more than that.
- *Dropped overloads.* An overload whose declared result the library does not
  deliver is removed. `reduce(cb): T` only throws on an empty array, which is
  an outcome ([Throws](#throws)), so soundness would admit it; it is still not
  listed, for a reason of the reader alone: it would be a second signature of
  a generic member beside `reduce<U>(cb, init: U): U`, and a member is one
  scheme with one signature here (the producer instantiates one quantified
  signature, and a scheme's signatures share its binders, of which
  `reduce(cb)` uses none of its own).

Each entry records the text of the TypeScript signature it was reviewed
against; a test compares it with the signature TypeScript reads, so a changed
library fails the check and is re-reviewed rather than silently trusted. The
overlay is the whole trusted surface for arrays.

**Dense arrays.** An array type promises no holes: every index below the
length holds an element (`listT`). JavaScript allows holes (`xs[5] = v` on an
empty array), and so does TypeScript, which types such a write like any other.
Here an element write is typed only at an index proven no greater than the
required length, in bounds or appending, so accepted programs never create a
hole. The cost is that `xs[i] = v` at an index not proven in range is refused;
`push` appends. In return iteration, spreads and `.apply` never produce an
`undefined` the element type lacks, `find` and `findIndex` can be trusted at
their declared types, and `T[]` spreads into a `T[]` rest.

**Instances up to members.** A type is a set of labels, so an instance matches
a scheme signature when each of its types has the same members as the
signature's image, in any order: `find`'s declared `T | undefined` at
`T = boolean` is `true | false | undefined` however the producer orders it
(`sameLabels`, `sigMatch`, `restMatch`).

**Increments.** (1) Rest store binding. (2) The reserved key, the
delegation steps and the guards. (3) The own-key bound and the prototype view,
with the read rule. (4) Literals and rest arrays allocated with the prototype;
`ArrayProto` as a trusted import. (5) Coverage through the prototype.
(6) Dense arrays. (7) Arrays as `Iterable<T>`: members found through the
prototype, instance rows in coverage, `[Symbol.iterator]` in the overlay.
(8) Arrays may carry other own keys.

### Arrays may carry other own keys

**Decision.** An array type says what prototype reads need and no more: the
array owns none of the keys `ArrayProto` provides. It may own others. Skip's
runtime marks the arrays it manages with a hidden own key
(`tagSkManaged` defines `sk_managed` on arrays read from its heap and on those
`deepFreeze` freezes), typed `T & Managed` with
`Managed = { [sk_managed]: true }`; an exact bound, own keys the store and the
prototype only, made every such type empty in the model, so a program reading
`Values<[number, number]>` was verified vacuously. Types express what is
actually true.

**One mechanism.** An own-key bound is either form of one statement about
which keys the object may own (`KeyBound`: $\mathsf{among}\,K$ or
$\mathsf{outside}\,N$, `KeyBound.admits`): a fresh literal's keys are among
its names, an array's are outside $N$, `ArrayProto`'s keys
(`SourceTypes.arrayProtoKeys`, the reserved keys aside, so the store and the
prototype are admitted). Everything that read a bound reads it through
`admits`: a read through the prototype needs the key not admitted
(`readProto`, `CoversByProto`); an optional field lacking its key needs its
key and the prototype key not admitted (`CoversOptional`); index contracts
need an $\mathsf{among}$ bound without the prototype key (`CoversKeys`), which
no array has; a target's bounds must follow from the source's
(`CoversBounds`), so a fresh array object, among its store and prototype, is
an array, outside $N$.

**Where $N$ comes from.** $N$ is the keys `ArrayProto`'s row names. Arrays in
its own members' signatures are lowered while that row is, so the declaration
graph reads $N$ from `ArrayProto`'s declaration, its fields' keys, and
`prepare` checks the filled row names the same; every later array reads it
from the row. A symbol key, `[Symbol.iterator]`, is the document's own index,
so $N$ is per document, not a constant.

**Intersections.** With arrays open, an array meets records: an array with
their members too. The meet is the existing `refs` meet, one object with both
contracts. The source gate admits one array or tuple operand with record and
alias operands in an annotation, and `DeclarationGraph` lowers it by its
ground meet (`meetRow`); the OCaml producer proposes it as a `Meet`, whose
reserved row Lean fills. A meet in which one operand owns a key another's bound
excludes is empty, and normalization drops it (`Clause.consistent`): an array
with an own `map` has no member, so `number[] & { map: number }` lowers to no
clause and is refused (`array-shadow-refused.ts`), not verified vacuously.
`[number, number] & Marked` with `Marked = { readonly [marker]: true }` is
kept and inhabited (`array-marked.ts`): its elements read as the tuple's, its
prototype members as any array's, and it is both a tuple and a `Marked`
(`array-marked-value-import.ts`); a plain tuple is not a marked one
(`invalid-array-marked-plain-value-import.ts`), nor is the marker `false`
(`invalid-array-marked-key-value-import.ts`). With the exact bound, the
meet-emptiness check refuses all of these as it refuses the shadowing one.

**Trust.** That an array owns no key its prototype provides is assumed of
every array a program receives, as TypeScript assumes it in resolving
`xs.map` to `Array.prototype.map`. An array the program allocates satisfies
it: its own keys are its store and its prototype.

**Symbol keys.** A client may declare the symbol it marks with,
`declare const marker: unique symbol`, and read the marker, `xs[marker]`,
at its type (`array-marked.ts`; not as a number,
`invalid-array-marked-read.ts`), by the symbol-keyed read of
"Bigints and symbols" in [Modules and code units](#modules-and-code-units).

### Primitive members

**Principle.** A member read on a primitive is JavaScript's: `ToObject`
wraps the value in an object whose `[[Prototype]]` is the realm's
`String.prototype` (`Number.prototype`, `BigInt.prototype`,
`Boolean.prototype`), and the read continues there, except for what a string
owns: its `length` and its indices. The array design is reused, not copied:
each prototype's members come from its contract, read from TypeScript's
library through the one overlay mechanism
([`array-prototype.mts`](tools/array-prototype.mts)), and are invoked with the
primitive as receiver.

**Calculus.** `lenOf` and `elemAt` read a string's own properties as they
read a store's (`lenStr`, `elemStr`; [semantics](SEMANTICS.md#operational-language),
"Strings"). Any other member is read through the wrapper as JavaScript makes
it, a fresh object owning only `[[proto]]` at the realm's prototype, so the
existing `alloc` and `readProto` rules type it. The source read dispatches on
the receiver's shape, one arm per primitive shape its type holds, the object
read last ([typing](PROGRAM-TYPING.md#judgments-and-constructor-views)): the
lowering is JavaScript's read for every value, and is stuck, never wrong,
where a value has a shape no arm names.

**Exact types.** `s.length` is a `number`. `s[i]` is `string | undefined`
for every number `i`, a literal index in bounds included (the fragment does
not track a string's length); TypeScript says `string`, which is false past
the end. Its own `length` is never read from the prototype: the overlay
refuses to list it.

**Contracts.** `StringProto`, `NumberProto`, `BigIntProto` and
`BooleanProto` are the members the overlay lists, each an own property of its
prototype (`String.prototype.toLocaleString` is `Object.prototype`'s and is
not listed; `Boolean.prototype.toString` is its own, though TypeScript reads
it from `Object`). A member that throws on some argument its declaration
admits is read as declared, since a throw is an outcome
([Throws](#throws)): `toString(radix)` of a number or bigint throws outside 2
to 36, `toFixed` and `toExponential` outside 0 to 100 digits, `toPrecision`
outside 1 to 100 (`primitive-radix`), `repeat` of a negative or infinite
count and `normalize(form?: string)` of a form that is none of the four
(`primitive-string-members`).

An entry may *state* its signature instead of reading the declared one, as
a library global's may ([Library globals](#library-globals)): parameters
that are a part of the declared ones on which the host runs no client code,
and the result the host returns. With $\omega$ the entry of member $m$ of the
prototype of primitive $p$:

$$
\frac{\omega\in\Omega_p\quad \omega.\mathit{text}=\mathsf{text}(m)\quad
      \omega.\mathit{stated}=(\vec P)\Rightarrow R}
     {\llbracket m\rrbracket_\omega=(\mathsf{this}:p,\ \vec P)\Rightarrow R}\ \textsc{proto-stated}
$$

`split(separator: string | RegExp, limit?: number): string[]`,
`replace(searchValue: string | RegExp, replaceValue: string)` and
`replaceAll` are stated at a string pattern: the host looks up the
pattern's `[Symbol.split]` or `[Symbol.replace]`, which for a string
primitive ends at `String.prototype`, owning none, and `$` patterns in a
string replacement are string operations; `split` gives a fresh `string[]`.
`toLocaleString`'s `locales` is stated at
$\mathsf{string}\mid\mathsf{readonly}\ \mathsf{string}[\,]\mid\mathsf{undefined}$:
the host reads an array of tags by `length` and index, each a string, and a
malformed tag is a `RangeError`. Its `options`, an `Intl` interface whose
values the host converts with `ToString` and `ToNumber`, which run an
object's own methods, is not stated, so a call must omit it. Not listed:
`match`, `search`, and `replace` with a replacer, which only a `RegExp` or
an `any` callback serves. The
parser asks TypeScript which receivers of member reads are primitives, and
each primitive so read brings its contract into the declaration document and
its realm prototype into the module's values, at the name
`[[String.prototype]]` and so on, which no source identifier spells.

**Trust.** The contracts are assumed, as `ArrayProto` is
([What remains assumed](#what-remains-assumed)).

**Open.** A method call on a union of primitives (`(x: string | number).toString()`)
reads a union of members whose receivers differ; the call rule needs one
callee contract its receiver meets, so such a call is refused.

### Library types

**Principle.** A few standard-library declarations do not say what TypeScript
means by their names: `T[]` is `Array<T>` by definition, every function and
class is a `Function` though that interface has no call signature, and
`Record<K, V>` is an alias of a mapped type. The declaration reader reads a
reference to such a name as its meaning, not as the declaration's members
(`LibraryType` in [`declaration-graph.mts`](tools/declaration-graph.mts)), and
only when every declaration TypeScript binds the name to is in a standard
library file. A program that declares its own `Array` in a module reads its
own interface; one that merges members into the global `Array` is refused, as
the merged interface is read.

**Source reading.** Write $\llbracket\tau\rrbracket$ for the source term the
reader gives type syntax $\tau$ (`typeTerm`), and $\mathit{lib}(N)$ when
every declaration of $N$ is a standard library's:

$$
\frac{\mathit{lib}(\mathtt{Array})}
     {\llbracket\mathtt{Array}\langle T\rangle\rrbracket=\llbracket T[\,]\rrbracket}
\qquad
\frac{\mathit{lib}(\mathtt{ReadonlyArray})}
     {\llbracket\mathtt{ReadonlyArray}\langle T\rangle\rrbracket=\llbracket\mathtt{readonly}\;T[\,]\rrbracket}
$$

So `Array<T>` is the one array type of [The array prototype](#the-array-prototype),
with its store, its exclusion bound and its `[[proto]]` at `ArrayProto`:
values pass between the spellings, the prototype's members apply, and it is
invariant in `T` as `T[]` is (`array-generic-name.ts`,
`invalid-array-generic-readonly.ts`, `invalid-array-generic-invariant.ts`).
Using the name is using arrays: the file's first `Array<T>` may stand for its
arrays and bring `ArrayProto` in. A declaration that extends `Array`, such as
`class StringArray extends Array<string>`, has no base to inherit members from
here and is refused.

A mapped type whose value does not name its key is expanded where its key is
known, as TypeScript expands it: string- and number-literal keys are fields,
each named by the property its literal names ($\mathsf{key}(\texttt{"}s\texttt{"})=s$,
$\mathsf{key}(n)=\mathsf{ToString}(n)$), `string` a string index, and $m$ its
`readonly` and `?` modifiers (a `-` modifier over a key union copies nothing,
so it states nothing):

$$
\frac{P\notin\mathrm{fv}(V)\quad\llbracket K\rrbracket=\lambda_1\mid\cdots\mid\lambda_n\ \text{literals}\quad(n\ge0)}
     {\llbracket\{[P\ \mathtt{in}\ K]^m\colon V\}\rrbracket=\{\mathsf{key}(\lambda_1)^m\colon\llbracket V\rrbracket;\ \ldots;\ \mathsf{key}(\lambda_n)^m\colon\llbracket V\rrbracket\}}
\qquad
\frac{P\notin\mathrm{fv}(V)\quad\mathtt{string}\in\llbracket K\rrbracket\subseteq\mathtt{string}\cup\mathtt{number}\cup\text{literals}\quad\mathtt{?}\notin m}
     {\llbracket\{[P\ \mathtt{in}\ K]^m\colon V\}\rrbracket=\{[k\colon\mathtt{string}]^m\colon\llbracket V\rrbracket\}}
$$

`string` absorbs every string and number key, as every numeric key is a
string key. The keys $\llbracket K\rrbracket$ are the union of literals and
primitives TypeScript computes for $K$ where it has one (`TermScope.keys`,
[Computed types](#computed-types)), so an alias of literals or a `keyof` is
its literals, in a declaration and in an annotation alike
(`record-alias-keys.ts`, `invalid-record-alias-keys.ts`). Likewise `number`
without `string` is a number index, absorbing every number literal, and
`symbol` a symbol index ([Index signatures](#index-signatures)), beside the
fields of the remaining literals (`record-numeric-key.ts`); an optional one,
a type parameter or any other key is refused. A library alias whose equation is a mapped
type is that mapped type at the reference's arguments, which is how
`Record<K, V> = { [P in K]: V }` reads:

$$
\frac{\mathit{lib}(L)\quad L\langle\vec X\rangle=\{[P\ \mathtt{in}\ K]^m\colon V\}}
     {\llbracket L\langle\vec A\rangle\rrbracket=
      \llbracket\{[P\ \mathtt{in}\ K[\vec A/\vec X]]^m\colon V[\vec A/\vec X]\}\rrbracket}
$$

Its parameters' bounds (`K extends keyof any`) are TypeScript's to check at
each reference; only the keys above expand, and an argument at the key
parameter is the keys TypeScript computes for it (`libraryArguments`). So `Record<"a" | "b", V>` is a record
with both fields required (`record-library.ts`, `invalid-record-missing-key.ts`),
and `Record<string, V>` is the writable string index `{ [k: string]: V }`,
whose read at a key the object may not own is `V | undefined`, where
TypeScript types it `V` (`invalid-record-string-read.ts`).

**`Function`.** Its equation is the source term `callable`, whatever members
the library declares:

$$
\frac{\mathit{lib}(\mathtt{Function})}{\mathtt{Function}=\mathsf{callable}}
\qquad
\llbracket\mathsf{callable}\rrbracket=\llbracket\mathsf{arrs}\,[\,]\,[\,]\rrbracket\cup\llbracket\mathsf{ctors}\,[\,]\,[\,]\rrbracket
$$

that is, a value with closed invocation code or a class: what TypeScript's
special case says every callable and constructible type meets. Dropping the
declared members (`apply`, `call`, `bind`, `length`, …) gives a supertype of
TypeScript's `Function` that the model can state: no closure here owns those
keys. It meets no signature, so nothing calls or constructs through it; a
call of a `Function`, which TypeScript types at `any`, is refused
(`function-call-refused.ts`). A function, a class and a construct-signature
value meet it (`function-library.ts`), by the coverage rules of
[POSITIVE-TYPES](POSITIVE-TYPES.md#function-and-class-coverage) with no
target signature; a record does not, though TypeScript admits an object
with `Function`'s members (`invalid-function-from-object.ts`). The OCaml
producer proposes the same two clauses (its `Callable` atom, a value with
call code meeting no signature, and `Ctors []`); Lean lowers the term itself
(`DeclarationGraph.lowerType`). An interface that extends `Function` meets
`callable` with its own record operand, which has no representable clause,
and is refused.

**`object` and `{}`.** The keyword `object` is every object: an ordinary one,
an array or an instance, which is a record constraining no key, or one with
call or construct code. `{}`, a type literal with no member, constrains no
key either, and is every value but `null` and `undefined`, a primitive
included; it is not an empty record:

$$
\llbracket\mathtt{object}\rrbracket=\llbracket\mathsf{refs}\,[\,]\,[\,]\,[\,]\rrbracket\cup\llbracket\mathsf{callable}\rrbracket
\qquad
\llbracket\{\}\rrbracket=\mathtt{boolean}\cup\mathtt{number}\cup\mathtt{string}\cup\mathtt{bigint}\cup\mathtt{symbol}\cup\llbracket\mathtt{object}\rrbracket
$$

`refs [] [] []` is `recT []`: an object with no call code, whatever its own
keys, arrays and class instances included (their store and `[[proto]]` are
own keys it does not constrain). The source term is the atom `object`, which
Lean lowers to those three clauses; an annotation's claim is those rows
(`object-types.ts`; `invalid-object-type.ts`: `{}` holds primitives, which
are not objects; `invalid-empty-object-type.ts`). Before this, a
declaration's `{}` was read as `refs [] [] []` alone, which as a result type
claimed an object where the library may return a number; and an interface
that extends `{}` meets its own members with those clauses, which is its own
members.

### Computed types

**Principle.** `typeof x`, `keyof T`, `T[K]`, template literal types and
intersections of primitives and literals (`computedForm`) are types
TypeScript computes from other types, and they mean the type it computes. The declaration reader evaluates each where it is written
([`computed-types.mts`](tools/computed-types.mts)), in a declaration and in
an annotation alike (the parser sends the file's outermost ones outside type
declarations to `collectDeclarations`, `computed`), to a term the fragment
already has, exactly, or refuses it with the reason no such term exists. It is
one reading, `typeTerm`'s: an evaluation that names a declared type reads
that declaration's own syntax where it is declared.

**Evaluation.** Write $\mathit{ts}(\tau)$ for the type TypeScript's checker
gives the type node $\tau$ (`getTypeFromTypeNode`), and $\mathsf{lits}(t)$
for $t$ as a union of literals (string, number, bigint, Boolean) and
primitive families (`string`, `number`, `bigint`, `symbol`, `null`,
`undefined`, `void`, `unknown`, `never`) when it is exactly one
(`literalUnion`). For a computed form $\tau$:

$$
\frac{\mathsf{lits}(\mathit{ts}(\tau))=U}{\llbracket\tau\rrbracket=U}\ \textsc{computed}
$$

This is how `keyof {a: T; b: U}` is `"a" | "b"`, `keyof {[k: string]: T}` is
`string | number`, `` `a${"b" | "c"}` `` is `"ab" | "ac"`, `` `${boolean}` `` is
`"false" | "true"`, `typeof undefined` is `undefined` and `typeof n` for a
`const n: number` is `number`. `typeof x` of a narrowed binding is its
narrowed type, as TypeScript reads it. Where the result is not such a union,
a form reads the syntax that states it:

$$
\frac{x\ \text{declares}\ x\colon\sigma\quad\mathit{ts}(\sigma)=\mathit{ts}(\mathtt{typeof}\ x)}
     {\llbracket\mathtt{typeof}\ x\rrbracket=\llbracket\sigma\rrbracket_{x}}
\qquad
\frac{x\ \text{a function or class value, not generic, no statics}}
     {\llbracket\mathtt{typeof}\ x\rrbracket=\mathsf{type}(x)}
$$

where $\llbracket\sigma\rrbracket_x$ reads $\sigma$ where $x$ is declared
(its enclosing functions' binders in scope), and $\mathsf{type}(x)$ is what an
import of $x$ reads (**Imported values**): a function's signature, a class's
construct signature. `typeof x.y` is its member's declared annotation, with
`| undefined` for an optional one. The checker's identity of the two types is
the premise: an annotation that is not what TypeScript computes, a narrowed
binding's or a generic member's at an instance, is refused. For an indexed
access, $\llbracket T\rrbracket$ is projected at each key of
$\mathsf{lits}(\mathit{ts}(K))$: a record's field (with `| undefined` where
optional), an array's element at `number`, a tuple's position (all of them at
`number`), a union's parts each, an alias without parameters through its
equation, and a named type's member through its declared annotation under the
same identity premise.

**Refusals.** Each with its reason: a template literal type with a
`${string}` or `${number}` hole is a string pattern, infinitely many strings
the fragment has no type for (`computed-template-pattern-refused.ts`); a form
over a type parameter, `keyof T` or `T[number]` in a generic alias, is
computed only at an instance (`computed-keyof-binder-refused.ts`); `keyof` of
an array, a string or a class with well-known symbol members has a unique
symbol key, which no type names; `typeof` of a binding without an annotation
is the type TypeScript infers for it, which no declaration states
(`computed-typeof-inferred-refused.ts`); `typeof C` of a class with static
members is refused, since the statics are bindings of their own, not members
of the class value (`computed-typeof-statics-refused.ts`); a generic function
or class value has no annotation type. `computed-types.ts` verifies each
evaluated form; `invalid-computed-keyof.ts`, `invalid-computed-typeof.ts` and
`invalid-computed-index.ts` show that each is the computed type and no wider.

**Trust.** TypeScript's evaluation is part of the trusted front end, as its
name resolution already is: the type a computed form denotes is the one the
checker computes, and the reader states it exactly or refuses it.

### Method signatures in type literals

A method signature in a type literal, `{ m(x: number): number }`, is what it
is in an interface ([Method members are host-relative](#method-members-are-host-relative)):
a member read off its object and invoked on it, not a field holding a function
another call may run detached. The declaration reader reads it in a type
alias's own body, as an interface's, and in a type literal nested in a
declaration or written in an annotation, where its receiver is the literal's
own object (`type-literal-methods.ts`; `invalid-type-literal-method.ts`:
read off its object it is no function value). An annotation's record with a
method is its graph rows, which Lean lowers as a declaration's body; the
producer marks such a member host-relative (`host`) and states it among the
clause's methods. An optional method is an optional field whose function
takes its declaration as its receiver, so one in a nested literal, which is
no declaration, is refused (`type-literal-optional-method-refused.ts`), as is
a generic method outside a declaration.

A type literal of construct signatures only is its constructor type
([Object literals](#object-literals)); an interface of construct signatures
only is read the same way (`constructorForms`, the one reading of a
construct signature). One with other members as well describes a class
value's statics, which are bindings of their own here, not members of a
class value's type, and is refused (`construct-signature-members-refused.ts`),
as `typeof C` of a class with statics is.

### Numeric property names

A numeric property name is the key its value's `ToString` spells, as
JavaScript's `ToPropertyKey` converts a number ([Object literals](#object-literals),
"Keys": `{ 0x10: T }`, `{ 16: T }` and `{ 1_6: T }` state the one key
"16"). One function spells it wherever a name is written, `numericKey`
(`type-term.mts`): a type literal's and an object literal's names, and a
mapped type's number-literal keys. A read or write with a number key of a
receiver claimed only at records is the named access of that key, as for an
enum's reverse mapping (`keyField` and `recordReceiver` in
`SourceExtraction.lean`, the producer's `number_key`):

$$
\frac{\Gamma\vdash e:R\quad R\ \text{only records, none owning the array store}\quad
      \Gamma\vdash k:n\ \text{(one number)}}
     {e[k]\ \text{is the access of}\ \mathsf{ToString}(n)\ \text{on}\ e,\ \text{after}\ e\ \text{and}\ k}
$$

where $\mathsf{ToString}$ is the calculus's `numberToString`,
`Number::toString` exactly. An array's number key stays its store's element.
`numeric-field-names.ts` verifies; `invalid-numeric-field-names.ts` and
`invalid-numeric-key-read.ts` show `0x10` is "16", not "10". An array may
carry own keys of its own ([Arrays may carry other own keys](#arrays-may-carry-other-own-keys)),
a numeric one included, which no JavaScript array has apart from its
elements: such a model value is no JavaScript value, so a record type naming
a numeric key holds of no JavaScript array, and nothing is claimed for one.

### Index signatures

**Principle.** An index signature constrains the keys its key type names, and
no other: `[k: string]` every string key, `[k: number]` the **canonical
numeric keys**, and `[k: symbol]` every symbol key. One mechanism states all
three: an index is a view (and, mutable, a writable contract) over a **key
class** $\kappa\in\{\mathsf{strings},\mathsf{numeric},\mathsf{symbols}\}$
(`IndexKeys`, [POSITIVE-TYPES](POSITIVE-TYPES.md#records)); every
dictionary is one over $\mathsf{strings}$. A canonical numeric key is a string
some number's `ToString` spells,

$$
\mathsf{Numeric}(s)\iff\exists x.\ \mathsf{ToString}(x)=s
$$

exactly TypeScript's numeric property names ($s$ with
`ToString(ToNumber(s)) = s`: "0", "1.5", "-1", "1e+21", "NaN", "Infinity";
not "01", "1.50" or "-0"), and exactly the keys `o[n]` reaches for a number
$n$: a computed key is converted by `ToPropertyKey`, which on a number is its
`ToString` (`propertyKey`, [SEMANTICS](SEMANTICS.md)). An index over a union
of key types is one index per member at the same contract, whose conjunction
constrains the union's keys; one over `string | number`, or a number index at
the string index's contract, is the string index alone, since every numeric
key is a string key (`index-signature-kinds.ts`):

$$
\llbracket\{[k\colon\mathtt{number}]^m\colon V\}\rrbracket=\mathsf{Dict}(\mathsf{numeric}{:}V)
\qquad
\llbracket\{[k\colon\mathtt{symbol}]^m\colon V\}\rrbracket=\mathsf{Dict}(\mathsf{symbols}{:}V)
\qquad
\llbracket\{[k\colon\mathtt{string}]^m\colon S;\ [k\colon\mathtt{number}]^m\colon N\}\rrbracket=
  \mathsf{Dict}(\mathsf{strings}{:}S,\ \mathsf{numeric}{:}N)
$$

TypeScript requires $N\subseteq S$ of the last (TS2413); the model needs no
such check, since the two views are a conjunction: a numeric key's value
meets both. Consequences, each proved in Lean:

- **Reads.** A named key reads through an index whose class surely admits
  it (`IndexKeys.surely`: any string key for $\mathsf{strings}$; for
  $\mathsf{numeric}$ a key a number spells, checked by that number,
  `numericKey?`), at $V\mid\mathtt{undefined}$ (`readDict`); `x[0]`, whose
  number names the key "0", and `x["1.5"]` read a number index. A computed
  key of type `string`, `number` or `symbol` reads through an index over a
  class containing its keys' (`keyClause`, `IndexKeys.within`): a number
  through a number index or a string one, a symbol through a symbol index
  (`indexDict`). Where both a number and a string index admit a key, the
  number index's narrower contract is read.
- **Subtyping.** A target index is covered by a source index over as many
  keys ($\mathsf{numeric}\subseteq\mathsf{strings}$) with a contract within
  it; a writable one by a writable one of an equivalent contract. So
  `{[k: string]: number}` is `{[k: number]: number}`, mutable as it is, and a
  number index is not a string index (TypeScript agrees). The class and the
  contract are compared separately: a smaller class with a larger contract
  is neither below nor above a larger class with a smaller one. Code holding
  a writable index may add keys of its class at its contract (the trust
  boundary of [Writable string index signatures](#writable-string-index-signatures)),
  so a writable target also needs every source index and optional field over
  such a key to admit its contract: a mutable
  `{ [k: string]: S; [k: number]: N }` is not a mutable `{ [k: string]: S }`,
  through which a numeric key could be given an $S$ value that a holder of the
  number index reads as $N$ (`invalid-number-index-forget.ts`; TypeScript
  accepts it). The optional-field half closes the same gap for string
  indexes: a mutable `{ a?: 1; [k: string]: number }` is no longer a mutable
  `{ [k: string]: number }`.
- **Literals.** A fresh literal meets an index through its exact own keys
  (`CoversKeys`): each key the class *may* admit must hold a field within the
  index. For a number index a key is excused only when no number spells it
  (`notNumericKey`: not `NaN` nor an infinity, and not beginning with a digit
  or `-` and a digit, which every number's spelling does,
  `numberToString_shape`), so `{ name: "n", 0: true }` is a
  `{ name: string; [k: number]: boolean }`: `name` is no number's spelling.
  A key the check cannot excuse, such as "1x", is held to the index:
  incompleteness, never unsoundness.
- **Writes.** As for string indexes, no computed write through an index is
  typed ([Writable string index signatures](#writable-string-index-signatures)):
  the calculus adds no key to an existing object. `x[99] = v` and `x[n] = v`
  stay refused.
- **Arrays** keep their own mechanism: a store of dense locations, not an
  index. A value TypeScript types `{ [k: number]: T }` that is an array (its
  prototype is `Array.prototype`) is not a dictionary here, which has no
  prototype: passing an array where a number index is expected is refused, an
  incompleteness.

Where TypeScript is unsound here, the model refuses: a read at a key the
object may lack is $V\mid\mathtt{undefined}$ (`invalid-number-index-read.ts`,
`invalid-symbol-index-read.ts`); a mutable number index is invariant
(`invalid-number-index-widen.ts`) and is not dropped from a mutable string
index (`invalid-number-index-forget.ts`); and a record type has no implicit number
index, since it states nothing of the keys it does not name
(`invalid-number-index-implicit.ts`). Positive cases: `number-index.ts`,
`symbol-index.ts`, `record-numeric-key.ts`.

**Source forms.** The declaration reader states a number index with a
contract of its own as the object term's `numberIndex`, a symbol index as its
`symbolIndex`, each present only when the object has one (`type-term.mts`);
Lean lowers them (`DeclarationGraph.lowerType`), and an annotation's type
literal holding one is its graph rows, as one with methods is, since no claim
atom spells an index over a class. The OCaml producer's shape carries its
indexes with their classes (`Semantic.index_signature.keys`), proposes reads
as above, and writes each dictionary index as `[class, labels]`
([REQUEST-PROTOCOL](REQUEST-PROTOCOL.md)).

### Annotation intersections

An annotation's intersection is the meet of its operands, as a declaration's
is ([Compositional unions at the source boundary](#compositional-unions-at-the-source-boundary)):
record and function operands, named or written, are one location under
several contracts or one function with several signatures, and other ground
operands the graph's meet of their rows (`meetRow`), an array's with records
included. An intersection of primitives and literals is the type TypeScript
reduces it to, `string & "fixed"` to `"fixed"` and `number & string` to
`never` (a computed form, [Computed types](#computed-types)). One with a type
parameter is known only at an instance, and is refused
(`intersection-binder-refused.ts`); a meet Lean cannot represent is refused
there (`annotation-intersections.ts`, `invalid-annotation-intersections.ts`).

### Library globals

**Principle.** The standard library's global values (`BigInt`, `Symbol`,
`String`, `console`, …) are global variables like Node's `process`, read by
the one global rule of [Modules and code units](#modules-and-code-units)
(**Global values**) at the members and call signatures a module uses. But
TypeScript's declarations of them are not all true: `String(value?: any):
string` converts an object by calling its `toString` or `valueOf`, code of
the client's that may do anything. A throw is not such a falsehood:
`BigInt(1.5)` throws a `RangeError`, an outcome safety admits
([Throws](#throws)), so `BigInt` is read as declared. So, as for `Array.prototype`
([The array prototype](#the-array-prototype)), a standard library global is
read only through a checked-in overlay
([`library-globals.mts`](tools/library-globals.mts)), one entry per signature,
holding only what the declarations do not say and soundness needs:

- *An allowlist.* A call, method or property signature of a global declared
  in a standard library file is read only when an entry lists it, with exactly
  the declaration text it was reviewed against; anything else is refused
  (`… is not in the reviewed overlay of library globals`), so a changed
  library is re-reviewed, never trusted silently. A global declared elsewhere,
  such as `@types/node`'s `process`, is read as declared.
- *Admitted arguments.* Where the host runs code of the client's on some
  arguments the declared parameter admits, the entry states the parameter at
  the part $S$ on which it runs none (`admit`). A host that only throws on an
  argument needs no entry: a throw is an outcome.

With $s$ a selected signature (in $C$ or some $O_m$ of the global rule),
$\Omega$ the overlay and $\omega$ an entry:

$$
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega.\mathit{global}=x\quad \omega.\mathit{text}=\mathsf{text}(s)\quad
      \omega\ \text{admits}\ (i, S)}
     {\llbracket s\rrbracket_\Omega=\llbracket s\rrbracket\bigl[\,p_i:=S\,\bigr]}\ \textsc{library-global}
$$

and an entry without `admit` reads $s$ as declared. Replacing a parameter by
a subset of it gives a supertype of the declared signature, so the entry
assumes no more than the declaration; what it adds is that the host meets the
weaker signature, which is what is actually true.

**Entries.**

| Global | Signature | Read as |
| --- | --- | --- |
| `BigInt` | `(value: bigint \| boolean \| number \| string): bigint` | as declared: a bigint, or a throw (`BigInt(1.5)` a `RangeError`, `BigInt("x")` a `SyntaxError`); no client code runs on a primitive |
| `Symbol` | `(description?: string \| number): symbol` | as declared: a fresh symbol, whose description converts without running code |
| `Symbol.for`, `Symbol.keyFor` | `for(key: string): symbol`, `keyFor(sym: symbol): string \| undefined` | as declared |
| `Symbol.iterator`, `Symbol.asyncIterator`, `Symbol.hasInstance`, `Symbol.toPrimitive`, `Symbol.toStringTag` | `readonly iterator: unique symbol` and the like | stated as `symbol`: which symbol each is, a key the library's own types use, is not read |
| `String` | `(value?: any): string` | `value` at the primitives, `symbol` included: converting an object runs its `toString` or `valueOf`, which may throw or return an object, and then `String` throws |
| `console.log` | `log(...data: any[]): void` (the DOM library's) | as declared, `any` as `unknown`: output, which the model does not observe; the host formats its arguments without running code the fragment can write |
| `Array.isArray` | `isArray(arg: any): arg is any[]` | the test $\mathsf{isArray}$, below; the declared guard is not read |
| `Object.keys` | `keys(o: object): string[]` (ES5), `keys(o: {}): string[]` (ES2015) | as declared: a fresh array of the own enumerable string keys, true of every object; no getter runs |
| `Object.values`, `Object.entries` | `values(o: {}): any[]`, `entries(o: {}): [string, any][]` | as declared, `any` as `unknown`: nothing is known of an open record's other keys' values (`invalid-object-values.ts`) |
| `new Array` | `new (arrayLength?: number): any[]`, `new <T>(...items: T[]): T[]` | stated as $\forall T.\ \mathsf{new}()\Rightarrow T[\,]$: a fresh empty array is at every element type, which `any[]` states less precisely; no argument |
| `new Error` | `new (message?: string): Error` (ES5), `new (message?: string, options?: ErrorOptions): Error` (ES2022) | stated as $\mathsf{new}(\mathit{message}:\mathsf{string})\Rightarrow\{\texttt{[[proto]]}:\{\mathsf{readonly}\ \mathit{message}:\mathsf{string}\}\}$, owning no `message` key: the message is own in JavaScript but not enumerable, which the model states by holding it on a prototype it gives the object (the object term's `prototype`), so a read and `in` find it and a spread does not copy it ([Object literals](#object-literals)); `name`, and a message not given, are `Error.prototype`'s, which the model does not hold, so an `Error`, a record owning both, is not claimed (`invalid-error-name.ts`, `invalid-error-no-message.ts`) |
| `Promise.resolve` | `resolve<T>(value: T): Promise<Awaited<T>>`, `resolve(): Promise<void>` | the intrinsics `%AsyncReturn%` and `%AsyncComplete%`, below: a promise settled to a primitive, or to `undefined` |
| `Promise.all` | `all<T extends readonly unknown[] \| []>(values: T): Promise<{ -readonly [P in keyof T]: Awaited<T[P]>; }>` | the intrinsic `%PromiseAll%`, below: an array of promises gives a promise of the array of their values |
| `Promise.reject` | `reject<T = never>(reason?: any): Promise<T>` | the intrinsic `%PromiseReject%`, below: a promise of every type, whose await throws the reason |
| `new Promise` | `new <T>(executor: (resolve: (value: T \| PromiseLike<T>) => void, reject: (reason?: any) => void) => void): Promise<T>` | the intrinsic `%NewPromise%`, below: `resolve` stated at a primitive, which it settles to without adopting |
| `x instanceof Array` | `Array: ArrayConstructor` (the variable's declaration) | the test $\mathsf{isArray}$, as `Array.isArray` is, below |
| `Object.values`, `Object.entries` (generic) | `values<T>(o: { [s: string]: T; } \| ArrayLike<T>): T[]`, `entries<T>(o: { [s: string]: T; } \| ArrayLike<T>): [string, T][]` | stated as $\forall T.\ (o:\{\mathsf{readonly}\ [k:\mathsf{string}]:T\})\Rightarrow T[\,]$ and $\ldots\Rightarrow[\mathsf{string},T][\,]$: a dictionary's every own string key holds a `T` (`dictViewT`); an open record may own others (`invalid-object-values-record.ts`); `ArrayLike<T>` is not read |
| `JSON.parse` | `parse(text: string, reviver?: …): any` | stated as $(\mathit{text}:\mathsf{string})\Rightarrow\mathsf{unknown}$: a fresh value of which nothing is stated, or a `SyntaxError`; a reviver is client code the host calls on every member, and is not admitted (`json-parse-reviver-refused.ts`) |
| `JSON.stringify` | `stringify(value: any, replacer?: …, space?: string \| number): string` | stated as $(\mathit{value}:\mathsf{JsonValue})\Rightarrow\mathsf{string}$, below |
| `new Set` | `new <T = any>(values?: readonly T[] \| null): Set<T>`, `new <T>(iterable?: Iterable<T> \| null): Set<T>` | stated as $\forall T.\ \mathsf{new}(\mathsf{readonly}\ T[\,]\mid\mathsf{undefined})\Rightarrow\mathsf{Set}\langle T\rangle$: a fresh set of the array's elements, read by the host's array iterator; another iterable's iterator is client code |
| `new Map` | `new (): Map<any, any>`, `new <K, V>(entries?: readonly (readonly [K, V])[] \| null): Map<K, V>`, `new <K, V>(iterable?: Iterable<readonly [K, V]> \| null): Map<K, V>` | stated as $\forall K\,V.\ \mathsf{new}(\mathsf{readonly}\ (\mathsf{readonly}\ [K,V])[\,]\mid\mathsf{undefined})\Rightarrow\mathsf{Map}\langle K,V\rangle$: each pair read at its indices 0 and 1; an empty map is at every `K` and `V` |
| `new Date` | `new (): Date`, `new (value: number \| string): Date` (ES5), `new (value: number \| string \| Date): Date` (ES2015), `new (year: number, monthIndex: number, date?: number, …): Date` | the first and last as declared; the one-argument forms stated at $\mathsf{number}\mid\mathsf{string}$: an object argument, which any value meeting the `Date` interface may be, is converted by its own `valueOf` or `toString` (`invalid-date-object-argument.ts`); an invalid date is a `Date` |
| `Date.now` | `now(): number` | as declared |

**Stated signatures and constructs.** Where the declaration states less
than the host does (`any`) or more (a parameter at which the host
misbehaves), an entry states the signature the host meets (`stated`): its
binders, its parameters, which a call may not exceed, and its result; for a
property, its type is the result, as for the well-known symbols. It is
read for construct signatures: a global the module only constructs is, as a
class value is, its selected construct signatures, each read as its entry
states it, or as declared outside the standard library. With $s$ selected
by the module's `new x(…)` expressions and $\omega$ its entry:

$$
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad \omega.\mathit{global}=x\quad
      \omega.\mathit{text}=\mathsf{text}(s)\quad
      \omega.\mathit{stated}=\forall\vec X.\ \mathsf{new}(\vec P)\Rightarrow R\quad
      |\vec a|\le|\vec P|\ \text{for each}\ \mathsf{new}\ x(\vec a)\ \text{selecting}\ s}
     {\llbracket s\rrbracket_\Omega=\forall\vec X.\ \mathsf{new}(\vec P)\Rightarrow R}\ \textsc{library-construct}
$$

Overloads stated alike are one signature, instantiated at each `new` by its
explicit type arguments or, as a generic call is, from the actuals and the
expected type. A global both constructed and read through members or calls
is refused: that value would be a class with members, which has no clause.
A stated signature is an assumption like any entry: that the host, called
with at most those arguments, each in its parameter, returns a member of the
result. Replacing a parameter by a subset of what the host accepts and the
result by what the host is known to return keeps it true of the host.

A method is read as its entry states it too, a generic statement as a
scheme over its binders (a readonly member, as a generic interface method
is), selected alone for its member:

$$
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad \omega=(x,\ m,\ \mathsf{text}(s),\ \mathsf{stated}\ \forall\vec X.\ (\vec P)\Rightarrow R)\quad
      |\vec a|\le|\vec P|\ \text{for each}\ x.m(\vec a)\ \text{selecting}\ s}
     {\llbracket s\rrbracket_\Omega=\forall\vec X.\ (\mathsf{this}:\mathsf{self},\ \vec P)\Rightarrow R}\ \textsc{library-stated}
$$

A statement may name a standard library interface, `Set<T>` for `new Set`,
which then joins the graph as any reference does (read through its own
overlay, [Library collections and dates](#library-collections-and-dates)),
and a declaration no library has, which joins the document with the entry:
`JsonValue`, in the module `skjs/json`,

$$
\mathsf{JsonValue}=\mathsf{null}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\{\mathsf{readonly}\ [k:\mathsf{string}]:\mathsf{JsonValue}\}
$$

`JSON.stringify(v)` returns `undefined` for `undefined`, a symbol or a
function, calls a callable `toJSON` it finds on `v` or on an object inside
it, and throws on a bigint or a cycle. At a `JsonValue` it does none of the
first two, and its throws are outcomes: a dictionary owns no `[[proto]]`
and every string key it owns holds a `JsonValue` (`dictViewT`), so no key
it owns is callable, and it inherits only what `Object.prototype` holds,
which has no `toJSON`. Arrays are not `JsonValue`s: an array may own keys its
type does not state ([Arrays may carry other own keys](#arrays-may-carry-other-own-keys)),
a callable `toJSON` among them, which the host would call, and whose result
may be `undefined` (`invalid-json-stringify-array.ts`); an interface's
value may own one too (`invalid-json-stringify-record.ts`). A replacer and a
`space` are not admitted.

**Tests.** An entry may read a member as a test of the calculus instead of a
value (`test`): its calls are lowered to the test, and the member joins no
value. `Array.isArray` is one such entry. Its call, with one argument and
no type arguments, where TypeScript binds `Array` to the standard library's
global, is the test $\mathsf{isArray}$ of its argument. An entry without a
member, reviewed against the variable's declaration, reads the global as
the right operand of `instanceof` as the same test:

$$
\frac{\mathit{lib}(\mathtt{Array})\quad \omega\in\Omega\quad
      \omega=(\mathtt{Array},\ \mathtt{isArray},\ \mathsf{text}(s),\ \mathsf{test}\ \mathsf{isArray})}
     {\llbracket\mathtt{Array.isArray}(e)\rrbracket=\mathsf{test}\ \mathsf{isArray}\ \llbracket e\rrbracket}\ \textsc{library-test}
\qquad
\frac{\mathit{lib}(\mathtt{Array})\quad \omega\in\Omega\quad
      \omega=(\mathtt{Array},\ \cdot,\ \mathsf{text}(d),\ \mathsf{test}\ \mathsf{isArray})}
     {\llbracket e\ \mathtt{instanceof}\ \mathtt{Array}\rrbracket=\mathsf{test}\ \mathsf{isArray}\ \llbracket e\rrbracket}\ \textsc{library-instanceof}
$$

with $d$ the declaration `Array: ArrayConstructor`. `Array` owns no
`[Symbol.hasInstance]`, and `Function.prototype`'s is neither writable nor
configurable, so `e instanceof Array` walks `e`'s prototype chain for the
realm's `Array.prototype`. That finds it exactly for the arrays under two
assumptions of the host ([What remains assumed](#what-remains-assumed)):
every array a program receives is of its realm (an array from another realm
passes `Array.isArray` and fails `instanceof`), and no object but an array
inherits from `Array.prototype`. The fragment makes no such object: `class
extends Array` and `Object.create` are refused, and it cannot name
`Array.prototype`. Everything said below of `Array.isArray` holds of it
(`array-instanceof.ts`, `invalid-instanceof-else.ts`); `instanceof` against
any other right operand is not this rule.

$\mathsf{isArray}$ holds of a plain object owning the array store key
$\sigma$ ([SEMANTICS.md](SEMANTICS.md)). That is `Array.isArray`'s meaning:
the objects owning $\sigma$ are exactly the arrays, since literals and rest
arrays are allocated with it, an array the library returns is one at its
array type, no source property can name $\sigma$ (the gate refuses it as a
literal's key and a declared member's), and the calculus adds no key to an
existing object. A host object is
represented with its own keys, $\sigma$ never among them; a JavaScript array
from the host, at an array type, owns it. The branch rule is the tag rule,
`tagSlice`, whose clause answers PROGRAM-TYPING.md states (`arrayAnswer`):
where the test holds, the labels that are not all non-arrays remain; where it
fails, the labels that are not all arrays. Nothing is added to the checker.

What is not read is the declared guard. `arg is any[]` states `any`, which
admits anything; TypeScript narrows `number[] | Foo` to `number[]` where it
holds, dropping `Foo`, but an array may carry `Foo`'s keys
([Arrays may carry other own keys](#arrays-may-carry-other-own-keys)), so the
`Foo` part stays on that arm (`invalid-isarray-record.ts`). Nor is it
`unknown[]`: a mutable array type is invariant, and `x.push("s")` on a
`number[]` tested so would break its contract. Narrowing the `Foo` part to
`readonly unknown[]`, as SKJS does, would be true of JavaScript, but not yet
of the model: an object owning $\sigma$ holds a dense store and
`Array.prototype` only when an invariant says so of every object a program
receives, and the world contracts of an open record's other keys are
unconstrained. That invariant is a change to the safety theorem's heap
premise, left for later; until then, such a use is a located search failure,
never a wrong verdict.

**Intrinsics.** An entry may read a member as a call of an intrinsic
([Async functions and await](#async-functions-and-await)) that states the
same step (`intrinsic`): its calls are lowered to that call, with the
arguments as written, and the member joins no value, the intrinsics joining
the module's values instead. The intrinsic's scheme is instantiated at each
call by the INSTANCES rule, as for `await`:

$$
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega=(x,\ m,\ \mathsf{text}(s),\ \mathsf{intrinsic}\ \iota)}
     {\llbracket x.m(\vec e)\rrbracket=\iota(\llbracket\vec e\rrbracket)}\ \textsc{library-intrinsic}
$$

`Promise.resolve(v)` settles a fresh promise to `v`, unless `v` is a thenable,
which it adopts: that is `return v` in an async function, `%AsyncReturn%`,
whose bound admits only the primitives, which are never thenables
(`invalid-promise-resolve-object.ts`), and what TypeScript's `Awaited<T>`
then is. `Promise.resolve()` is `%AsyncComplete%()`, settled to `undefined`.
`Promise.all(ps)` is a new intrinsic,

$$
\mathtt{\%PromiseAll\%}:\forall T.\ (\mathit{values}:\mathsf{readonly}\ \mathsf{Promise}\langle T\rangle[\,])\Rightarrow\mathsf{Promise}\langle T[\,]\rangle
$$

a promise of the array of what the promises settle to, in order: each settles
to a member of its type argument, as `%Await%` assumes, and the array, fresh,
owns no `then` and is not adopted. The declaration takes values of any kind,
each adopted; stated, it takes promises (`invalid-promise-all-values.ts`).
Reading these members as intrinsics, not as generic members of the global,
also keeps to the one statement of adoption the async rules make.

`Promise.reject(r)` and `new Promise(executor)` are two more:

$$
\begin{aligned}
\mathtt{\%PromiseReject\%}&:\forall T.\ (\mathit{reason}:\mathsf{unknown})\Rightarrow\mathsf{Promise}\langle T\rangle\\
\mathtt{\%NewPromise\%}&:\forall T\le P.\ (\mathit{executor}:(\mathit{resolve}:(T)\Rightarrow\mathsf{void},\ \mathit{reject}:(\mathsf{unknown})\Rightarrow\mathsf{void})\Rightarrow\mathsf{void})\Rightarrow\mathsf{Promise}\langle T\rangle
\end{aligned}
$$

with $P$ `%AsyncReturn%`'s bound. A rejected promise settles to no value:
awaiting it throws its reason, an outcome ([Throws](#throws)), so it is a
promise of every type (`library-promise-reject.ts`). `new Promise` calls the
executor at once with the promise's resolving functions, and a throw out of
it rejects the promise. The declared `resolve` takes `T | PromiseLike<T>`
and adopts a thenable; stated at $T\le P$, it settles to its argument, as an
async function's return does (`library-new-promise.ts`,
`invalid-new-promise-object.ts`). A construct, `new x(…)`, is lowered to its
intrinsic as a call is:

$$
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega=(x,\ \cdot,\ \mathsf{text}(s),\ \mathsf{intrinsic}\ \iota)\quad s\ \text{a construct signature}}
     {\llbracket \mathsf{new}\ x(\vec e)\rrbracket=\iota(\llbracket\vec e\rrbracket)}\ \textsc{library-construct-intrinsic}
$$

Type arguments written at a call or construct read as an intrinsic are
TypeScript's instance of the declaration: the intrinsic's instance is
proposed from the actuals and the expected type, and Lean checks it.

**Refused, by decision.** What remains unlisted, each for its reason:

- `new Array(n)` and `new Array<T>(n)` make an array of length `n` with
  holes, which an array type here promises it has not
  ([The array prototype](#the-array-prototype), dense arrays), and
  `new Array(x)` with one argument is that whenever `x` is a number, so
  `new Array` is read without arguments only (`array-length-refused.ts`).
- A `JSON.parse` reviver, and a `JSON.stringify` replacer, are client code
  the host calls on every member, and whose results replace the members
  (`json-parse-reviver-refused.ts`). `JSON.stringify` of an array, or of an
  open record, may call a `toJSON` it owns (above).
- `new Set(it)` and `new Map(it)` of an iterable that is not an array run
  its iterator, client code; `new Date(d)` of an object runs its `valueOf`
  (`invalid-date-object-argument.ts`).
- A global both constructed and read through its members, `new Date()`
  beside `Date.now()` in one module, is a class value with members, which
  has no clause (`date-construct-and-now-refused.ts`); either alone is read.
  A global both called and read through a method, `Symbol()` beside
  `Symbol.for`, is a callable object with methods, likewise
  (`library-global-call-and-method.ts`).
- Any other signature of a library global is not reviewed and is refused as
  such (`library-global-unreviewed.ts`, `Math.random`).

**Trust.** Each entry is an assumption on the host's implementation, as
`ArrayProto` is ([What remains assumed](#what-remains-assumed)): the
selection enters the module as a global value, an input the result is
relative to.

### Library collections and dates

**Principle.** `Set<T>`, `Map<K, V>` and `Date` are standard library
interfaces whose declarations the reader cannot take as they stand: `add`
and `set` return `this`, `Date` has overloads that take locales and hints,
and every member is a native method of the realm's prototype. As for
`Array.prototype` ([The array prototype](#the-array-prototype)), they are read
through the one overlay mechanism ([`array-prototype.mts`](tools/array-prototype.mts),
`interfaceOverlay`): a reference to one of them, from the client or from a
statement of [Library globals](#library-globals), is the interface with only
its listed members, each read from the one declaration among the merged
parts whose text is the reviewed one.

$$
\frac{\mathit{lib}(I)\quad \Omega_I=[\omega_1,\ldots,\omega_n]\quad
      m_j\ \text{the member of}\ I\ \text{with}\ \mathsf{text}(m_j)=\omega_j.\mathit{text}}
     {\llbracket I\langle\vec X\rangle\rrbracket_\Omega=\{k_1:\llbracket m_1\rrbracket_{\omega_1};\ \ldots;\ k_n:\llbracket m_n\rrbracket_{\omega_n}\}}\ \textsc{library-interface}
$$

A member the project's library does not declare is left out, and so are
every other member, overload and base: a supertype of the declared
interface. A method is a host-relative member
([Method members are host-relative](#method-members-are-host-relative)):
invoked on the object it is read from, at run time its prototype's, it
behaves as its signature states. $\llbracket m\rrbracket_\omega$ drops
`thisArg`, reads a `this` result as the receiver $\mathsf{self}$, the
interface at its own parameters (`add(value: T): this` returns the set it
is called on), and `[Symbol.iterator]()`'s `SetIterator<T>` or
`MapIterator<[K, V]>` as `Iterator<T>` or `Iterator<[K, V]>`, which they
extend. A property is a readonly view: `size` is an accessor of the
prototype, and reading it gives a number.

**Members.** `Set<T>`: `add`, `clear`, `delete`, `forEach`, `has`, `size`,
`[Symbol.iterator]`. `Map<K, V>`: `clear`, `delete`, `forEach`,
`get(key: K): V | undefined` (TypeScript's own: a key the map lacks reads
nothing), `has`, `set`, `size`, `[Symbol.iterator]`. `Date`: `valueOf`,
`getTime` and the other getters, each a number (`NaN` of an invalid date),
`setTime`, `toString`, `toISOString` (a `RangeError` of an invalid date, an
outcome). The collections hold their elements in internal slots the model
does not see: a member's contract is what it returns. `Set<T>` and
`Map<K, V>` are invariant, since `add` and `set` take their parameters and
`has`, `get` and `forEach` give them (`invalid-set-covariant.ts`, where
TypeScript's bivariant methods admit the widening). Their constructors are
stated in [Library globals](#library-globals) (`library-collections.ts`,
`library-date.ts`).

**Not listed.** `keys`, `values` and `entries`, whose `SetIterator` and
`MapIterator` no rule reads yet; `[Symbol.toStringTag]`; `Date`'s
`[Symbol.toPrimitive]`, whose overloads take hints, and its members taking
locales; `ReadonlySet` and `ReadonlyMap`. A `for...of` over a `Set` or `Map`
is refused: `%Iterate%` is stated for arrays
([Loops over arrays](#loops-over-arrays), `set-for-of-refused.ts`).

**Trust.** The realm's `Set.prototype`, `Map.prototype` and
`Date.prototype` hold these natives, unmodified
([What remains assumed](#what-remains-assumed)).

### Async functions and await

**Decision.** `await` is a trusted step: `await e` yields the value the
promise `e` settles to, at its type argument, or throws the reason a rejected
promise carries ([Throws](#throws)), with no model of the job queue.
An async function's call returns a promise of what its body returns. Both are
stated as values the program calls, so no calculus rule, typing rule or proof
changes: the calculus has calls, and a call's callee is an assumption at its
declared type, as an imported value's is.

**Elaboration.** The parser writes each form as a call of an *intrinsic*, a
value named `%…%`, which no source identifier can spell and so none can
shadow (`intrinsics.mts`):

$$
\begin{aligned}
\llbracket\mathsf{await}\ e\rrbracket&=\mathtt{\%Await\%}(\llbracket e\rrbracket)\\
\llbracket\mathsf{return}\ e\rrbracket_{\mathsf{async}}&=\mathsf{return}\ \mathtt{\%AsyncReturn\%}(\llbracket e\rrbracket)\\
\llbracket\text{completion}\rrbracket_{\mathsf{async}}&=\mathsf{return}\ \mathtt{\%AsyncComplete\%}()
\end{aligned}
$$

in an async function, arrow or function expression's own body (a nested
closure's returns are its own); an async arrow's expression body is its
return, and a body that can complete gets the completing return after its last
statement. The declaration reader lists the intrinsics among the module's
values, at signatures over the standard library's `Promise`:

$$
\begin{aligned}
\mathtt{\%Await\%}&:\forall T.\ (\mathit{promise}:\mathsf{Promise}\langle T\rangle)\Rightarrow T\\
\mathtt{\%AsyncReturn\%}&:\forall T\le P.\ (\mathit{value}:T)\Rightarrow\mathsf{Promise}\langle T\rangle
\qquad P=\mathsf{null}\mid\mathsf{undefined}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\mathsf{bigint}\mid\mathsf{symbol}\\
\mathtt{\%AsyncComplete\%}&:()\Rightarrow\mathsf{Promise}\langle\mathsf{void}\rangle
\end{aligned}
$$

The reviewed overlay reads `Promise.resolve` as the last two,
`Promise.all` as a fourth, `%PromiseAll%`, and `Promise.reject` and
`new Promise` as `%PromiseReject%` and `%NewPromise%`
([Library globals](#library-globals), intrinsics).

A generic intrinsic is instantiated at each call by the INSTANCES rule of
[Modules and code units](#modules-and-code-units), so the rules below are
derived, not added: with $R$ the async function's result annotation,

$$
\frac{\Gamma\vdash e:\mathsf{Promise}\langle A\rangle}{\Gamma\vdash\mathsf{await}\ e:A}\ \textsc{await}
\qquad
\frac{\Gamma\vdash e:A\quad A\le P\quad \mathsf{Promise}\langle A\rangle\le R}{\Gamma\vdash_R\mathsf{return}\ e}\ \textsc{async-return}
\qquad
\frac{\mathsf{Promise}\langle\mathsf{void}\rangle\le R}{\Gamma\vdash_R\text{completion}}\ \textsc{async-complete}
$$

**Why the result is a primitive.** JavaScript resolves a promise with a
thenable, any object whose `then` is callable, by calling that `then` and
adopting what it passes on, not by settling to the object. Record types are
open, so no object type rules a `then` out, and TypeScript's own
`Promise<{ a: number }>` can settle to a string. The bound $P$ admits only
values that are never thenables. `Promise<void>` is `Promise<unknown>` here
(`void` is top), so a void async function may only complete: returning a value
from it is refused, where `%AsyncComplete%` settles to `undefined`, which top
admits. An awaited operand must be a `Promise`, since `await` calls a
thenable's `then` too.

**Interleaving.** Other jobs run while a function is suspended, and the body
after its first `await` runs after its caller has continued. The model runs the
body to its end before the call returns. Every point where other code can
intervene is an `await`, a call of an unknown function, so the facts a body or
its caller keeps across it are what they keep across any call: storage
contracts, which every job preserves, not observations of mutable cells.
Module initialization is no different: a module function a statement names
must read only constants already initialized, whatever runs during that
statement (`checkInitializationOrder`), so a callback a later `await` lets run
was checked when it was passed.

**Refused.** `await` of an operand not typed as `Promise`, an async function
returning an object, a void async function returning a value, a promise
returned for adoption (`return p` in an async function), async class methods,
async generators and `for await`.

### Loops over arrays

**Decision.** `for (const x of e) S` is admitted where `e` is an array, and
its step is a trusted intrinsic, stated in `intrinsics.mts` like the async
ones:

$$
\mathtt{\%Iterate\%}:\forall T.\ (\mathit{xs}:\mathsf{readonly}\ T[\,])\Rightarrow
(()\Rightarrow\{\mathsf{readonly}\ \mathit{value}:T\}\mid\mathsf{null})
$$

It is the array's iterator, stepped: each call reads the array's current
length and yields the element at the next index, or `null` past the end.
Two other readings need no new trust but more than the calculus has. The
iterator protocol through `Array.prototype[Symbol.iterator]`, which
`ArrayProto` already trusts, yields an `IteratorResult<T>`, a union told apart
by its `done` field, and narrowing a record by a test on one of its fields has
no rule here. Indexing `xs[i]` while `i < xs.length` needs a comparison of
numbers and a range fact, and there are neither. The intrinsic is the smallest
statement that yields the element type, and it is what the array iterator
does.

**Compilation.** Lean compiles the loop itself (`SourceExtraction.body`), with
no source expression for its internal steps:

$$
\llbracket\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S\rrbracket=
n\leftarrow\mathtt{\%Iterate\%}(\llbracket e\rrbracket);\
\mathit{head}:\ r\leftarrow n();\
\mathsf{if}\ r\ \mathsf{is\ null}\ \mathsf{then}\ \mathit{exit}\
\mathsf{else}\ x\leftarrow r.\mathit{value};\ \llbracket S\rrbracket;\ \mathsf{goto}\ \mathit{head}
$$

`n` is a slot of its own, at the claimed type of the call (the producer's
claim at the loop's span, with its instance), `continue` and the body's end go
to the head, which is a cut stated by the loop's entry claims, and `break` to
the exit. The tag dispatch refines `r` on each arm (`tagBind isNul`), so the
read is of a record. The rule it derives is

$$
\frac{\Gamma\vdash e:A\quad A\le\mathsf{readonly}\ T[\,]\quad
      \Gamma_{\mathit{head}},x:T\vdash S\quad \Gamma_{\mathit{head}}\ \text{the loop's entry claims}}
     {\Gamma\vdash\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S}\ \textsc{for-of}
$$

with $T$ the call's instance. Arrays are dense (`listT`), so the iterator
yields a `T` at every index below the length.

**Trust.** JavaScript's loop calls `xs[Symbol.iterator]()`, which reaches
`Array.prototype`'s, since an array owns none of the prototype's keys,
and steps it. Leaving early calls the iterator's `return` when it has one,
and the array iterator has none, so an early exit runs nothing. `%Iterate%`
states that behavior; see [What remains assumed](#what-remains-assumed).

**Refused.** A loop over anything but an array (a string, a `Set`, a `Map`,
any other iterable), a destructuring, `let` or `var` binding, `for await`, a
loop at the top level of a module (as for `while`) or inside a closure. A
client's iterable is refused for a reason of soundness: leaving its loop
early calls its iterator's `return`, client code the lowering does not
model. The host's `Set` and `Map` iterators have no `return`, so stating
`%Iterate%` at them too would be sound; it is one intrinsic, generic in one
element over one parameter type, and the loop's lowering names it alone
(`set-for-of-refused.ts`).

### Patterns

**Decision.** A pattern is lowered to the forms the graph compiler and the
closure checker already have: the value once, held in an anonymous slot; each
property or position read in pattern order by the ordinary read rules; a
default only where that read is `undefined` (a tag dispatch, the default's
claimed value on one arm and the defined slice on the other); a nested
pattern over the read, held in its own slot. One Fragment form, `destructure`
(a statement) and `destructBody` (a closure body), over one recursive
`Pattern`, carries object and array patterns, nesting, holes and an array
rest ([PROGRAM-TYPING.md](PROGRAM-TYPING.md#patterns) states the rules).

- *Array patterns read positions.* JavaScript steps the array's iterator,
  which is `Array.prototype`'s (an array owns none of its keys) and reads the
  current length and the next index at each step; a default between two steps
  runs where it does here. This is the trust `%Iterate%` already states
  ([Loops over arrays](#loops-over-arrays)); it replaces the earlier
  fresh-literal-only rule, which that decision superseded. An iterable that
  is not an array (a string, a `Set`) is refused.
- *An array rest* over one tuple of required positions is a fresh array of
  reads of the positions after the elements, allocated like an array literal
  and claimed at the rest's span, so a producer may claim `[string, boolean]`
  or, for an assigned rest, the local's `T[]`. A tuple's length is exact
  (`listT`), so the reads are the rest. Over an array of unknown length the
  rest is a slice whose length only the run knows; the calculus has no such
  term, and the rest is refused rather than approximated.
- *An object rest* `{a, ...r}` is refused: it copies every remaining own
  enumerable key of its source, which a record contract does not bound (a
  value of `{a: string; b: number}` may own `c`), and an object's keys are
  fixed where it is allocated, so allocating the named fields would give an
  object whose keys the model bounds and JavaScript's does not.
- *Defaults and the temporal dead zone.* A default sees the bindings before
  it. One that names a binding of its own declaration not yet initialized is
  refused by the parser: JavaScript throws there, and the lowering would read
  an outer binding of that name instead.
- *A declared alias* read with a default is told apart clause by clause
  (`byClause`): `type Maybe = number | undefined` is one label whose tag
  answers are mixed, and its clauses are the same values.
- *Parameters.* A function's parameter written as a pattern or with a
  default binds a hidden name (`parameter i`, which no source can spell), at
  its annotation or, with a default, its annotation or `undefined`, so a
  caller may omit it; the body starts with a `destructure` over it, in
  parameter order, which is where JavaScript initializes it. A closure keeps
  its own default schedule (`parameterOrder`) and starts its body with a
  `destructBody` for a pattern.
- *A method* is not read by a pattern: read off its object it is no function
  value (`MethodMembers`), as for `c.m` as a value.
- *Rest parameters* may be `readonly T[]`, a readonly tuple, or a declared
  alias of an array or tuple, read through its equation: the array a call
  collects is fresh, and viewing it readonly gives up only writes.

Not lowered: `let` patterns (their bindings would be cells with storage
contracts a producer states per name), assignment targets other than a
mutable local (a field or index inside `[o.f] = …`), and a rest parameter
written as a pattern.

### Statement forms

**Decision.** The remaining statement forms of a function body are lowered to
the ones the graph compiler has, where the lowering is exact, and refused
where it is not. The parser owns the lowerings that are source rewriting; Lean
owns the two graph shapes they need (a loop's update, a labeled block).
Each is stated with the rule it derives; $\Gamma\vdash_R S$ reads "the
statements $S$ are safe under $\Gamma$ in a function whose result is $R$".

- **Unbraced arms and `else if`.** An arm that is one statement is the block
  holding it; `else if (c) S` is `else { if (c) S }`. A declaration cannot be
  an unbraced arm (a syntax error), so no scope depends on the braces. A
  nested block `{ S }` is a scope of its own, `;` is nothing.
- **Bare `return` and completion.** `return;` is `return undefined`, the
  literal at the keyword (in an async body, `return %AsyncComplete%()`, as
  completing is). A block closure that does not return on every terminal arm
  ends with `return undefined` at its closing brace, as JavaScript's
  completion does; a function body already completes so
  ([Source integration](#source-integration)). Either is checked against the
  result, which `void` (top) and `T | undefined` admit:

$$
\frac{\mathsf{undefined}\le R}{\Gamma\vdash_R\ \mathsf{return};}\ \textsc{return-bare}
$$

- **Dead code.** The statements after one that always jumps (`return`,
  `break`, `continue`, `throw`, a block holding one, an `if` whose arms both
  do) are never reached: nothing jumps into the middle of a list. They are
  dropped unread when dropping them leaves every live name meaning what it
  meant: a `var` or function declaration there is hoisted, and refused; a
  `let`, `const` or `class` there binds its name in the whole block, so a
  live statement naming it is refused (it would read that binding, forever
  uninitialized); any other declaration is refused.

$$
\frac{\Gamma\vdash_R S_1\quad S_1\ \text{always jumps}\quad \mathit{names}(S_2)\ \text{free in no live statement, none hoisted}}
     {\Gamma\vdash_R S_1;S_2}\ \textsc{dead}
$$

- **`for (init; cond; update) S`** is `{ init; loop }`, where the loop is a
  `while (cond)` (`true` when absent) with an *update*: the end of the body
  and every `continue` targeting the loop run `update`, then go to the head.
  The `while` node carries the update (`Stmt.loop`, empty for a `while`), so
  the update is compiled once and nothing is duplicated. A `let` declared in
  `init` is one binding for the whole loop; JavaScript copies it into each
  iteration, which differs only for a closure capturing it, so such a closure
  is refused.

$$
\frac{\Gamma\vdash_R \mathit{init}:\Gamma'\quad \Gamma_h\ \text{the head's entry claims}\quad
      \Gamma'\le\Gamma_h\quad \Gamma_h\vdash c:\mathsf{boolean}\quad
      \Gamma_h\wedge c\vdash_R S\ \text{with}\ \mathsf{continue}\mapsto u\quad
      \Gamma_u\vdash \mathit{update}\ \text{back to}\ \Gamma_h}
     {\Gamma\vdash_R\ \mathsf{for}\ (\mathit{init};c;\mathit{update})\ S}\ \textsc{for}
$$

- **`switch (d) { … }`** is a labeled block per clause, nested in source order
  inside a labeled block for the whole switch. The innermost holds the
  dispatch: each case label in source order, `if (d === l) break` to the end
  of that label's clause block; all failing, `break` to the end of the
  `default` clause's block, or of the switch's. Each clause's statements
  follow its block's end, inside the next clause's block, so a clause that
  completes runs on into the next one's statements: fall-through is the
  graph's ordinary sequencing. A `break` in a clause leaves the switch's
  block. The discriminant is evaluated once, bound to a name no source can
  spell, unless it is a name or a field of a name and every label is a
  literal or a name, when it is read again at each test (nothing between the
  tests writes, and a field is a plain location). Labels are
  evaluated in order, each only if every earlier one failed, as JavaScript
  does. The clauses share one scope in JavaScript but not in the lowering, so
  a name declared directly in one clause and read in another, or in a label,
  is refused. Blocks carry a label and no entry of their own
  (`Stmt.block`); a `break` carries the label of the block it leaves, or none
  for a loop (`Stmt.brk`). Case narrowing is the narrowing of these `===`
  tests ([Strict equality and tag narrowing](#strict-equality-and-tag-narrowing)).

$$
\frac{\Gamma\vdash_R S\ \text{with}\ \mathsf{break}\ \ell\mapsto\Gamma_{\mathit{after}}\quad
      \Gamma_{\mathit{after}}\vdash_R S'}
     {\Gamma\vdash_R\ \ell:\{S\};S'}\ \textsc{labeled-block}
$$

- **`for (const k in o) S`** is `for (const k of %ForIn%(o)) S`, with the
  trusted intrinsic

$$
\mathtt{\%ForIn\%}:(o:\mathsf{unknown})\Rightarrow\mathsf{readonly}\ \mathsf{string}[\,]
$$

  the keys the loop visits. JavaScript visits the enumerable string keys of
  `o` and its prototypes, none for `null` or `undefined`, a string's indices
  for a string: always strings, and for any value, so `o` is unrestricted and
  the key is a `string`, never a literal of `o`'s type (an object may carry
  keys its type does not state). A key deleted before it is visited is
  skipped, one added may or may not be: the visited keys are still a finite
  list of strings, which the intrinsic's result may be. Only a `const`
  binding is admitted, as for `for...of`.

**Refused.** A clause's fall-through is admitted; still refused are a name
shared across switch clauses, a `for` closure capturing its `let`, a `var`, a
labeled source statement, a `do…while`, and any of these forms inside a
closure body (its lowering has no graph). `try`, `catch`, `finally` and
`throw` are not these lowerings: they use the calculus's throw outcome
([Throws](#throws)). A statement after a `throw` is dead code all the same.

### Throws

**Principle.** A throw is an outcome, beside a value and a step. Safety
states that every well-typed program evaluates to a value of its type, takes
a step, or throws a value; it never gets stuck, and it never reaches a wrong
value. This is ML-style type soundness with exceptions (Wright and Felleisen's,
where a division by zero raises): a type says what a *value* is, never that
none is thrown. What is refused because it would produce a wrong-typed value
stays refused; what was refused only because it could throw is admitted.

**Calculus.** `throw a` (`Tm.throw`) evaluates `a`, then throws its value. A
throwing term is one with `throw v` in evaluation position, under exactly the
contexts `Step` evaluates in (`Raises t v`, one constructor per congruence
rule); it does not step and throws one value (`raises_no_step`, `Raises_det`).
There is no propagation step: the context closure is the predicate, so no
step rule, and no proof about steps, changes but for the throwing primitives.
Those step to throwing an error object where JavaScript throws, no code of
the program's run first (`binopThrows`, disjoint from `binop`): a bigint
division by zero or negative exponent (`RangeError`), arithmetic mixing a
number and a bigint (`TypeError`), and any operator with a symbol operand and
a primitive other one (`TypeError`). The error object is an object with no
field (`thrownError`), standing for the `TypeError` or `RangeError` instance;
a handler binds it at `unknown`, and nothing typed reads more of it.

$$
\frac{v\ \text{a value}}{\mathsf{throw}\ v\ \text{raises}\ v}
\qquad
\frac{t\ \text{raises}\ v}{E[t]\ \text{raises}\ v}
\qquad
\frac{\mathsf{binopThrows}(op,v_1,v_2)}{h,\ v_1\mathbin{op}v_2\to h,\ \mathsf{throw}\ \mathit{err}}
$$

with $E$ an evaluation context. `Safe` gains the outcome
([semantics](SEMANTICS.md#computations-and-recursive-types)):

```lean
def Thrown (t : Tm) : Prop := ∃ v, Raises t v ∧ Scoped 0 v

def Safe (T : Fam) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n + 1, W, h, t =>
      ((isVal t = true ∧ T (n + 1) W t) ∨ Thrown t) ∨
      (∃ (W' : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) W' ∧ WorldAdm W' ∧ Step h t h' t' ∧
          HeapOk n W' h' ∧ Safe T n W' h' t')
```

Every composition lemma (`bind`, `bind_list`, `ctx_bind`,
`HeapObservations.bind`) takes, beside the context's step rule, its throw
rule, which carries a throw out of the context. The graph machine
(`SafeGraph`, [program typing](PROGRAM-TYPING.md#checked-control-flow-graphs))
ends a run either returning a typed value or with a closed thrown value no
handler caught.

**Typing.** `throw e` has every type (`HasTy.throw`), its operand at a type
of its own:

$$
\frac{\Gamma\vdash a:A}{\Gamma\vdash\mathsf{throw}\ a:B}\ \textsc{throw}
$$

Two bigints give a bigint for every arithmetic operator: the nonzero-divisor
and non-negative-exponent conditions are dropped (`bigint-range-errors`).
Arithmetic mixing a number and a bigint, `+` on a bigint, and a symbol in a
concatenation or a template stay refused, as TypeScript refuses them: each
would throw, which safety admits, but TypeScript's rule is sound and each is
almost surely a bug, and following TypeScript where it is sound is a
principle (`invalid-mixed-arithmetic`, `invalid-unary-plus-bigint`,
`invalid-template-symbol`). An object in a concatenation stays refused for
another reason: its conversion runs its own code.

**Handlers.** A graph node carries an optional handler: where a throw out of
its expression goes, the thrown value bound in a fresh slot as a `bind`
continuation binds a value. A node without one lets the throw end the run.
The checker requires the handler's edge (`checkHandler`) at a type admitting
every value (`admitsAll`: one of its clauses is top) and under only the facts
that hold without the heap (`handlerFacts`: immutable values, alias and
distinct links), since the expression may have run any effect before it
threw:

$$
\frac{h,t\ \text{raises}\ v\quad v\ \text{closed}}{h,\ \mathsf{eval}(t,\rho,k,\ell)\to h,\ \mathsf{at}(\ell,\mathsf{push}(v,\rho))}
\qquad
\frac{h,t\ \text{raises}\ v}{h,\ \mathsf{eval}(t,\rho,k,\varnothing)\to h,\ \mathsf{raised}(v)}
$$

**Source.** `throw e` is the node `throw x` after `e`'s value, whose
continuation is the return and whose claim is the function's result, which a
throw has: a body ending in a throw needs no return. In a closure body,
`throw e` ends the body as a return does (`throwBody`). `try B catch (e) C
finally F`:

- The nodes of `B` that may throw name `C`'s entry as their handler, with the
  thrown value bound to `e` and the slots of the `try`'s scope kept; those of
  `C` name `F`'s throw-path entry, or the enclosing handler. `e` is
  `unknown`, the only annotation admitted: anything may be thrown, by the
  body's own `throw` or by any trusted step. A `typeof` test narrows it to the
  family it names (`tagMember`: a passed test naming one primitive family is
  covered by that family's clause, whatever the tested type).
- `F` runs on every way out, and is compiled on each: after a normal
  completion of `B` or `C`, where one can complete, continuing after the
  statement; after a throw, the thrown value held in a slot of its own, then
  thrown again; before each `return` in `B` or `C`, the value held in a slot
  of its own, through every enclosing `finally`, innermost first, then
  returned. Each copy runs in the `try`'s own context: its scope, handler and
  jump targets. A `return` or `throw` in `F` leaves by its own way, as
  JavaScript's replaces the pending completion. So `F` never changes the
  completion unless it itself returns or throws, and then exactly as
  JavaScript does.

$$
\frac{\Gamma\vdash_R B\ \text{with throws}\mapsto(\mathsf{unknown},\Gamma)\vdash_R C\quad
      \Gamma\vdash_R F\ \text{on each way out}}
     {\Gamma\vdash_R\ \mathsf{try}\ B\ \mathsf{catch}\ (e)\ C\ \mathsf{finally}\ F}\ \textsc{try}
$$

- The producer states the handler's and the finalizer's entries with each
  cell at its contract and the caught value at `unknown`: a throw may leave
  the body after any part of it ran (`invalid-try-catch`).
- In an async body a throw rejects the returned promise. The lowering lets it
  leave the body as a throw, which safety admits as well: the function's
  callers use its declared signature, and the over-approximation adds no
  wrong value.

**Refused.** A `break` or `continue` leaving a `try` with a `finally` (the
lowering runs `F` for returns and throws, not for jumps:
`try-finally-jump-refused`); `try` inside a closure body (its lowering has no
graph); a destructured or annotated (other than `unknown`) catch binding; a
throw inside a generic closure, whose certificate language has no throw rule.

**Flipped.** `invalid-bigint-division` and `invalid-bigint-exponent` became
`bigint-range-errors`; `invalid-bigint-number`, `invalid-bigint-fraction`
and `invalid-bigint-string` became `bigint-conversions`;
`invalid-primitive-radix` and `invalid-primitive-radix-number` became
`primitive-radix`. The refusals they tested existed only to avoid a throw.

### Next object milestone

Multi-field objects are finite maps from property keys to locations, fixed at
allocation, each field invariant on its own. A key is a string or a symbol
(`PropKey`), and the two spaces are disjoint, as in JavaScript: a string-keyed
access never reaches a symbol-keyed field, and a string index signature
constrains string keys only. `make_fields_rule` allocates one
location per named field, `covers_recs` composes contracts field by field, and a
current-content assertion names the field it is about. Required record fields
store callbacks through the existing reference and arrow rules, and the source
tests distinguish a saved callback from a replacement and tie recursive
invocation through a cell.

**Optional fields.** An optional field is one more list on a record clause,
`optional`, with one meaning (`optT`): where the object has the key, its
location holds exactly the stated contract, as a required mutable field's
does; where it does not, nothing is claimed, and a read is `undefined`. So
presence is separate from the value's type: an absent key and a present key
holding `undefined` are different objects, both of which the type admits when
`undefined` is in the contract. `readOptional` reads the field at its contract
or `undefined`. No rule writes it, since an object's keys are fixed at
allocation and the model has no key addition. A record that does not name the
key does not cover an optional field, since it may hold the key at any type
(SKJS agrees; TypeScript does not check this). An optional method,
`return?(...)`, is an optional field. An `in` test is in the fragment
([Guards](#guards)); a key a passed test found present is a field of the
object's records from then on ([a key found present](#strict-equality-and-tag-narrowing)).

**Readonly optional fields.** `readonly k?: T` is a view that may be absent
(`SkipService.externalServices`). It is not a second mechanism: an optional
field carries a mode, writable or readonly (`OptionalField`), and `optT`
relates a present key's contract to the type by the mode, as a tuple position
does (`SlotContract`): equal for a writable one, implying it for a readonly
one. The no-prototype condition is the same for both, since both read an
absent key as `undefined`. Hence one read rule (`readOptional`, whose semantic
premise `read_optional_rule` now asks only that the contract imply the type)
and one coverage rule: an optional field is met by a source slot of its key,
an invariant field, a view or an optional field, each with its mode, whose
type is within the target's, and, for a writable target, by a writable slot of
an equivalent type, so no location is retyped. A readonly optional field is
thus covariant and never covers a writable one, as a view is and does not;
TypeScript agrees, except that it lets a readonly field meet a mutable one,
which here would let a write through the target retype what the source's
readers rely on. It is also met by an own-key bound excluding both its key and
the prototype key, which says the object lacks the key and has no prototype:
the bound is how a fresh literal that leaves out an optional field, such as
`runService`'s options without `no_cors`, establishes it
([Fresh literals have exact keys](#fresh-literals-have-exact-keys)). A class instance lacking the key does not cover
it: it has a prototype, where the read would continue (TypeScript accepts
this). The claim wire needs no new form: a readonly field's write capability
is empty, and the lowering reads any field whose read and write differ as
readonly, optional or not, as the plain record lowering does.

The callable forms still to be taken, and their order, are the
[callable surface](tests/callables/README.md#the-callable-surface). Each should
follow explicit argument and receiver contracts rather than be erased into free
unary calls. None of them is a prerequisite for the bounded callable-model
integration above.

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

### Shape predicates

The trusted parser recognizes strict equality or inequality between `typeof e`
and one of the literals `"number"`, `"string"`, `"boolean"`, `"undefined"`,
`"function"`, `"bigint"`, `"symbol"` and `"object"`, in either operand order. It
lowers that syntax to one Boolean shape test (`isNum`, `isStr`, `isBool`,
`isUndef`, `isFun`, `isBigint`, `isSymbol`, `typeofObject`); no separate claim
for the `typeof` intermediate is introduced. The operand and the complete
predicate retain their source claims. The operand runs once through the
existing tag-test plan and graph rules. `"object"` is one more tag,
`typeofObject`, which holds of null and of an object without call code, since
`typeof` names every callable object, a class included, `"function"`
([Guards](#guards)).

Only a syntactic immutable variable may carry the guard's refinement into a
branch. The tested slice keeps the atoms of that shape (for `isFun`, the
callable signatures) and the failed test keeps the others; testing a call or
mutable read does not refine another expression. The OCaml producer also
refines the rest of a block after an `if` whose one arm always returns, by the
test the other arm took.
The TypeScript producer follows the same explicit guard edges for fixed binding
contracts and immutable captures. [guards.ts](tests/callables/guards.ts) checks
mixed unions, a returning negative guard captured by a thunk, and a call operand.
Forged polarity, variable identity and stronger result guarantees are rejected.

### Guards

**Principle.** A guard is a test JavaScript defines exactly: it is followed
where the model answers it as JavaScript does, as one more tag test (`Tag`,
`tagHolds`), so it narrows by the one mechanism of tag observations
(`tagSlice`, `tagClause_sound`), and it is refused, with the reason, where the
model would answer otherwise. A thrown `TypeError` is an allowed outcome, but
a test the model answers where JavaScript throws is not: a `catch` would then
run where the model says nothing throws.

**`typeof`.** `typeof v` is one of eight strings, each a set of values the
tags already name, plus `typeofObject` for `"object"`: null, or an object
without call code. Every callable object, a class value included, is
`"function"` (`isFun`): the model's `[[Call]]` and `[[Construct]]` codes are
what JavaScript's `typeof` reads. A record, dictionary or array type holds
only objects without call code, so `typeof x === "object"` keeps exactly those
arms and `null`, and its failure keeps the primitives and callables
(`typeof.ts`: tuples, arrays, class instances, promises). TypeScript agrees,
except that it lets a primitive meet a record type (`{ length: number }` is
met by a string), which the model's record types do not admit.

$$
\frac{\Gamma(x)=A\quad\Gamma[x:T_{\mathsf{typeofObject}}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{typeofObject}}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{typeof}\ x\equiv\texttt{"object"})\ S_1\ \mathsf{else}\ S_2}\ \textsc{if-typeof-object}
$$

`typeof e` read as a value is the string of the first answer whose tag holds,
in the order undefined, object, boolean, number, string, bigint, symbol, and
`"function"` for a value none holds of ([derived form](PROGRAM-TYPING.md#derived-source-forms));
its claim is `string`. `typeof x === typeof y`, or `typeof x` compared with a
name, is then the strict-equality operator on two strings, which narrows
nothing. A `switch (typeof x)` compares a temporary and narrows nothing either.

**`in`.** `key in o` evaluates the key, then the object, and asks whether the
object has the key, its own or one its prototype chain holds; it throws a
`TypeError` on a primitive. The model's test (`hasKey`) asks the same along
the prototype keys it holds (`tagHoldsIn`, `keyInChain`: the object's own
fields, then its prototype's, as far as the heap reaches). The two agree on
the objects of the fragment for a key none of the realm's prototypes holds and
whose own keys the model keeps as JavaScript does:

- *Plain objects and class instances.* A record literal's prototype is
  `Object.prototype`; a class instance's is its class's, which the model
  holds under the prototype key with the class's methods (a derived class's
  linking to its base's), and whose other key, `constructor`, is
  `Object.prototype`'s name too. So a key that is not one of
  `Object.prototype`'s names is found in the model exactly where JavaScript
  finds it: `"m" in instance` holds of a method `m`.
- *Arrays.* An array owns `length` and its indices, which the model keeps in
  the store, and inherits `Array.prototype`'s names: those are refused. Its
  other own keys are the model's ([Arrays may carry other own keys](#arrays-may-carry-other-own-keys)).
- *Functions.* A function owns `length`, `name` and, for an ordinary one,
  `prototype`, and inherits `Function.prototype`'s `apply`, `bind`, `call`,
  `arguments` and `caller`: refused. A class value is refused as an operand:
  its static members are bound apart from it (`static C.x`), so it lacks
  keys JavaScript's has.
- *Values from a declaration or the library* (a `Promise`, a `Set`, an
  imported object) are what their type says, as for every other operation.
  An open type admits a value owning any further key, so the test's answer
  on them is not fixed, and either answer is some value of the type.

The refused names are `Object.prototype`'s, `Array.prototype`'s and
`Function.prototype`'s own string keys, as node lists them
(`Object.getOwnPropertyNames`), array indices, and the keys the model
reserves (`[]` and every name in double brackets, `[[proto]]` and a class's
prototype key among them): `inKeyRefusal`, a trusted list, since a realm
whose prototypes hold another string key would answer `true` where the model
answers `false` ([What remains assumed](#what-remains-assumed)). The operand
must be of object types (`inOperand`): a union with a primitive arm, or
`unknown`, is refused, as TypeScript refuses it (TS2361), and `unknown` after
`typeof x === "object" && x !== null` stays refused since no type here names
every object. A key is a string literal or a name whose type is a union of
string literals, dispatched on its singletons (`inKeysTerm`); a key of type
`string` may be any of the refused names and is refused, and a numeric key
names an array element, which the model keeps in the store.

$$
\frac{\Gamma(x)=A\quad A\ \text{objects, no class value}\quad \kappa\notin\mathcal R\quad
      \Gamma[x:T_{\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{"}\kappa\texttt{"}\ \mathtt{in}\ x)\ S_1\ \mathsf{else}\ S_2}\ \textsc{if-in}
$$

Narrowing is by keys the types state (`inAnswer`): a failed test drops an
arm that owns the key (a required field or view), and a passed one drops an
arm whose key bounds exclude both it and the prototype key (a fresh literal)
and every primitive. An arm that may hold a prototype, a class instance's
exact type among them, answers nothing, since its prototype may hold the
key; so does a method, which the object or its prototype may hold. An answer
reads no prototype (`tagClause_protoFree`), so it is the test's in any heap
(`answers_heap`); an edge's observation of a test that read one says only
that it did (`Observation.holds`). A passed test keeps an open record that does not name the key:
it may own it at any type. TypeScript narrows `{ a: number } | { b: string }`
to its first arm there, which is unsound: `{ b: "", a: "x" }` is a
`{ b: string }` (`invalid-in-open.ts`; SKJS refuses the read too).
A passed test also promotes: after `"f" in x` with `x: { f?: number }` the key
is the object's own, since an object of a record lacking one of its optional
keys holds no prototype that could have answered (`optT`), and an object keeps
its keys, so each record of `x` holds with `f` a field of the same contract
(`promote`: `optT` of a present key against `recT`, or a view for a readonly
key), and `x.f` reads a `number`
([rule](PROGRAM-TYPING.md#refinement-under-an-observed-outcome), `present-key`).
`Closed<T>` is read as `T` by the environment, so its absent keys prove
nothing.

**`instanceof`.** `x instanceof C` looks for `C.prototype` along `x`'s
prototype chain, unless `C` has a `[Symbol.hasInstance]`, which it then
calls. For `C` a class the file declares at its top level, as TypeScript
binds the name, the model identifies that prototype by a key only it owns:
`C.[[prototype]]`, allocated once at the class's definition, owns
$\kappa_C$ (`[[C.prototype]]`, at `undefined`; a name in double brackets,
which no source key spells: `Fragment.reservedSourceKey`), and
`x instanceof C` is `hasKey` of it, the test `in` is, after evaluating `x`
and reading the prototype's binding, so a test before the class's
definition fails as a read of the class does
([derived form](PROGRAM-TYPING.md#derived-source-forms)). The two answer
alike: the key is along `x`'s chain exactly where that prototype is, since
no other object owns it; a derived class's prototype links to its base's
("Class inheritance"), so an instance of `D extends C` finds it; a primitive
answers `false` in both; and the prototype itself, which owns the key where
JavaScript's answer is `false`, is no value a source term reaches, since no
operation of the fragment reads a prototype object. A constructor from
elsewhere (an ambient or imported class, a function, a class-valued
expression) gives its instances a prototype nothing in the file names, and
is refused.

Narrowing is the key test's (`inAnswer`): a passed test drops primitives and
fresh literals, whose key bounds exclude both $\kappa_C$ and the prototype
key, and a failed one drops nothing, since no type states $\kappa_C$
present. So `x: Box<number> | string` is a `Box<number>` where
`x instanceof Box` holds (`instanceof-class.ts`). A failed test removes no
class arm: a class type is structural, and an object of its shape made
elsewhere meets it without the prototype; SKJS does not narrow there either.
TypeScript's narrowing of `unknown` to `C` is not taken, and a member read of
such an operand is refused with the reason: it needs "an object whose chain
holds `C`'s prototype has `C`'s fields". That holds of every object the
program makes, since only `C`'s constructor and its subclasses' allocate
with that prototype, each checked against `C`'s type, but it is a fact
about every allocation, a world invariant, not about a value of `unknown`,
whose meaning admits every object. `instanceof Array`
is `Array.isArray` ([Library globals](#library-globals)). A class declaring
a static `[Symbol.hasInstance]` makes `instanceof` a call of that method with
`x`, its result read by `ToBoolean`, and no narrowing: that is how it would be
admitted, once a computed static method is.

**User-defined guards.** A predicate `x is T` promises two things TypeScript
never checks: a `true` result means `x` is a `T` (the passed branch narrows to
`T`), and, for the failed branch to narrow to the rest of `x`'s type, every
`T` gives `true`. Both are facts about the function's result relative to its
argument, which no function type here states. A body with a predicate
return type is refused, as SKJS refuses it (`type-predicate-requires-no-body.ts`);
a declared one reads as a function returning a Boolean, and SKJS does not
narrow through it either (`gap-type-predicate-narrowing.ts`). No accepted unit
of the corpus narrows through a guard. The sound form is a contract on the
result checked against the body, as an assertion function's `asserts x is T`
would be a contract on returning at all; both are future work.

### String concatenation, templates and `void`

`+` with a string operand is the same `arith` term, rule and `binop` as the
numeric operators, not a second mechanism: `binop` concatenates, and
`opResult` classifies the pair as a string. The decisions:

- **What converts without code is admitted, exactly.** The other operand may
  be any primitive but a symbol: its `ToString` is a total function of the
  value that runs no code, which the calculus defines (`primString`). A number
  converts by `Number::toString` itself, digit for digit (`numberToString`,
  checked against node), so the concatenation's value is the one JavaScript
  computes, not an approximation. Where several shortest digit strings
  round-trip, the specification leaves the last digit to the engine and
  recommends the closest; the calculus takes that one, as V8, SpiderMonkey and
  JavaScriptCore do. Only values depend on it, never a type: every result is
  the `string` family. TypeScript admits these operands beside a string, so
  this follows it.
- **What converts through code is refused.** An object concatenates through
  its own `toString`/`valueOf`, which may run anything; TypeScript admits it,
  and the rule refuses it (`invalid-concat-object`). A symbol's conversion
  throws a `TypeError`, which the calculus steps to; TypeScript refuses it,
  and the rule follows (`invalid-template-symbol`).
- **One kind of result.** A `string | number` operand added to a number is a
  string or a number by the value; the rule wants every clause pair to agree
  and refuses it, as TypeScript does.
- **Templates are concatenations.** The parser writes a template literal as
  the left-nested `+` of its parts, starting from the first string part, which
  makes each `+` a concatenation and converts each substitution where the
  template does, in order. `ToString` on a primitive and `+`'s `ToPrimitive`
  then `ToString` agree, so the rewrite is exact on the operands the rule
  admits. Each partial concatenation is claimed at its own span, from the
  template's start to the end of its last part; the whole, at the template's.
  Tagged templates remain outside the fragment; template literal *types* are
  a type form.
- **Increments stay numeric.** `x++` converts `x` to a number, which `x + 1`
  does not for a string, so the lowering of an increment requires a target of
  one numeric family (`invalid-increment-string`); `s += e` is `s = s + e` and
  concatenates.
- **`void e` is a comma.** The comma operator `a, b` is one source form: `a`
  for its effects, then `b`'s value, claimed at the comma and proved from
  `b`'s. `void e` is `e, undefined`, the `undefined` a literal at the keyword.
  No calculus term or rule is added: the lowering binds `a` in an unread
  slot.

### Enums

An enum is what TypeScript's emit makes of it, and its types say exactly
that. With $m_1,\ldots,m_n$ its members and $v_i$ the value TypeScript
computes for $m_i$ (`getConstantValue`: a literal, an auto-increment, a
folded constant expression or an earlier member):

- **`enum E { … }` is a module constant.** The emit creates an object and,
  in member order, sets each member's property to its value and, for a
  numeric value, the property its `ToString` spells to the member's name (the
  reverse mapping; a later member with the same value overwrites it). The
  parser writes the statement `const E: typeof E = {…}`, the allocation of
  exactly those properties in JavaScript's key order, each at its literal,
  where the declaration is: initialization order is a constant's
  ([Modules and code units](#modules-and-code-units)), and every field is
  readonly, so no verified code writes it.

  $$
  \frac{\forall i.\ v_i\ \text{computed by TypeScript, finite if a number}\quad
        \text{no reverse key names a member}}
       {\texttt{enum E}\{\vec m\}\ \leadsto\ \texttt{const E}:\mathcal O(E)=\{\overline{m_i:v_i},\ \overline{\mathrm{str}(v_j):\text{"}m_j\text{"}}^{\,v_j\in\mathbb R}\}}
  $$

  with $\mathcal O(E)$ the object type of those fields, each readonly at its
  value's literal type. That value is the one the emit writes: TypeScript
  folds a constant member into its literal in the emitted code, so trusting
  its value is trusting the front end, as reading any source is.
- **The types are the value sets.** The type `E` is
  $\bigcup_i\{v_i\}$, the union of its members' literal types (`never` for
  none), `E.A` the literal type of `A`'s value, and `typeof E` is
  $\mathcal O(E)$. So two enums with the same values are the same type, as
  SKJS has them (TypeScript's nominal enums are a checker convention, not a
  runtime fact), and TypeScript's rule that any number is a numeric enum,
  kept for bit flags, is not followed: it is unsound for the value set
  (`invalid-enum-number`).
- **`const enum` runs nothing.** TypeScript writes a member's value in place
  of each read `CE.A` and `CE["A"]`, and emits no object; the parser does the
  same where TypeScript binds the read to the member (`constEnumReads`), and
  the declaration is no statement. `declare const enum` is the same.
- **Refused, with the reason.** A member TypeScript computes no value for
  (`A = "abc".length`, a call): its reverse mapping is keyed by its value at
  run time, which an allocation with fixed keys cannot name, and its type
  would be every number (`enum-computed-refused`). A NaN or infinite value,
  which has no literal type. A reverse key that is also a member's name. An
  ambient `declare enum`, whose object the environment supplies and whose
  declaration need not state every value. An enum TypeScript reports an
  error in. An enum without members allocates an object with no field,
  outside the fragment. A type `E` inside another declaration's body (the
  declaration reader does not read enums; `typeof E` there is refused with
  that reason). `keyof typeof E` is the union of the member names, as
  TypeScript computes it ([Computed types](#computed-types)).

### Object literals

An object literal allocates one object owning exactly the properties it
writes, each a data property at the value its initializer gives, evaluated in
order; one with a spread of a value is an allocation from parts. What the
parser admits, and why the rest is refused:

- **Keys.** An identifier, a string, or a number, whose property is the one
  its `ToString` spells (`{0: x}` owns `"0"`, `{1e3: x}` owns `"1000"`), as
  `ToPropertyKey` has it; a type literal's numeric name is read the same way.
  `__proto__` sets the prototype and is refused. A computed key `[k]` is
  refused: its property is known only by evaluating `k`. A key written twice
  as a field is refused, spreads between them or not.
- **Methods and shorthand.** `m() {…}` is an ordinary function expression in
  a field and `{ x }` is `{ x: x }`.
- **A spread of an object literal is its fields.** `{ a, ...{ b: e } }` is
  `{ a, b: e }`: the inner object is fresh, so it owns exactly its written
  keys, its allocation is unobservable, and copying reads back the values it
  was built from, in the order they were evaluated.
- **A spread of any other value copies its own enumerable properties** when
  it is evaluated, the later parts' over the earlier ones'
  (`CopyDataProperties`). The literal is a chain of merges from a fresh
  accumulator: the fields before the first spread allocated together, each
  spread copied onto what is built so far, each later run of fields
  allocated and copied on too ([the step](SEMANTICS.md#operational-language),
  `Tm.merge`). In a closure body the chain is one nested term; in a graph
  body each merge is a node right after its operand's, so the copy reads the
  operand before any later part runs. A field is built at the type the
  literal's claim states for it. What a spread copies: a plain object's fields
  under string keys the model does not reserve, and an array's elements under
  their index keys; nothing from `null`, `undefined`, a Boolean, a number, a
  bigint or a symbol. A string (its code units), a function (the model gives
  a closure a field JavaScript's lacks) and a class value (its static fields
  are bindings here) are refused as operands. A symbol-keyed field is never
  copied (What remains assumed).
- **What a copy is known to hold** is decided per pair of the operands'
  clauses ([the rule](PROGRAM-TYPING.md#allocation-from-parts)): a field
  after a spread is the literal's; one the source's type names is the
  source's, writable whatever it was; one before a spread survives only where
  the source never has its key or has it within the field's type, since an
  open record may own any key at any type (`invalid-object-spread-before.ts`;
  TypeScript keeps the field's type); a union operand distributes, one result
  per alternative; a class instance's methods, its prototype's, are not
  copied (`invalid-object-spread-method.ts`); an `Error`'s `message`, which
  is not enumerable, is not either (`invalid-object-spread-error.ts`). The
  copy is exact where every part's keys are, as a fresh literal's are: a
  literal spread directly, or as an arm of `&&`, `||`, `??` or a
  conditional, is claimed with its exact keys (`cond && { y: 1 }`).
- **An object pattern's rest** `const { a, ...r } = x` is the same copy onto a
  fresh object, less the keys the pattern names (`object-rest.ts`).
- **Accessors are refused.** `get x() {…}` runs code on every read of `x`
  and `set` on every write; the heap model's properties are data only.
- **A write never adds a key.** An object's keys are fixed at its
  allocation (`alloc`); a write stores at an existing location. So a write
  of a key no arm of a record's type has (`let o = {}; o.x = 5`, SKJS's
  growth of a local object, which TypeScript refuses) and a write of a
  writable optional field (`x.opt = 3`, which adds the key where the object
  was allocated without it) are refused by the producer with that reason
  (`object-growth-refused.ts`, `optional-write-refused.ts`) rather than
  reaching search as an unexplained failure. A readonly optional field is
  not refused there: it grants no write, and Lean refuses it as such.
  Admitting growth needs a key-adding write in the calculus, whose typing
  changes the object's own-key bound at a point where no other reference to
  it exists; a write through an index signature is the same step.

Next: a copy whose result states an index signature (a spread of a
dictionary into one; 4 units), which needs an index on the result clause
with every copied location at its type; `Object.assign(t, s)`, which defines
on the existing `t`, whose keys the model fixes at allocation.

A type literal of construct signatures only, `{ new (x: number): T }`, is the
constructor type it states, `new (x: number) => T`; several are overloads of
the one value, as a constructor type's forms are. A literal mixing construct
signatures with other members is still refused.

### Optional chaining

`r?.b`, `r?.[k]`, `r?.(a)` and `r?.m(a)` are one derived form, `optional`,
the shape of `??` with the arms exchanged
([PROGRAM-TYPING.md](PROGRAM-TYPING.md#derived-source-forms)):
the receiver is evaluated once and saved; `undefined` where it is null or
undefined; otherwise the rest of the chain runs on the saved value, read as
the variable `?.`, a name no source identifier can have. The decisions:

- **The chain is the unit, not the link.** Every link after a `?.` belongs to
  its body, so `r?.a.b` never reads `.b` of `undefined`, as JavaScript's
  short-circuit has it. A later `?.` tests the chain so far; nesting the two
  forms gives the same value and the same effects, since the inner form's
  `undefined` is what the outer one tests.
- **Claims have sites of their own.** The saved receiver's read is spelled at
  the `?.` token and each body node from that token to its end, so no body
  node shares a span with the chain or the receiver, whose claims differ (the
  chain adds `undefined`, the saved value drops null and undefined).
- **A receiver that is only nullish.** `null?.f` is `null, undefined`: the
  literal is the receiver's whole value, so the lowering is exact whatever the
  claims, and the body, which would read a field of nothing, never exists.
  Any other receiver keeps the body, which Lean checks at the present slice.
- **`o.m?.()` is refused.** It tests `o.m` but calls it with `o` as its
  receiver; the form saves only the tested value. Nothing in the corpus
  writes it.

### Numeric operators and bigints

Every binary operator the fragment has on primitive operands is one term,
`arith`, with one meaning (`binop`, [semantics](SEMANTICS.md#operational-language))
and one typing rule ([`arith`](PROGRAM-TYPING.md#judgments-and-constructor-views)):
`+ - * / %` and `**` on two numbers or two bigints, and `< <= > >=` on two
numeric operands of either kind or on two strings, and `+` concatenating a
string with a primitive ([String concatenation, templates and
`void`](#string-concatenation-templates-and-void)). `**=` is a compound
assignment through the same rule, as `+=` is. The decisions, each from what
JavaScript does:

- **Where JavaScript throws, the calculus throws.** A bigint division by zero,
  a bigint remainder by zero and a negative bigint exponent throw a `RangeError`, an outcome
  ([Throws](#throws)): the divisor and the exponent may be any bigint, as
  TypeScript admits. Arithmetic mixing a number and a bigint throws a
  `TypeError`, as does `+` on a bigint; TypeScript refuses both, and the rule
  follows it.
- **Where JavaScript converts, the rule refuses.** A relational operator on a
  string and a number converts the string, on an object runs its `valueOf`, on
  Booleans converts them to numbers. TypeScript refuses the first and admits
  the others; the rule admits only the combinations whose comparison is the
  primitive order of the operands as they are: two numeric values, compared
  exactly across number and bigint (no rounding of the bigint to a double), or
  two strings, by UTF-16 code units. Comparing two Booleans is well defined
  and refused, an incompleteness (`boolean-comparison`).
- **Types say what is true, and no more.** The result of arithmetic is the
  family of its operands, never a singleton; a comparison is a Boolean holding
  both literals. `1n + 2n` is a `bigint`, as `1 + 2` is a `number`.
- **Unary operators are the binary one.** `-x` is `x * -1`, `+x` is `x * 1`
  and `~x` is `x ^ -1`, exactly, on doubles (`^` is exclusive or after
  `ToInt32`, as JavaScript's) and on integers. Lean lowers the source form by
  the operand's claimed family, which the operand's own obligation
  establishes, so no second mechanism types them. `^` itself is in the
  calculus for `~`; the gate does not admit the binary bitwise operators.
  A sign written on a decimal numeric literal is part of the literal, as
  TypeScript types it: the parser reads `-1` and `+1` as the numbers -1 and
  1 (unary `+` returns a number operand unchanged), so `[+1]` is an
  `Array<1>` (`unary-plus-literal.ts`); on any other operand the sign is the
  operator above.
- **`%` is the exact remainder.** On two numbers it is `Number::remainder`,
  which never rounds: the result `n - d * trunc(n / d)` is always a double, so
  `remBits` computes it on the integers both operands are multiples of and
  encodes it back, with the dividend's sign; NaN, infinities and zeros as the
  specification lists them. It is not C's `fmod` through Lean's `Float` (Lean
  has none), and not `n - d * trunc(n / d)` in doubles, which rounds. On two
  bigints it is the truncating remainder (`Int.tmod`), and throws a
  `RangeError` on a zero divisor (`binopThrows`), an outcome, as for `/`: any
  divisor is admitted. `%=` is a compound assignment through the same rule.
- **A bigint is its integer.** Its identity is its value, as a number's is its
  double, so `16n`, `0x10n` and `1_6n` are one singleton. The trusted parser
  writes every bigint literal, and every bigint literal type, as its
  canonical decimal integer (JavaScript's own `BigInt` of the spelling), and
  folds a negated literal into a negative one, as it does for numbers; Lean
  refuses a non-canonical spelling. `typeof x === "bigint"` is the existing
  `isBigint` shape test, which a bigint singleton answers as the family does.
- **The `BigInt` function is a library global.** `BigInt(v)` calls the global
  `BigInt`, read through the reviewed overlay
  ([Library globals](#library-globals)) as declared: it returns a bigint or
  throws (`bigint-conversions`).

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

### Truthiness

**Principle.** JavaScript reads any value as a condition by `ToBoolean`, and
`&&`/`||` return an operand, not a Boolean. Both are followed exactly.
Truthiness is one more tag test, $\mathsf{truthy}$, false exactly on `false`,
the two zeros, NaN, `""`, `0n`, `null` and `undefined`
([semantics](SEMANTICS.md#operational-language)). A truthiness guard, `!x` of
a value that is not a Boolean and the value-level `&&`/`||` are then the
existing tag machinery on that test: `tagBind` edges, `unionVar` with
`ifTag`, `ifBool` on the test where a label's answer is not settled, and
`tagSlice` refinement ([derived forms](PROGRAM-TYPING.md#derived-source-forms)).
No typing rule is added.

**Types say what is true.** A number's falsy part is the whole family, since
no type here names $\{0,-0,\mathrm{NaN}\}$; TypeScript's `0` for it forgets
NaN and is not followed. SKJS's default truthiness mode refuses a number or
string condition or left operand; the pipeline accepts it at that exact type.

### Strict equality and tag narrowing

**Principle.** `===` is exactly defined on every JavaScript value
(`IsStrictlyEqual`: `Number::equal` on numbers, content on the other
primitives, identity on objects) and converts nothing, so it is followed
exactly, with one mechanism for each of its two uses: a comparison with a
singleton is a tag test, which narrows; any other is one more binary operator,
which computes a Boolean and narrows nothing.

- **Singletons of every primitive kind.** A claimed singleton operand selects a
  tag test on the other operand (`comparisonsExpr`): `null`, `undefined`, one
  number (`numEq`, both zeros one), one string (`strEq`), and now one Boolean
  (`boolEq`) and one bigint (`bigintEq`). Each is false on every other kind,
  so a union loses exactly the labels the test excludes (`tagSlice`), on both
  edges, as for null. The singleton operand stays in the program with its own
  obligation; it may be a literal, a name or a field read holding one. The
  name may be a module value's, and the field one of a module value's (an
  enum member `E.A`, an ambient constant's field), read at its declared type
  as the producer proposes the narrowing (`module-value-equality.ts`).
- **Strict equality without a singleton** is the operator
  $\equiv$ (`Arith.eq`, the `arith` rule; [semantics](SEMANTICS.md#operational-language),
  [rule](PROGRAM-TYPING.md#judgments-and-constructor-views)), `!==` its
  negation. It answers wherever one operand is a primitive, and on two objects
  where one has a field: an object value is its field locations, which only its
  allocation creates, fresh, so two such objects are one exactly when their
  locations are. That correspondence (distinct JavaScript objects have
  disjoint field locations) is a modelling assumption of the lowering, like
  plain-data fields; it holds because `makeV` is the only step that creates
  an object value. Two operands that may both be objects without a field (a
  function, a record of optional fields only, any value of `unknown`) carry no
  identity here and are refused with that reason: two closures with no field
  would be the same value though JavaScript tells them apart. It narrows
  nothing: that two slots hold one object is a slot equality, which knowledge
  carries within a statement, and a statement entry states no equality, so
  after `if (x.child !== narrow) return 0;` a later read of `x.child` is not
  `narrow`'s type (TypeScript refuses that return too).
- **Two unions of singletons narrow as their tag tests.** A condition
  `x === y`, with `x` claimed at a union of singletons, is the disjunction
  over `x`'s singletons $c$ of $x\equiv c\land y\equiv c$. Where both
  operands are read without effect (a name, or a field of a name; `x` a name
  where it can be, else a field), the graph runs the comparison as the source
  has it (its Boolean dropped, its obligations kept), then dispatches by those
  tag tests, re-reading the operands, which nothing between has written; a
  field read is saved and its copy tested, as a guard's saved read is, so the
  copy states what the value is and its link what the field holds. Where `x`
  is evaluated with effects (a call) and `y` is an immutable name, `x` is
  evaluated once into a slot of its own and split there, the comparison's own
  claim a supplemental obligation, and `y`, which no effect changes, is read
  where it is (`savedSplit`). Each edge refines by the one mechanism of tag
  observations, so both operands (and the objects' arms, for fields) narrow
  where they are equal, and each path states what a field it tested holds:
  where several paths meet at the true edge's target, each covers the
  target's claim. The dispatch is exact: `x` holds one of its claimed
  singletons (each read of it is typed at that claim), strict equality is
  transitive where it holds, and a NaN, equal to nothing, fails every test
  and takes the unequal edge. `!==` between two such unions narrows neither
  (either may still be anything it was).
- **An observation the tested type rules out** (a Boolean `x: true` found
  false, a tag no label answers) makes its edge never taken: the edge
  constrains nothing (`impossible`), so the `else` of `if (x)` may claim
  `x: never`.
- **Discriminated unions.** A test of a field of an immutable binding's object
  against a singleton (`s.kind === "circle"`) keeps the arms whose field
  admits the outcome. The saved read's current read link names the object and
  the field, and the branch edge may then refine the object's slot to its field
  slice ([rule](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)): a heap meeting the
  world holds, at the field's location, a value of the field's contract, so an
  arm whose field answers the other way is not the object's. The arm is fixed
  at allocation, so the refinement is timeless: a write or a call after the
  test does not undo it, and a readonly or a mutable field serves alike. The
  producer holds an immutable binding declared at a named union at its arms
  (the same values), so a read splits on them and a guard keeps or drops each.
  A read of a field that every arm has, at different types, records its link
  (`typedRead` over `fieldOperand`).
- **What a field holds after a guard** is a current-content fact
  (`obj.val !== null`, then `return obj.val`): the producer claims it at the
  entries that follow, as the field's `current` assertion, until a step may
  write it (a write or a call forgets it), and Lean checks it on every edge
  ([current-content assertions](#current-content-assertions)). A record, or a
  union of records each naming the field, carries one: the fact names the
  location the field is at, whichever record the object is. A family found
  equal to one of its values is that value (`x.f === 1` with `f: number`
  gives `x.f: 1`; equal to a zero it stays `number`, since the zeros are two
  values, and a slot is narrowed alike, `x === 1` giving `x: 1`).
- **A key found present.** A key some record of the object names only as
  optional may be absent, and a fact names a location. A read that found it
  says so: `"f" in x` passed, or a read of `x.f` whose value is observed not
  to be `undefined` (`x.f !== undefined`, `if (x.f)` where `f`'s contract
  excludes `undefined`), since a record lacking an optional key has no
  prototype and reads it as `undefined`. The object keeps the key from its
  allocation on, so its slot is promoted, each record with the key present
  (`promote`: a writable optional key an invariant field, a readonly one a
  view), and it stays so across writes and calls, as TypeScript narrows `x`.
  A read through the key records an optional read link, whose observation
  also states what the field holds ([rules](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)).
  `x.f === undefined` on such a key leaves presence open (a present key may
  not hold `undefined`, but an absent one reads it), so no fact follows:
  knowledge of an absent key would need a record clause whose bound excludes
  the key and a read rule for it (`field-refinement.ts#testOptionalFieldEqualsUndefined`).
- **`switch` case narrowing** falls out: each case is a `===` test of the
  discriminant, a `break` leaves with what its path knew, and the producer
  joins every `break` of a label (and the completion of the block's body) at
  the block's end. A discriminant that is a name, or a field of a name, is read
  again at each test (nothing between the tests writes, and a field is a plain
  location), so a case narrows the name or the object's arms as an `if` does;
  any other is bound once to a temporary, whose narrowing reaches nothing
  else. A switch whose cases cover the discriminant's type leaves its last
  dispatch with the discriminant at the empty type: a jump whose entry claims
  a binding of the empty type is unreachable, and completes the function
  instead, so an exhaustive switch never falls off the end.
- **Loose equality** is admitted only as `x == null` / `x == undefined` (and
  `!=`), which hold exactly of `null` and `undefined` (the nullish test).
  Against anything else `==` converts its operands (`ToNumber`,
  `ToPrimitive`, which may run code), and the parser refuses it with that
  reason.

$$
\frac{\Gamma\vdash a:A\quad \Gamma\vdash k:\{c\}\quad
      \Gamma[x:T_{\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_1\quad
      \Gamma[x:T_{\lnot\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (x\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsc{if-singleton}
\qquad
\frac{\Gamma\vdash k:\{c\}\quad
      \Gamma[o:F^{f}_{\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_1\quad
      \Gamma[o:F^{f}_{\lnot\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (o.f\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsc{if-field}
$$

where $T$ is the tag slice and $F^f$ the field slice of a type, and $x$, $o$
immutable bindings. The producer follows TypeScript in one related inference:
a fresh object literal's field widens a literal's type (`{ v: 0 }` is
`{ v: number }`) but keeps a name's or a read's declared one (`{ v: seed }`
with `seed: 0 | 1` is `{ v: 0 | 1 }`).

### Compositional unions at the source boundary

`Fragment.translate` now decodes each union atom through its existing primitive,
cell or function decoder, then canonicalizes the combined labels. It rejects the
entire type if any arm fails. This needs no new graph label or semantic rule:
label lists already denote unions. Required fields, function and constructor
arguments and results recursively admit object, callable, array and primitive
contracts through `Fragment.callableType`. Plain records use the same decoder
as receiver contracts: mutable fields keep fixed read/write contracts and
readonly fields grant views. This removes the former difference between an
object used as a receiver and the same object used as an ordinary argument.
Optional and indexed fields retain their explicit restrictions.

An intersection of such records is lowered by the one meet a declaration's
intersection gets (`meetLists`, the [`meet` rule](#one-row-per-application)),
not by a separate conjunction of cells. With $\varphi_i$ the invariant fields
and $\psi_i$ the readonly fields of the record $R_i$ (read and write equal, or
write empty; any other field is refused, and so are optional and indexed
ones),

$$
\frac{\forall i.\ \llbracket R_i\rrbracket=\mathsf{Ref}(\varphi_i;\psi_i)}
     {\llbracket R_1\mathbin{\&}\cdots\mathbin{\&}R_n\rrbracket=
      \mathsf{Ref}(\varphi_1\cdots\varphi_n;\,\psi_1\cdots\psi_n)}\ \textsc{record-meet}
$$

with each field list sorted and deduplicated, since conjunction is
commutative and idempotent (`Fragment.cellConjunction`). It is exact:
$\mathsf{rec}(\varphi\varphi')=\mathsf{rec}\,\varphi\cap\mathsf{rec}\,\varphi'$
(`recT_append`), and a list of views holds when each view does. So
`{ readonly value: number } & { readonly tag: "ok" }` is one object read at
both views (`readonly-intersection.ts`); before, a readonly conjunct was
refused. A view still grants no write, though TypeScript lets the
intersection meet a writable record (`invalid-readonly-intersection.ts`).

The literal type `0` denotes both runtime zeros (`SourceTypes.numberLabels`;
TypeScript types `-0` as `0`). The OCaml producer reads an annotation's `0`
the same way (`Semantic.number_literal_type`), while a literal *value* keeps
its own bit pattern; before, it claimed only `+0` and every parameter or
result annotated with `0` was refused as differing from its annotation
(`zero-literal-type.ts`, `invalid-zero-literal-type.ts`).

Locally allocated nullable cells and optional checked-closure results exercise
the extension. External object and callable parameters are assumptions under
the semantic contracts described above; their annotations do not themselves
prove that arbitrary JavaScript callers obey those contracts. The null-guard
examples include local annotation checks and functions that return
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
lowering. Value-level operands and truthiness are in [Truthiness](#truthiness). See [derived forms](PROGRAM-TYPING.md#derived-source-forms),
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
unannotated construction. Named/multiple/optional fields and general expando
assignment remain separate milestones; receiver-dependent functions are
[below](#receivers-and-methods).

### Local arrow receiver calls

The source gate recognizes `.call`, `.bind` and `.apply` only on fresh arrows
and function expressions, the restricted callable field initializer, function
members of a `const` object literal that no write in the file can replace,
immutable lexical aliases of those values, including captures, and the file's
function declarations with a body, where nothing between the use and the
module rebinds the name and no write in the file can replace a `call`,
`apply` or `bind` property (an assignment to the declaration's binding is
refused where it is written). It checks lexical bindings rather than relying on a type's call
signature: an arbitrary function parameter or call result could have its own
`call` property. The supported source fragment cannot write that property or
mutate the standard function prototype. As with `Object.assign`, identification
of the standard intrinsic belongs to the trusted source boundary.

`receiver-call.ts` exercises a function with a field and a captured nullary arrow.
Both producers verify its claims. Lowering saves the callee, evaluates and checks
the receiver, then evaluates actuals left to right, and invokes the callee with
the receiver: `invoke f r args`. The receiver's effects persist even though
arrows ignore its value; a JavaScript control that omits the write changes the
result. The independent consumer rejects changed receiver evidence, false
receiver claims and wrong actual counts. Ordinary `this`-dependent methods are
the next section.

### Receivers and methods

Every signature states its receiver, and every call passes one: `undefined` for
a plain call, the object for a method call `o.m(a)` or `(o.m)(a)`, the first
argument for `.call` and `.apply`. An ordinary function expression or
object-literal method binds it as `this`, in the slot before its parameters; an
arrow resolves `this` to the enclosing ordinary function's slot, as a capture.
The receiver rule is the strict one, so the fragment records strictness — a
`"use strict"` directive of the file or an enclosing function body (including
an arrow body). The parser checks strictness at every `this` read, including
declaration entry points and lexical captures, using the binding function's
mode rather than a capturing arrow's mode; the decoder additionally checks
ordinary closure bodies against their recorded strictness. Sloppy receiver
conversion is not modeled, so these reads are refused in sloppy code. A
receiver annotation is lowered like a record contract with its readonly members
as views, so writing through a readonly receiver field is refused. A method call
saves the object, then the method read from it, then the actuals, then invokes;
`methods.ts` shows the saved callee, the live receiver fields, `.call`
rebinding, and a copied method whose plain call fails its `method-receiver`
obligation. `.apply` reads a tuple list's length and indices in order after its
receiver runs (`apply.ts`); a fresh array literal as the list is its elements,
since its allocation is unobservable and `apply` reads back the values it was
built from, in order: `f.apply(r, [a, b])` is `f.call(r, a, b)`. A module
function declared with a leading `this: T` parameter has `T` as its
receiver, not as a position (`moduleArrow`): its unit assumes `this` at `T`
as it assumes every parameter, and its value's signature states the receiver
every call passes, so a plain call, which passes `undefined`, is admitted
only at `this: void` (`receiver-functions.ts`, `invalid-receiver-call.ts`). `generic-receivers.ts` introduces one quantified
function whose receiver is its binder and eliminates it at two receiver
contracts, with a captured cell keeping its one contract.

Both the TypeScript and the OCaml producers verify `methods.ts`,
`call-objects.ts`, `apply.ts` and `generic-receivers.ts` independently. For a
quantified closure the TypeScript producer states the scheme and reads each
call's instantiation from the receiver and actuals it passes, since
TypeScript's own `.call` forgets the binder. SKJS does not parse the directive, so the
corpus reports these files unparsed in its column rather than as rejections, and
the SKJS exporter's `function-this-parameter` refusal is unchanged: no checker
change was made to SKJS for receivers.

The captured receiver test also covers SKJS's optimized local-object assignment
path. That path records the receiver's pre-write type for export without routing
it through the ordinary variable-read operation, which would freeze object
growth. The dedicated `assignment-receiver` export snapshot preserves this
collection obligation independently of the `.call` source lowering.

### Bound arrow arguments

`bound-arguments.ts` distinguishes saved argument values from a target's live
cell capture and returns a fully bound nullary function. The parser restricts
`.bind` to the same source-established provenance as `.call`; a bound
result retains that provenance. Target, receiver and prefix expressions run once
at binding time, in source order. Lowering saves them in native lets, re-binds
the receiver and each prefix value at the contract the selected signature gives
it, and allocates the forwarding descriptor `bound(target, receiver, prefix)`:
invoking it drops its own receiver and invokes the target with the saved one and
the prefix before the new actuals. It is a runtime descriptor, with its own step
and its own safety proof (`callsT_bound`), not an ordinary wrapper closure, so a
second `.bind` or a `.call` on a bound function cannot replace the first
receiver (`rebind_keeps_receiver`).

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
