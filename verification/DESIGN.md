# Independent verification of SKJS results

The goal is to check selected SKJS claims with a small, independently justified
consumer. It is not to prove SKJS's inference implementation sound. SKJS supplies
candidate types and invariants; acceptance requires derivations in an independent
calculus whose rules are proved sound against its execution model.

The chosen architecture has a stateful positive-type calculus, a serialized
certificate consumer, and a source adapter for parameterized null/boolean functions.
The extraction format may change to provide the program points, binding identities and exact
types needed by the chosen calculus.

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
and the older design's reduced example need no numbers, strings, general calls or
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
missing feature is initialized mutable lexical bindings and assignment; loops,
back edges, primitive claims and local allocation already exist. The target is a
failed loop-head/back-edge obligation or the stale read it justifies, not an
unsupported-`let` error. A counterpart that checks the value inside the loop must
verify, with supplied invariants on every incoming edge and no fixed-point inference.

Before implementing `let`, specify binding identity, storage and initialization
once, including capture. The existing stable heap contracts provide a cell-based foundation. A captured variable must denote a
shared location, not the value it held when the closure was created. If uncaptured
locals use graph slots instead, treat that as a deliberate lowering choice with
explicit restrictions and a capture story, not an implicit representation change
when a lambda happens to appear. Explain how point claims about current values
relate to stable storage contracts, and which observations an assignment or call
invalidates. Do not confuse discarding stale refinements with preserving the
storage guarantees of every live alias. Keep shadowing and uninitialized bindings
gated until their identities and initialization obligations are supported.

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
| **Numeric false disjointness — `L-LIT`, deep dive G.** [Witness family](https://github.com/SkipLabs/skjs/blob/bf20814b4c0bfc72305e9e58411e13da68f94bca/docs/deep-dives/issues/beyond-precision-numeric-literals.md). | Distinct decimal spellings can denote the same binary64 value, making a claimed unreachable branch live. It tests runtime grounding independently of mutation. | The current calculus does not model numbers; the historical numeric success is not present coverage. Ground literal conversion, equality, signed zero and underflow first. Do not interpret decimal spellings as distinct mathematical integers. General truthiness and arithmetic are separate additions. |
| **Callability/absence, getters and void.** `F-CABSENT`, `ACCESSOR-METHOD`, `L-SEQ`. | The corpus has concrete reachable-never and non-callable-call witnesses. | They require object-shape guarantees, accessor execution, or an explicit distinction between void as a typing convention and undefined as a value. Preserve the external-object boundary; do not trust structural declarations or treat void as a disjoint runtime tag. |
| **Inference-state and expansion failures.** `MR-1`, `C-FREEZE-CACHE`, `L-SUB-TSINST`, `E-EXPKEY`. | Wrong inferred types remain valid verifier targets even when their cause is a cache or substitution bug. | Select a concrete escaping wrong claim whose ground types fit the calculus. This pipeline should check that consequence, not model SKJS caches, rollback or its entire generic inference algorithm. Universal generic certification needs separate rules; checking one ground instance does not supply it. |

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
the current fixed source graph. The strict
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
and typing rules.

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
| Serialized requests | Versioned requests and evidence pass through a separate JSON consumer in the existing verifier binary. Acceptance yields decoded-request safety. |
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
because the parsers differ on trailing semicolons. Primitive wire decoding lives
in [SourceEncoding.lean](lean/Verification/ExperimentState/SourceEncoding.lean);
cell and function contracts have separate bounded decoders. This input encoding
is not a second calculus or an executable source model.

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
`return`, `break` or `continue` are outside the current source slice. The graph
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
consumer. It accepts primitive parameters, initialized `const` declarations,
nested boolean branches, block-bodied `while` loops and returns, with variables, null/boolean literals,
plain `{ value: e }` allocation, `.value` reads and `.value = e` assignments,
and the bounded local closures and calls described below. Every syntactic exit
path must reach an explicit return; loops may diverge.
It rejects active-name shadowing, calls to named top-level functions, statements after
an explicit return, and unsupported types. This is a coverage gate for this slice, not the intended final dead-code policy.

[SourceTypes.lean](lean/Verification/ExperimentState/SourceTypes.lean) translates
null, boolean, their singleton types, unions and bottom exactly into three
primitive labels: null, true and false. Eight further labels represent invariant
references to the subsets of these values, and sixty-four represent the unary
arrows between them. Lean proves the translation preserves primitive
membership. Singleton clause and typing rules have been added with soundness
proofs; no claim is widened from a singleton to boolean.

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

Protocol version 2 makes the source parameter types an explicit input contract.
The exporter’s parameter signature is checked for matching names, order and types.
A synthetic entry edge must justify the first supplied point claim from that
contract. Lean proves safety for any typed input environment, admissible world
and satisfying heap. Source parameter slots follow declaration order, with
locals pushed ahead of them. This certifies the function body. Local expression
closures use the existing lambda/application rules; graph-backed closure bodies
and external callers remain separate integration work.

The cell-contract boundary is implemented in
[CellClaims.lean](lean/Verification/ExperimentState/CellClaims.lean). SKJS exports
a bounded single-field record with separate read/write types, optionality and
object-mode flags. Synthetic index markers are recorded separately from runtime
permissions; real indexes remain unsupported. The Lean gate requires a required `value` field and equal
read/write meanings after exact primitive normalization. A mutable Boolean
field passes; a readonly Boolean field has `never` writes and fails this
particular invariant-cell gate. Readonly objects need a different capability
interface; this rejection does not mean they are unsafe.

Theorems preserve both primitive sides of an accepted contract and show that
the chosen reference label denotes exactly that invariant. This is not
an equivalence theorem for TypeScript records and calculus references. Record
annotations cannot distinguish data properties from accessors. Establishing
plain-data allocation is the source gate’s responsibility. The parser accepts
only an explicit single `value` data property, with no getters, setters, spreads
or computed keys. Cell parameters remain rejected: an external object needs
a separate plain-data boundary that its structural annotation cannot establish.

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
function's substitution snapshot, without changing inference. Only isolated,
bound variables without constraints are followed, with bounded recursion;
unresolved or recursive cases remain unsupported. Tests check actual allocation
expression claims at Boolean and singleton contracts, contextual field growth,
and preservation of both aliases' contracts after a write. This export mapping
is explicit but is not a proved correspondence with SKJS's internal semantics.

Cell programs now pass through source extraction, certificate production and
independent consumption. [SourceInput.lean](lean/Verification/ExperimentState/SourceInput.lean)
decodes the source AST and routes record types through the contract gate. Every nested expression retains
its own supplied claim. Expression lowering saves intermediate values in
anonymous slots and evaluates the receiver before the RHS. A write uses the
existing calculus rule, then returns the saved RHS to match JavaScript assignment
semantics; temporary slots are discarded by explicit edge maps. An execution
regression checks the extracted alias-assignment graph's heap and result.

The first closure slice is connected through
[FunctionClaims.lean](lean/Verification/ExperimentState/FunctionClaims.lean).
It accepts explicitly typed unary arrows with a null/Boolean primitive argument and a primitive
result. Bodies compose literals, variables, cell allocation, reads, assignments,
and calls, including nested expression arrows with the same signature limits.
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

Straight-line blocks also support initialized `const` declarations and expression
statements before the final return. Each statement entry uses the same checked
environment obligations. Local annotations are separate obligations; bindings
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
through both raw SKJS claims and [version-2 sidecars](SOURCE-CLAIMS.md#current-content-assertions).
Every statement entry is an exact local interface: its supplied ordinary types
and current observations are the whole starting context. Extra derived heap/value
facts and links are forgotten there, even on single-predecessor paths. The
consumer enforces this independently of the producer. Expression-result claims
are checked local obligations within a statement, where effect rules can derive
postconditions. Loop heads use supplied interfaces; every backedge must establish
them. No loop invariant is inferred.

Writes establish new contents for recorded aliases and discard other heap facts;
ordinary calls discard heap observations and read links. Immutable values and
slot equalities survive. Boolean guards refine current cells through checked
read links, including links carried through receiver temporaries. Ordinary
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
3. **Original-witness diagnosis — implemented.** The three unedited exports each
   have exactly one failing heap edge: the required observation at the return
   after the write/callback. Every ordinary expression/edge obligation, external
   entry, and other heap edge checks. Both source formats report the same site.
   [The audit](tests/refinement-witnesses.js) also verifies fresh producer claims
   for [three structurally matched controls](tests/refinement-controls.ts), which
   remove only the invalidating operation. `writeRefinedRead` needs an explicit
   current-true return-entry claim; its original broad claim is insufficient.
   Immutable snapshot controls remain verified.

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
after an unconditional transfer remain gated in this source slice.

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
| More primitives and operators | Define their runtime behavior and validate agreement, particularly numbers and JavaScript equality. |
| Graph-backed closure bodies | Extend the call/body interface if source functions require graph control flow internally; surrounding graph loops are insufficient. |
| Generics and bounds | Add syntax, substitution, disciplined quantification and a uniform program-typing theorem; distinguish regular recursion from parameter-changing aliases. |
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

### Primitive callback integration

The source graph contains all 64 unary arrows between subsets of null, true and
false. `FunctionClaims.translate_exact` proves the selected arrow's domain and
codomain interpretations. Existing application and lambda rules discharge their
obligations; no operational constructor or semantic axiom was added. [Source claims](SOURCE-CLAIMS.md#encoding) specifies the fixed label table and
profile version.

Source-mode search uses labels in the function's request and required-expression
sequents, plus primitive labels. Vocabulary construction includes their operand
types. This is a search restriction, not a restriction on consumer checking or
a completeness claim. Enumerating every unused arrow at each subtype query was
already expensive in this small table; expanding a fixed profile must not silently
expand every local search problem.

The [captured-refinement fixture](tests/skjs-unsound/README.md) pairs a known stale
read with a verified immutable snapshot. It distinguishes the raw contract boundary
from a failed obligation after explicit candidate edits; neither an unsupported
contract nor failed search alone is the runtime counterexample.

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

### Null predicates through union elimination

`HasTy.unionVar` eliminates one variable's finite union by checking the same term
and result under every singleton-label alternative. Its soundness proof selects
the alternative containing the actual immutable value; no semantic budget enters
the rule. The ordinary evidence checker enforces complete coverage and unchanged
other bindings. Derivation-to-evidence completeness is extended with this rule.

The source adapter now checks strict equality/inequality against a null literal,
including inside callbacks and with effectful operands. Both operand claims are
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

`SourceInput.translate` now decodes each union atom through its existing primitive,
cell or function decoder, then canonicalizes the combined labels. It rejects the
entire type if any arm fails. This needs no new graph label or semantic rule:
label lists already denote unions. Cell fields and arrow inputs/results retain
their primitive-only decoders; nested records and richer callable contracts are
not enabled by this change.

Locally allocated nullable cells and optional checked-closure results exercise
the extension. External cell/function parameters remain rejected: annotations
alone cannot exclude accessors or establish a callable implementation. A regression
checks that adding null to such a parameter does not evade this boundary. The
null-guard examples include local annotation checks and functions that return
null on one path and a locally created cell or closure on another.

Source ternary expressions now share the closure conditional proof construction.
They require their own result claim and each operand claim, rather than a
synthetic statement-entry environment. This supports dynamically chosen local
nullable cells and callbacks without changing the external-value boundary or
adding a typing rule. Effectful conditions and selected-arm effects retain their
ordinary sequential evaluation.

Null coalescing uses the same existing null-tag and union-elimination rules:
save the left operand once, evaluate the fallback only for null, otherwise return
the saved value (including false). The fallback may allocate, write or call.
For an immutable variable operand, moving its name to the saved slot exposes its
null refinement; reads and calls confer no retained alias. Both operand claims
remain required. Undefined remains outside the source profile. Examples use
named cell/callback fallback contracts because the current exporter can leave
compound inferred alternatives unsupported; the consumer does not approximate them.

Boolean short-circuit operators reuse the existing conditional rules and source
proof builder. Statement guards use checked graph paths and retain the complete
condition claim as a separate obligation; no condition type is discarded by
lowering. This extends syntax without changing refinement semantics or adding
truthiness. See [derived forms](PROGRAM-TYPING.md#derived-source-forms),
[AST encoding](REQUEST-PROTOCOL.md#expression-closures-and-calls), and the
[regression index](tests/README.md) for their respective details.

The [compound-write witness](tests/skjs-unsound/README.md) connects that syntax
to known issue #598. Its runtime counterexample, original interpretation limit,
and explicitly edited diagnostic candidate are documented with the fixture;
a boundary rejection is not evidence of unsoundness.
