# Independent verification of SKJS results

The goal is to check selected SKJS claims with a small, independently justified
consumer. It is not to prove SKJS's inference implementation sound. SKJS supplies
candidate types and invariants; acceptance requires derivations in an independent
calculus whose rules are proved sound against its execution model.

The chosen architecture is implemented in memory for a stateful positive-type
fragment. The source-facing pipeline still runs F0, the smaller first-order
primitive fragment. Extraction and integration have not yet connected the
stateful checker to that pipeline. These are implementation stages, not competing
semantic designs or a requirement to compare historical calculus versions.

This document records the architecture, established commitments, trust boundary
and remaining work. Details live in:

| Document | Responsibility |
| --- | --- |
| [README](README.md) | Running the existing F0 pipeline and locating its implementation. |
| [SEMANTICS](SEMANTICS.md) | Worlds, heap invariants, operational safety and recursive interpretation. |
| [POSITIVE-TYPES](POSITIVE-TYPES.md) | Type grammar, normalization, declarative subtype rules and their certificates. |
| [PROGRAM-TYPING](PROGRAM-TYPING.md) | Program rules, graph claims, slot maps, certificate production and mathematical statements. |

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
value, discards it, or branches on a boolean. A destination carries a label and
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
outside the current program rules, which use known shape answers per overload.

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
| Source-facing integration | F0 runs end to end. Extraction, claim translation and serialization for the stateful checker remain. |

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

## Running F0 integration

The existing pipeline independently parses TypeScript with the TypeScript
compiler API, obtains SKJS claims, and checks them using `Verify.lean` and the
F0 calculus in `Calculus/`. F0 has primitive types, first-order calls and
narrowing. Its `meet` and `diff` operations belong to that primitive calculus;
they are not established operations of the stateful positive-type model.

For example:

```ts
function describe(x: string | number): string {
  if (typeof x === "string") {
    return x;
  }
  return "a number";
}
```

The parameter and return requirements come from the independently parsed source.
SKJS proposes the environments at the branch and returns. The F0 verifier derives
the branch refinement itself and checks that it covers the supplied successor
claim. It then checks each returned expression against the source return type.
An unjustifiably narrowed claim fails on an incoming edge.

`Verify.lean` constructs and discharges obligations in the same traversal.
`Obligation.discharge_sound` justifies successful comparisons;
`checkFile_sound` establishes typing of the lowered program; `Core.sound`
establishes its modeled execution safety. The file-level result is:

```text
checkFile funs claims = .ok () → ProgOk (lowerProg funs)
```

This is a theorem about the compiled calculus program. It does not by itself
prove that compilation preserves source execution.

### Source association and claim validation

`--emit-skjs-type-claims` exports file entries containing function names and
spans, claimed signatures, expression types and statement-entry environments.
The verifier checks duplicated signatures against source annotations and checks
the body against the source requirements regardless. Expression lookup uses the
full span; environment lookup uses the statement start because the parsers differ
on trailing semicolons. [JsonDecode.lean](lean/Verification/JsonDecode.lean)
defines the exact current format.

The F0 type encoding is `{top, atoms}`, with an explicit unsupported marker.
Required unsupported expression or signature types reject verification.
Unsupported environment bindings are omitted; a binding needed by a checked
expression must still be available and justified. This encoding is not the
stateful type-graph or certificate protocol.

Positions associate claims with independently parsed syntax; they do not
authenticate source contents. Extra entries need not be consumed. Whatever data
lookup returns must satisfy the obligations for the actual AST. There is no
claim cache or production certification command; the harness generates claims
for each run.

Program certification and claim validation are related but distinct. Acceptance
establishes program typing and the required claim relations, not agreement with
SKJS's internal state or exactness of every reported type. A wider claim may be
valid. The duplicated-signature check also rejects inconsistencies that would
not necessarily undermine program safety by themselves.

### Lexical binding and unreachable source

F0 lowering allocates fresh slots and resolves lexical bindings. This is
semantically significant even when all affected bindings have the same type:

```ts
const x = "outer";
if (b) { const x = "inner"; }
return x; // must read the outer binding
```

Declarations bind throughout their blocks. A read before an inner declaration
must resolve to that uninitialized binding, not an outer variable of the same
name. Lowering therefore distinguishes block-wide **resolution** from the
statement-entry **visibility** used to interpret SKJS's named environment claims.
Hidden live bindings retain the types needed when their scopes become visible
again. The current justification relies on F0's immutable bindings; it must not
be reused as a mutation/refinement preservation argument.

F0 omits statements that cannot execute, while still accounting for their
declarations during name resolution. SKJS checks those statements and may emit
claims that F0 does not consume. The stateful graph checker, by contrast, checks
every node present in its input graph, including unreachable nodes. Extraction
must explicitly specify which source statements become graph nodes; these two
facts do not establish a source dead-code policy for the extended integration.

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

Numeric agreement is a known limitation of the running F0 model. Numbers use
double bit patterns with signed zero normalized; NaN truthiness and value
equality do not fully match JavaScript. A `number` parameter can receive NaN even
without arithmetic in the fragment. The Node sampler does not settle these
cases. The stateful fragment currently has null and boolean primitives, so its
proofs do not resolve that F0 limitation either.

### Optional: prove source-to-graph preservation

Lean has access to the F0 source AST and its compiled graph. Some translation
trust can therefore move into proofs; it is not inherently outside Lean's reach.
The same approach can guide the extended extractor.

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

## Next integration milestone

Connect a small source fragment to the existing stateful checking interface
before adding more semantic machinery. Start with constructs already modeled:
null/booleans, invariant cells, supported closures, and graph control flow.
Prefer translation into existing constructs when it preserves source behavior.

The concrete work is:

1. Specify source-to-graph binding and evaluation order, including slot maps,
   initialization, and the treatment of unreachable statements.
2. Associate exported claims with the resulting program points and type graph.
   The current producer takes an entry context **and expression-result type**
   per node. Specify which are source requirements, which come from SKJS, and
   which intermediate annotations the producer may choose and must justify.
   Do not silently treat producer-chosen annotations as verified SKJS claims.
3. Define a serialized request/evidence interface and validate it at the consumer.
   Inspect what the exporter actually supplies; extend its representation only
   where the chosen source slice needs it.
4. Run accepted programs and deliberately corrupted claims through the complete
   path. Include a merge, a loop, and a captured cell modified through an alias.
   Require rejection for the intended claim obligation, not merely unsupported
   syntax or missing data.

Completion means independently parsed source and associated claims reach the
proved stateful consumer, without hand-written derivations per program, with an
explicit account of the remaining translation trust. Evidence production already
works in memory and is not itself the missing semantic foundation.

The existing F0 path remains operational until that replacement covers the source
behavior we choose to retain. Migration does not require a theorem relating old
and new evaluators. It does require an accurate statement of which source
programs the integrated checker certifies.

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

For the running source pipeline, `make verify-programs` exercises programs,
`make verify-claims` mutates valid claim sets, and `make verify` runs both.
The [beyond_precision](tests/programs/known-unsound/beyond_precision.ts) fixture
is a concrete case where verification rejects SKJS's unsound numeric narrowing.
Runtime checks sample calls in Node; they do not prove equivalence with the model.
There is no standing test establishing exporter faithfulness to SKJS internals.

Use Lean checks for Lean development and pipeline checks for extraction or
certificate integration. The repository-wide SKJS tests concern changes to SKJS
itself; they are not evidence for an otherwise unchanged Lean model.

The eventual user-facing command must report certified success only after the
consumer accepts. `--emit-skjs-type-claims` currently emits claims without making
that guarantee. `make verify` remains the experiment's source-facing command.
