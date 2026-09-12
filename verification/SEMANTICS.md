# Semantics

The stateful development in [ExperimentState](lean/Verification/ExperimentState)
provides the semantic foundation for the positive-type rules specified in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md). This is the semantics used by the current verifier. [PROGRAM-TYPING.md](PROGRAM-TYPING.md) specifies the proved program
typing system and checked control-flow graphs. The
[source integration status](DESIGN.md#source-integration-current-slice-and-next-milestone)
distinguishes the supported source fragment from model-only features.

## Operational language

`Language.lean` defines an untyped call-by-value language with a mutable heap.
This is the whole term syntax:

$$t ::= x_i\mid t\,t\mid\mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}
\mid\mathsf{obj}(\ell,c)\mid\mathsf{make}(c,t)\mid\mathsf{let}(t,t)
\mid\mathsf{read}(t)\mid\mathsf{write}(t,t)
\mid\mathsf{test}_k(t)\mid\mathsf{if}\;t\;t\;t.$$

Here $x_i$ is a variable, given as a de Bruijn position, $\ell$ a heap location,
and $k$ a shape test
drawn from $\{\mathsf{isNul},\mathsf{isUndef},\mathsf{isNullish},\mathsf{isBool},\mathsf{isRef},\mathsf{isFun}\}$.
The nullish test accepts null or undefined; the others recognize individual value shapes. Values are
the subset

$$v ::= \mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{obj}(\ell,c),$$

where $c ::= \mathsf{absent}\mid\mathsf{closure}(m,t)$ is a separate invocation
descriptor with a declared parameter count `m`. `make c a` evaluates its initializer `a`, then appends that value
to the heap and returns `obj h.length c`, where `h.length` is the length
before appending.
`alloc a` abbreviates `make absent a`; `attach b a` abbreviates
`make (closure 1 b) a`; `funE b` abbreviates `make (closure 1 b) null`.
All three use the same constructor and the same allocation step, `Step.makeV`.
The closure body is not evaluated during creation. There is no bare lambda value.

`make_rule` proves heap and world extension once, with a result obligation for
the fresh object's descriptor. `alloc_rule` and `attach_rule` specialize that
proof to plain reference and callable contracts.

[ObjectCoherence.lean](lean/Verification/ExperimentState/ObjectCoherence.lean)
proves the separate identity invariant. An append-only ghost registry records
each allocation's descriptor. Every object occurrence in terms, closure bodies,
and heap cells agrees with that registry; an already allocated closure has no
free variables other than its argument. Substitution therefore preserves its
descriptor. `step_preserves` follows the existing `Step` relation and proves that
reads, writes, calls, and allocation preserve coherence, including heap cycles.
The registry is proof data, not an additional runtime heap.

[GraphCoherence.lean](lean/Verification/ExperimentState/GraphCoherence.lean)
lifts this to the existing graph execution, including saved environments and
slot maps. The graph consumer checks `sourceTerm` on every node, forbidding
embedded runtime identities even inside unselected branches and empty-overload
bodies. `accepted_closed_coherent` covers every finite prefix of an accepted
closed invocation. External invocations preserve a supplied coherent heap and
environment, with all pre-existing descriptors unchanged. This theorem is
separate from semantic type safety: arbitrary raw terms and the unrestricted
semantic families do not themselves impose a global registry.

`Val` abbreviates `Tm`, so worlds, heaps and the step relation all speak
about the same objects. `letE a b` is an explicit binding: it evaluates `a`,
then substitutes the resulting value into `b` in one step without changing the
heap. Only `b` is under the new binder. `HasTy.letE`, source lowering, and the
certificate producer and consumer all use that constructor. `Step_det` proves
that a term and heap have at most one successor.

Two different things are named here, and both run through the whole development.
A **binding** lives in the environment $\rho$; a **location** $\ell$ is an address
in the heap $h$. This is the usual store/heap pair of an ML-style operational
semantics. A binding may *hold* an object: $\rho(x)=\mathsf{obj}(\ell,c)$. Below,
$\ell$ abbreviates the plain-object value $\mathsf{obj}(\ell,\mathsf{absent})$.
A function object carries closure code at the same kind of heap identity;
[callable contracts](PROGRAM-TYPING.md#callables) additionally constrain that code.

Because the calculus is nameless, a binding is really a de Bruijn position, and
the implementation calls it a **slot**: environments are lists, and pushing a
value renumbers everything already there. Rules in these documents write names
for bindings anyway, which reads better and matches the source they describe.
The two views agree, and `shift_holds` is the theorem that says so: renumbering
on a push preserves every fact. Positions surface again only where something
genuinely carries them — a certificate's binding transfer, and the wire format.

Assertions are attached to bindings, because bindings are what a checker can
name; locations arise only during execution and never appear in a program. So
$x\mapsto R$ is not a claim about $x$'s value but about the
location that value *is*: there exist $\ell$ and $v$ with $\rho(x)=\ell$,
$h(\ell)=v$ and $v\in R$. That one indirection is where aliasing enters, and it
is why the checked rules have
[no frame rule](PROGRAM-TYPING.md#the-reference-operations): two names can hold
the same location, and no assertion can say they do not.

Two of these forms are deliberately outside the typing judgment. A location
arises only at run time and takes its contract from the world, never from a
typing rule. A shape test is typed only in the guard of a conditional, by
`ifTag`; it has no standalone rule. The source fragment uses null and undefined tests for strict comparisons, and
the nullish test for `??`. Every test is total on values.

Substitution operates on closed substituted values. `Bindings.lean` supplies
scope and simultaneous closing substitution, including its beta law. The program
typing theorem uses semantic environments of closed values; its closed-program
interface explicitly checks scope.

## Argument-list preparation

[CallArguments.lean](lean/Verification/ExperimentState/CallArguments.lean)
defines preparation separately from invocation. A frame contains a callee term
and an ordered list of argument terms. `Prepare` steps the callee until it is a
value, then `ArgStep` steps the leftmost non-value argument using the existing
term machine and heap. Previously evaluated operands remain in their original
positions. No argument binding, padding, truncation or body invocation occurs
in this relation.

`prepare_deterministic`, `arity_preserved`, `callee_preserved` and `prefix_iff`
prove unique next states, unchanged list length, stability of the saved callee,
and preservation of every completed argument prefix. `unary_step` embeds each
single-argument preparation step into the current application's congruence
rules. A ready frame has a value callee and value arguments; readiness does not
establish callability, arity compatibility or typing. A stuck operand blocks later
effects rather than being skipped.

After preparation, `parameters n args` supplies exactly `n` parameter values:
actual position `i` when present, otherwise `undefined`. Extra actuals do not
occupy parameter slots; their effects have already happened during preparation.
`parameter_at` and `parameters_length` establish this for every list and arity.
The type contract must separately justify any missing argument.

`bindArgs` substitutes parameter slots from highest to lowest, preserving earlier
arguments and nested body binders. Parameters use declaration order: the first
parameter is slot zero, and captures begin after the full parameter list.
`instantiate_args` proves that closing captures then binding parameters agrees
with one simultaneous substitution. `bound_body_closed` establishes that a body
scoped to its parameters is closed after binding closed actuals. Binding performs
no heap operation.

[Safety.lean](lean/Verification/ExperimentState/Safety.lean) defines `ArgsT` for
an ordered list of actual-argument types and `InvocationSpec` for code with a
declared parameter count. Each overload fixes its actual argument count, which
can differ from the declared count. The safety obligation uses the normalized
parameter list, so omitted parameters must be safe as `undefined`; extra actuals
still satisfy their own domains. These are semantic code obligations, not a
source policy allowing omitted required arguments. `ArgsT_length` establishes
the actual count, and `ArgsT_values` establishes readiness when the domains
contain only values. Invocation contracts survive budget reduction and world
extension.

`Invoke` dispatches a ready frame to the immutable code on its saved callee,
using `bindParameters`. It performs no heap operation and cannot overlap a
preparation step. All actuals must be values, including those discarded during
normalization. `invoke_iff` characterizes dispatch exactly; readiness alone does
not make a primitive or a plain object callable. `invoke_closed` preserves closed
scope, and `InvocationSpec.invoke` supplies the promised body safety for an
admitted actual list. The descriptor carries its parameter count explicitly;
`Scoped`, substitution, capture instantiation and the certificate scope check
all traverse its body under that many binders. Object coherence preserves both
arity and body at an identity. `Step.beta` and dispatch use the same normalized
binding operation, including when a unary application supplies fewer or more
actuals than the descriptor declares.

`unary_step_iff` proves both directions of the connection to the maintained
machine: every application step is preparation or dispatch, and either operation
reconstructs an application step. This includes beta as well as operand effects;
it introduces no second term evaluator.

`callsT` lifts list-signature code contracts to callable values. An overload can
admit any fixed actual count, including zero, independently of the descriptor's
parameter count. `callsT_invoke` obtains both a dispatch and its safe body from
membership and typed value arguments. `ArgsT_transfer` preserves the saved
arguments' types as budget decreases and the world extends.

`callsT_adm` proves admissibility without assuming admissible domains, and
`callsT_congr` proves that every argument position and result is guarded by the
call step. `ArgsAgree` requires corresponding domain positions and equal list
lengths. `arrowsT_callsT` establishes exact equivalence to the existing unary
overload type for singleton domains; the unary admissibility and congruence
proofs now use these general results.

The existing `CodeSpec` is now the one-parameter, singleton-domain specialization
of `InvocationSpec`. `CodeSpec_iff` proves equivalence to its previous unary
obligation, and existing callable creation proofs use that equivalence. The
current beta rule and semantic call helper both use `bindParameters` with the
saved descriptor's arity. `arrowsT_invocation_iff` connects unary actual-argument
contracts to code of any declared arity. Source creation still uses arity one
(including the current implicit-undefined thunk encoding). List-valued application
terms, list-domain type-graph nodes, typing certificates and source integration
remain to be added before multi-argument source calls are enabled.

## Types, worlds and heaps

A semantic family has type

```lean
Fam := (n : Nat) → WorldT n → Val → Prop
```

A world records the invariant contract of each allocated location. At level
`n`, a contract can inspect lower levels and their worlds. `WorldAdm` requires
contracts to survive extension by further allocations. `HeapOk` says the heap
has the world's allocated locations and their contents satisfy those contracts
at lower levels. `Heaps.lean` proves that appropriate writes and allocation
preserve heap satisfaction.

`Adm` requires a family to be downward closed when both budget and world are
truncated, and monotone under world extension. Unions and intersections are
pointwise disjunction and conjunction; both preserve admissibility.

`refT A` means that the value is a location whose stored contract agrees with
`A` at every lower level and world. It is invariant in its operand, not a
covariant container. `ReferenceConjunctions.lean` retains multiple requirements
on this same contract and proves their read/write rules.

Worlds have different types at different budgets. Consequently, “the type is
just the intersection of its approximations” is not a complete standalone
account of membership. The proved subtype soundness theorem quantifies over
every budget, matching world, and value; no quotient of worlds or all-budget
observational equivalence is assumed.

## Computations and recursive types

`Safe A 0 W h e` imposes no obligation. At a positive budget, either `e` is a
value belonging to `A`, or it can step with one budget spent, preserving heap
satisfaction in an admissible extension of the truncated world. This is partial
correctness/safety, not termination.

`SafeGraph` is the same predicate one level up, for the machine that runs a
control-flow graph rather than a single term. Its states are

$$s ::= \mathsf{at}(p,\rho)\mid\mathsf{eval}(t,\rho,k)\mid\mathsf{done}(v),$$

where $p$ is a program point (a node label, not a location), $\rho$ an
environment of closed values, and $k$ a
[continuation](PROGRAM-TYPING.md#checked-control-flow-graphs). Entering a node
instantiates its term against $\rho$; the term then steps as usual; a value meets
the node's continuation, which either finishes the run or moves to the next label
with a transformed environment. `SafeGraph P T n W h s` says that at a positive
budget the state is either $\mathsf{done}(v)$ with $v\in T$, or it can take one
graph transition, spending a budget and preserving heap satisfaction in an
admissible future, and remain safe there. `Safe` is the special case with no
graph. Starting a graph means starting at $\mathsf{at}(p,\rho)$ for the entry
point and the input environment.

`CallableConjunctions.objectsT` combines invariant bag requirements and
overloads on one value. Its guardedness and admissibility proofs let the
`callable first rest arrows` clause participate in recursive positive graphs.
Normalization concatenates bag requirements and signatures; it retains
incompatible invariant operands at low budgets just as reference conjunctions
do. Subtyping can forget properties but cannot widen an invariant bag or turn
a function into a plain reference. Checked creation proves the stored value
and all code obligations separately. Graph calls, reads, and writes then use
the corresponding part of that same object's contract.

An arrow contains **function objects with closed invocation code** whose
substituted bodies are safe at every
smaller budget, every admissible future world, every satisfying heap, and every
argument in the domain there. The guarantee concerns the body after beta; the
actual application spends that step before invoking it. Consequently `app_elim`
proves same-budget application compatibility from function and argument
membership. Quantification over future worlds remains essential for allocation.

In notation, for every $j<n$ and admissible future $U$ and satisfying heap $h$,

$$\mathsf{obj}(\ell,\mathsf{closure}(m,b))\in\llbracket A\to B\rrbracket(n,W)
\Longrightarrow
\big(a\in\llbracket A\rrbracket(j,U)\Rightarrow
\operatorname{Safe}(B,j,U,h,\operatorname{bindParameters}(m,[a],b))\big).$$

A guarded operator consults recursive operands only below the current budget.
Its approximation tower stabilizes at every finite observation level, and the
diagonal is a fixed point. `Tower.lean` supplies that construction for graph
interpretations. It does not require monotonicity of the recursive operand, so
negative occurrences in function domains are permitted when guarded. This is
not a greatest-fixed-point construction on unindexed sets of values.

The type graph is a finite system of guarded positive formulas. Normalization
preserves the entire interpretation operator, hence also its recursive fixed
point. No cycle is unfolded during normalization. See the grammar and equations
in [POSITIVE-TYPES.md](POSITIVE-TYPES.md).

## Current-content assertions and postconditions

The [assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) defines the
notation and its separation from ordinary types. This section gives its meaning.

A world records a location's persistent storage contract, while a heap records
its current contents. Both a true heap and a false heap can satisfy the same
Boolean world. A point claim `{ value: B = R }` combines the invariant reference
with a current-content predicate:

$$
\operatorname{Obs}(h,\ell,R)
\equiv \exists v.\ h(\ell)=v \land R(v),
\qquad
\operatorname{ObservedRef}(B,R,n,W,h,\ell)
\equiv \operatorname{Ref}(B)(n,W,\ell)\land\operatorname{Obs}(h,\ell,R).
$$

`ObservedRef` in [HeapObservations.lean](lean/Verification/ExperimentState/HeapObservations.lean)
is used with `HeapOk(n,W,h)`. For primitive predicates this requires the contents
to satisfy both the storage invariant and the observation. Consequently
`{ value: true = false }` is inconsistent in a satisfying heap at every positive
budget. The raw predicate without `HeapOk` does not enforce that connection;
the invariant check is vacuous at budget zero. Giving the conjunction meaning
does not require a syntactic subtype relation between `R` and `B`.

The right side of `=` is a predicate, not an initializer or a future-read promise.
Only null/undefined/Boolean predicates are exported today; numeric notation illustrates a
future extension. These assertions are duplicable facts, not exclusive write
permissions. This is a chosen plain-cell interpretation, not a theorem equating
SKJS's internal types with heap assertions.

### What is asserted, and what a heap change can touch

The finite assertion layer records three forms, and they divide on one question:
does the form mention the heap?

$$
\begin{aligned}
x=R&\equiv\rho(x)\in R,
  &&\text{a variable equals one of these constants}\\
x=y&\equiv\rho(x)=\rho(y),
  &&\text{two variables hold the same value}\\
x\mapsto R&\equiv
  \exists\ell\,v.\;\rho(x)=\ell\land h(\ell)=v\land v\in R,
  &&\text{the cell }x\text{ names holds one of them}\\
x\mapsto y&\equiv
  \exists\ell.\;\rho(x)=\ell\land h(\ell)=\rho(y),
  &&\text{that cell holds the value of }y
\end{aligned}
$$

Two relations, each taking a finite set of constants or a variable on the right.
The $=$ atoms mention only $\rho$; the $\mapsto$ atoms mention $h$ as well, and
that is the only difference that matters. $x=R$ abbreviates the disjunction
$x=c_1\lor\dots\lor c_k$, an ordinary equality when $R$ is a singleton; its
meaning is membership, but the assertion is an equality. Write $\Pi$ for a list of them. The last two mention $h$ as
well. Write $\Sigma$ for a list of those. Both are read as the conjunction of
their atoms and extended with a comma, exactly as $\Gamma$ is; neither carries
ownership or disjointness, and the atoms are duplicable, so there is no
separating conjunction to write.

That division is the whole state discipline. No write and no call can disturb
$\Pi$, because nothing in $\Pi$ speaks about the heap: two copied references remain
the same location after any write, and a constant a variable is equal to does not
change when a cell does. Everything in $\Sigma$ is a claim about the heap as it is
now, so a write to an unknown location or a call to an unknown function can
falsify any of it. Allocation is the exception that proves it: a fresh cell
cannot be one an existing fact names, so allocation preserves both. The
checked `allocated` rule applies to both plain and callable objects through
`make`, with a known initializer slot. Typed reads also use one proof for both
kinds of bag and retain their actual descriptor in the read links. Closure
bodies may mutate when called; allocating their code does not execute them.

`ValueHolds` and the alias branch of `HeapLinks.Holds` interpret $\Pi$;
`HeapFacts.Holds` and the read branch interpret $\Sigma$. The implementation stores
them as three lists — cell facts, value facts, and links carrying an `alias`
flag — so the links list straddles the division: the flag is what says which side
a link is on. [Program typing](PROGRAM-TYPING.md#the-reference-operations) states
the rules over $\Pi$ and $\Sigma$; the
[assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) owns the notation
for what a source claim may say.

`SafePost T Q n W h e` strengthens `Safe T n W h e`: at a positive-budget final
value it additionally requires `Q h e`; its step case uses exactly the same
operational step, truncated-world extension, admissibility and heap satisfaction.
At budget zero it is true. The `postcondition` theorem proves `Q` for an actual
terminating execution observed with one remaining level; divergence is permitted.
`erase` yields ordinary safety, and `forget` embeds ordinary safety with `Q = True`.

[HeapObservationTests.lean](lean/Verification/ExperimentState/HeapObservationTests.lean)
proves the important counterexamples. `observation_not_a_value_type` excludes
representing current contents by a heap-independent value family.
`observation_does_not_narrow_invariant` gives a Boolean cell currently true that
is not `Ref true`. `callback_counterexample` supplies an inhabited heap and an
ordinarily typed captured writer that destroys the true observation. Thus an
ordinary arrow cannot promise preservation of captured current contents.

[Program typing](PROGRAM-TYPING.md#current-content-rules-semantic-layer) specifies
the operation and composition rules using this predicate;
[Design](DESIGN.md#current-content-assertions) owns the graph-integration plan.

## What the checked development establishes

- `Rules.lean` gives the operational rules for functions, application, heap
  operations, shape testing and branching, including an application-context
  composition rule.
- `Examples.lean` checks negative recursive function types, closures surviving
  alias writes, and a composed program that allocates, mutates and reads back a
  changed boolean. It also rejects a stuck function.
- `ProgramTyping.lean` proves safety by induction on syntactic typing derivations.
  `ProgramTypingTests.lean` combines overload dispatch, captured state, an alias
  write and checked overload subsumption in one program.
- `ProgramCertificates.lean` checks finite program evidence and proves acceptance
  equivalent to closed-program derivability. The same example has executable
  evidence and obtains safety from its successful check.
- `PointClaims.lean` checks supplied environment claims against individual incoming
  edges, proves environment transfer, and composes checked computations through
  such claims.
- `ControlFlow.lean` enumerates every actual node and outgoing edge, then proves
  global safety, no stuck execution and typed returns, including cyclic graphs.
  It reuses expression steps and adds explicit dispatch and transfer steps.
- `PositiveNormalization.lean` and `PositiveGraphs.lean` prove finite and
  recursive normalization preservation.
- `PositiveRules.lean` defines declarative subtype rules and proves their
  semantic soundness.
- `PositiveCertificates.lean` proves checker soundness and certificate
  completeness for those rules, and transports accepted subtyping through
  normalization to computation subsumption.

The certificate theorem says **derivable iff some finite certificate is
accepted**. It does not assert completeness for every inclusion true in the
semantic model, automatic proof search, or that exported point invariants
already contain all necessary subtype evidence.

## Two retained design constraints

`ModelBoundaries.lean` preserves counterexamples that constrain future rules.

First, unrestricted arrow-result distribution fails:

```text
(A → B) & (A → C) ≤ A → (B & C)
```

An allocating function can satisfy the two arrows using different invariant
choices for a new cell. Requiring a single result-world interpretation is
stronger. The maintained combination rule uses a proved conservative shape
condition instead.

Second, eventual incompatibility of nested reference contracts cannot justify
collapsing their arrow results to bottom at every finite index. A concrete
cyclic heap and constant function witness the failure. This is a limitation of
that indexed semantic inclusion, not evidence of a program accepted unsafely.

These counterexamples are regression tests for the model's laws. They do not
require keeping separator searches or a second subtyping implementation.

## Remaining scope

The bounded source adapter and graph consumer are connected; their guarantees
are described in [Program typing](PROGRAM-TYPING.md) and the
[request protocol](REQUEST-PROTOCOL.md). This does not prove source-to-graph
correspondence. Source current-content claims are connected to graph checkpoints;
graph-backed closure bodies remain integration work. Type parameters, bounded polymorphism, and general
difference/negation require further syntax and sound rules; definability of
quantification over semantic families alone is not a generics result.
[Design](DESIGN.md#later-feature-gates) owns the feature roadmap and priorities.
