# Semantics

The stateful development in [Model](lean/Verification/Model)
provides the semantic foundation for the positive-type rules specified in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md). This is the semantics used by the current verifier. [PROGRAM-TYPING.md](PROGRAM-TYPING.md) specifies the proved program
typing system and checked control-flow graphs. The
[source integration status](DESIGN.md#source-integration)
distinguishes the supported source fragment from model-only features.

## Operational language

`Calculus.lean` defines an untyped call-by-value language with a mutable heap.
The following is the original one-field kernel notation, not an exhaustive
constructor inventory (see `Tm` in `Calculus.lean` for the maintained syntax):

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

where $c ::= \mathsf{absent}\mid\mathsf{closure}(m,t)\mid\mathsf{variadic}(m,t)\mid\mathsf{bound}(f,r,\vec p)$ is a separate invocation
descriptor, the first two with a declared parameter count `m`. A closure body is
under `m + 1` binders: the receiver of the call in slot 0, then its parameters.
A variadic body has its rest array in slot 0, the receiver in slot 1, then `m`
parameters. `bound` is the forwarding descriptor `.bind` creates: the target, the
receiver and the argument prefix it saved, values that no field holds and no
write can reach. `make c a` evaluates its initializer `a`, then appends that value
to the heap and returns `obj h.length c`, where `h.length` is the length
before appending.
`alloc a` abbreviates `make absent a`; `attach b a` abbreviates
`make (closure 1 b) a`; `funE b` abbreviates `make (closure 1 b) null`.
All three use the same constructor and the same allocation step, `Step.makeV`.
The closure body is not evaluated during creation. There is no bare lambda value.

`make_rule` proves heap and world extension once, with a result obligation for
the fresh object's descriptor. `alloc_rule` and `attach_rule` specialize that
proof to plain reference and callable contracts.

[ObjectCoherence.lean](lean/Verification/Model/Semantics/ObjectCoherence.lean)
proves the separate identity invariant. An append-only ghost registry records
each allocation's descriptor. Every object occurrence in terms, closure bodies,
and heap cells agrees with that registry; an already allocated closure has no
free variables other than its argument. Substitution therefore preserves its
descriptor. `step_preserves` follows the existing `Step` relation and proves that
reads, writes, calls, and allocation preserve coherence, including heap cycles.
The registry is proof data, not an additional runtime heap.

[GraphCoherence.lean](lean/Verification/Model/Semantics/GraphCoherence.lean)
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

A read of a named property on an object with no such own field steps to
`undefined` (`Step.readMissing`); a present field still reads its heap location.
The semantic readonly string-dictionary view `dictViewT A` requires every
*present* field's stored contract to imply `A` at lower budgets. This is guarded
and admissible even when `A` is recursive, and it grants no write permission.
`empty_bool_dict_missing` witnesses the distinction: an empty object satisfies
the Boolean dictionary view, while a read of any key yields `undefined`, which
is not Boolean. An arbitrary indexed read therefore needs a result including
`undefined`. The positive graph has a `dict` clause whose operands are guarded
recursive labels, and the checked covering rule can compare dictionary views.
The source parser and OCaml producer lower inline readonly string-index
annotations into that clause. A named key read uses the proved `readDict` rule;
a computed string key uses `indexAt`, which evaluates the receiver before the
key and then reads the selected field (or `undefined` if it is absent). The
proved `indexDict` rule checks the key at `string`. Both reads carry
`undefined` in their result. This path reaches the same certified
source acceptance theorem as other expressions. The `allocDict` rule checks
every initializer at the index element contract and uses the exact fresh
field map to establish a dictionary view; it cannot retype an existing open
record. Imported recursive declarations remain outside the source fragment.

Term and descriptor equality use explicit structural comparisons, each returning
a kernel-checked `Decidable` result and recurring only on strict subterms. This
keeps certificate equality executable for list-valued
applications: Lean's `DecidableEq` deriving handler does not support nested
mutually recursive types. The comparisons inspect every constructor field,
including descriptor arity.

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

## One meaning for callable contracts

The core equation is a behavioral promise, shared by fixed signatures, rest
signatures, overloads and callable objects. Let $R_c$ be the receiver family,
$\mathcal A$ describe the admitted lists of actual values and $R$ the result
family. Then

$$
f\in\mathcal F(R_c,\mathcal A,R)(n,W)\iff
\operatorname{Invocable}(f)\ \land\
\forall j<n,\ U\succeq W{\downarrow}j,\ h,r,\vec v.\;
\begin{aligned}
&\operatorname{WorldAdm}(U)\land\operatorname{HeapOk}(j,U,h)
 \land r\in R_c(j,U)\land\operatorname{Values}(\vec v)\land\mathcal A(j,U,\vec v)\\
&\quad\Longrightarrow\exists t.\;
 \operatorname{Invoke}(f,r,\vec v,t)\land\operatorname{Safe}(R,j,U,h,t).
\end{aligned}
$$

This is `Invocable` together with `Safety.Promise`. The receiver is not an
actual: it changes no arity, optional position or rest, and $\mathcal A$
never sees it. A plain call passes `undefined`; a method call, the object the
method was read from; `.call`, its first argument. A signature indifferent to
its receiver states top. Weakening is contravariant in $R_c$ as in each
domain: a function that ignores its receiver meets any receiver requirement,
and one that reads its receiver cannot be widened to accept arbitrary ones. `Invoke` dispatches the
saved code and yields a term; `Safe` describes its execution, including any
allocation, mutation or further call. The call spends a step before using
this lower-budget guarantee. Safety permits nontermination. Neither the
contract nor the equation requires a particular parameter-binding descriptor.

This supplies the call component of the existing
[callable-object equation](PROGRAM-TYPING.md#types-describe-behaviour-not-internal-storage):

$$
\mathsf{Callable}(L;P)=\mathsf{Fun}\cap\mathsf{Props}(P)
  \cap\bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma).
$$

Here `Invocable` supplies function shape, `propsT` supplies the field
requirements, and `Promise` supplies each call specification. The same value
must satisfy every conjunct; neither overloads nor generic instantiation
allocate a replacement function or choose a new storage contract.

All the callable uses build on this equation:

- A fixed signature uses `ArgsShort`: written actuals meet their corresponding
  domains, and each omitted trailing domain admits `undefined`. A rest
  signature uses `ArgsRest`: it additionally admits arbitrarily many extra
  values at its element contract. `callsT` and `restsT` conjoin `Promise` over
  their respective signature lists.
- Overloads conjoin promises on **one value**. The `arrs L S` clause combines
  fixed and variadic promises; either list may be empty. Thus compatible
  fixed and variadic contracts overlap. Their syntax does not divide runtime
  functions into disjoint type shapes.
- A callable object's field contract is intersected with these same promises:
  `callable P Ps L S` means `propsT P Ps ∩ callsT L ∩ restsT S`.
  Reads and writes use the fixed world contracts of the fields; invocation
  uses the call promises on that same object. Returning, passing or capturing
  a callback simply uses this family as a result, domain or environment type.
- Quantification requires the same value, in the same world, to satisfy the
  promises at every admissible binder assignment. `TypeSchemes.schemeT`
  universally quantifies the conjunction of instantiated `callsT` and `restsT`;
  its shape condition is `Invocable`, even when no assignment satisfies the
  bounds. The executable universal certificate covers both fixed and rest
  descriptors. `T[]` denotes invariant array storage under the same assignment,
  and each invocation allocates its rest array with that contract.
- Contract weakening follows `Promise.weaken`: admit fewer argument lists
  and weaken the result. Fixed-to-variadic coverage is not generally valid
  from a fixed contract alone, since it promises nothing about longer lists.
  A concrete ordinary closure can nevertheless have stronger behavior.

The [typing rules](PROGRAM-TYPING.md#expressions) build creation and
application rules on this meaning. `InvocationSpec` and `RestCalls.RestSpec`
are code-specific introduction premises. `callsT_of_invocationSpec` and
`restsT_of_restSpec` turn them into the behavioral contracts above. The older
unary `arrowT`, `arrowsT` and fixed-code `codeCallsT` remain specialized
semantic lemmas for ordinary closure code; they are not the graph's definition
of all function values. `callsT_of_arrowsT` embeds that specialized guarantee.

## Argument-list preparation

Applications use `invoke f r args`: the callee, the receiver, the ordered
actuals. `call f args` abbreviates `invoke f undefined args`, and `app f a` the
singleton call; neither is a second form of call. Substitution, scope checking,
capture instantiation and object-name traversal visit the receiver, the entire
list and every code descriptor, including a `bound` descriptor's saved values.
`CallArguments.Frame` keeps the callee, the receiver and ordered arguments
separate from invocation.

`Prepare` evaluates the callee, then the receiver, then processes arguments from
left to right.
`Step.callArg` requires earlier arguments to be values. A `spread` is not a
value: `Step.callSpread` consumes its ready store before any later argument
can step, replacing holes with `undefined`. Splicing can change list length;
`ArgStep.length_preserved` applies to an individual operand reduction, not to
all preparation. `prepare_deterministic` and `call_step_iff` connect preparation
and invocation to the deterministic term machine. A ready frame has value
operands; readiness alone does not establish callability or typing.

Ordinary code uses `parameters n args` to pad missing positions with
`undefined` and discard extra positions after their effects have occurred.
`bindParameters` substitutes the receiver in slot 0 and these values after it,
without allocating. Variadic code uses
`bindRest`: fixed positions are padded in the same way, while `args.drop n`
becomes a fresh rest array. Padding never enters the rest array. Dispatch
itself leaves the heap unchanged; the yielded term allocates the array using
ordinary store and object allocation steps. These operational distinctions
are independent of the contracts callers use.

A `bound` descriptor dispatches without binding anything: `Step.callBound`
turns `invoke (bound f r₀ p⃗) r a⃗` into `invoke f r₀ (p⃗ ++ a⃗)`, dropping the
receiver `r` it was given. `bound_ignores_receiver` states that the yielded term
is the same whatever `r` is, and `rebind_keeps_receiver` that binding a bound
function forwards to it, which forwards with the first saved receiver.
`callsT_bound` proves the residual contract: a target meeting
$(R_t, \vec P \mathbin{+\!\!+} \vec D, R)$ with a saved receiver in $R_t$ and a
saved prefix in $\vec P$ gives an object meeting $(R_c, \vec D, R)$ for any
$R_c$, and `restsT_bound` the same for a variadic target, whose residual keeps
its element contract. There is no forwarding wrapper closure: construction and
`new.target` are not modelled, and a bound function has no own fields.

`.apply` is a source lowering onto these steps, not a new preparation: it saves
the target, the receiver and the list, then reads the list's length and each
index in order with the ordinary store operations, then invokes the target with
those elements. It never iterates the list, so it shares the prepared actual
list with ordinary calls but not the spread's operation.

`callsT_invoke` obtains safe dispatch from a behavioral promise.
`ProgramTyping.call_safe` first evaluates the callee and composes effectful
arguments using `bind_list` and `FutureSafe`. `ArgsT_transfer` preserves saved
value types as the budget decreases and the world extends. Variadic calls
add `RestCalls.spread_parts_safe` and `call_elim_rest`; source lowering copies
a spread's elements at its evaluation point when later operands run code.
The copy preserves element values, including object references, rather than
merely saving the source array's identity.

`callsT_adm`, `restsT_adm` and the corresponding congruence lemmas establish
world monotonicity and guardedness of both domains and results. The
source/calculus correspondence remains the documented trusted-adapter
boundary; these theorems establish safety of the extracted program.

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

`CallableConjunctions.objectsT` combines invariant field requirements and
fixed call promises on one value. `PositiveNormalization.sem` intersects it
with `restsT` for the graph's `callable first rest arrows variadic` clause.
The plain `arrs arrows variadic` clause carries the same call promises without
field requirements. Normalization concatenates both kinds of signature and
retains invariant field operands. Checked creation establishes field storage
and code obligations separately; calls, reads and writes use the corresponding
part of the same object's contract. The common function equation above governs
all these call obligations.

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

`ObservedRef` in [HeapObservations.lean](lean/Verification/Model/Semantics/HeapObservations.lean)
is used with `HeapOk(n,W,h)`. For primitive predicates this requires the contents
to satisfy both the storage invariant and the observation. Consequently
`{ value: true = false }` is inconsistent in a satisfying heap at every positive
budget. The raw predicate without `HeapOk` does not enforce that connection;
the invariant check is vacuous at budget zero. Giving the conjunction meaning
does not require a syntactic subtype relation between `R` and `B`.

The right side of `=` is a predicate, not an initializer or a future-read promise.
Null/undefined/Boolean and numeric predicates are supported, including the
whole number family and exact numeric singletons. These assertions are duplicable facts, not exclusive write
permissions. This is a chosen plain-cell interpretation, not a theorem equating
SKJS's internal types with heap assertions.

### What is asserted, and what a heap change can touch

The finite assertion layer records three forms, and they divide on one question:
does the form mention the heap?

$$
\begin{aligned}
x=R&\equiv\rho(x)\in R,
  &&\text{a variable satisfies a primitive predicate}\\
x=y&\equiv\rho(x)=\rho(y),
  &&\text{two variables hold the same value}\\
x\mapsto R&\equiv
  \exists\ell\,v.\;\rho(x)=\ell\land h(\ell)=v\land v\in R,
  &&\text{the cell }x\text{ names satisfies }R\\
x\mapsto y&\equiv
  \exists\ell.\;\rho(x)=\ell\land h(\ell)=\rho(y),
  &&\text{that cell holds the value of }y
\end{aligned}
$$

Two relations, each taking a finite primitive-predicate disjunction or a variable on the right.
The [predicate vocabulary](POSITIVE-TYPES.md#state-assertion-grammar) includes
numeric singletons and the whole number family.
The $=$ atoms mention only $\rho$; the $\mapsto$ atoms mention $h$ as well, and
that is the only difference that matters. $x=R$ abbreviates membership in the
disjunction of predicates in $R$. For constant predicates this is a disjunction
of equalities; the numeric-family predicate also admits any numeric value.
Write $\Pi$ for a list of them. The last two mention $h$ as
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

[HeapObservationTests.lean](lean/Verification/Model/Tests/HeapObservationTests.lean)
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
Rigid parameters, substitution on the identity and `Ref T` aliases (source
`type Id<T> = T` and `type Box<T> = { value: T }`), and the
identity function at every `T` are in
[TypeParams.lean](lean/Verification/Model/Types/TypeParams.lean).
Receivers follow the strict rule only: sloppy code's global-object substitution
and primitive boxing, `super` and home objects, construction and `new.target`,
and a bound function's reflective properties (`name`, `length`) are later
obligations, not approximated by the strict rule.
The intended path is the
[operation-level contracts, then a small first-order fragment](DESIGN.md#semantic-contracts-for-skjs-operations).
[Design](DESIGN.md#later-feature-gates) owns the feature roadmap and priorities.
