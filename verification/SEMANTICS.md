# Semantics

The stateful development in [ExperimentState](lean/Verification/ExperimentState)
provides the semantic foundation for the positive-type rules specified in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md). This is the semantics used by the current verifier. [PROGRAM-TYPING.md](PROGRAM-TYPING.md) specifies the proved program
typing system and checked control-flow graphs. Extraction for the extended
language remains an integration obligation.

## Operational language

`Language.lean` defines an untyped call-by-value language with a mutable heap.
This is the whole term syntax:

$$t ::= x_i\mid\lambda t\mid t\,t\mid\mathsf{null}\mid\mathsf{true}\mid\mathsf{false}
\mid\ell\mid\mathsf{alloc}(t)\mid\mathsf{read}(t)\mid\mathsf{write}(t,t)
\mid\mathsf{test}_k(t)\mid\mathsf{if}\;t\;t\;t.$$

Here $x_i$ is a variable, given as a de Bruijn position, $\ell$ a heap location,
and $k$ a shape test
drawn from $\{\mathsf{isNul},\mathsf{isBool},\mathsf{isRef},\mathsf{isFun}\}$,
one per type constructor, which is what a source `typeof` amounts to. Values are
the subset

$$v ::= \lambda t\mid\mathsf{null}\mid\mathsf{true}\mid\mathsf{false}\mid\ell,$$

and `Val` abbreviates `Tm`, so worlds, heaps and the step relation all speak
about the same objects. There is no `let` constructor: `HasTy.letE` types the
pattern $(\lambda t)\,t$. `Step_det` proves that a term and heap have at most
one successor.

Two different things are named here, and both run through the whole development.
A **binding** lives in the environment $\rho$; a **location** $\ell$ is an address
in the heap $h$. This is the usual store/heap pair of an ML-style operational
semantics. A binding may *hold* a location: $\rho(x)=\ell$.

Because the calculus is nameless, a binding is really a de Bruijn position, and
the implementation calls it a **slot**: environments are lists, and pushing a
value renumbers everything already there. Rules in these documents write names
for bindings anyway, which reads better and matches the source they describe.
The two views agree, and `shift_holds` is the theorem that says so: renumbering
on a push preserves every fact. Positions surface again only where something
genuinely carries them — a certificate's binding transfer, and the wire format.

Assertions are attached to bindings, because bindings are what a checker can
name; locations arise only during execution and never appear in a program. So
$\operatorname{cell}(x,R)$ is not a claim about $x$'s value but about the
location that value *is*: there exist $\ell$ and $v$ with $\rho(x)=\ell$,
$h(\ell)=v$ and $v\in R$. That one indirection is where aliasing enters, and it
is why the checked rules have
[no frame rule](PROGRAM-TYPING.md#the-reference-operations): two names can hold
the same location, and no assertion can say they do not.

Two of these forms are deliberately outside the typing judgment. A location
arises only at run time and takes its contract from the world, never from a
typing rule. A shape test is typed only in the guard of a conditional, by
`ifTag`; it has no standalone rule. Of the four tags, only $\mathsf{isNul}$ is
reachable from the current source fragment, through null comparisons; the others
keep the test total on values, which the shape lemmas rely on.

Substitution operates on closed substituted values. `Bindings.lean` supplies
scope and simultaneous closing substitution, including its beta law. The program
typing theorem uses semantic environments of closed values; its closed-program
interface explicitly checks scope.

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

An arrow contains **closed lambdas** whose substituted bodies are safe at every
smaller budget, every admissible future world, every satisfying heap, and every
argument in the domain there. The guarantee concerns the body after beta; the
actual application spends that step before invoking it. Consequently `app_elim`
proves same-budget application compatibility from function and argument
membership. Quantification over future worlds remains essential for allocation.

In notation, for every $j<n$ and admissible future $U$ and satisfying heap $h$,

$$\lambda x.b\in\llbracket A\to B\rrbracket(n,W)
\Longrightarrow
\big(a\in\llbracket A\rrbracket(j,U)\Rightarrow
\operatorname{Safe}(B,j,U,h,b[a/x])\big).$$

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
Only null/Boolean predicates are exported today; numeric notation illustrates a
future extension. These assertions are duplicable facts, not exclusive write
permissions. This is a chosen plain-cell interpretation, not a theorem equating
SKJS's internal types with heap assertions.

The finite assertion layer also records two relationships between bindings,
interpreted by `HeapLinks.Holds`:

$$
\begin{aligned}
\operatorname{read}(x,y)&\equiv
  \exists\ell.\;\rho(x)=\ell\land h(\ell)=\rho(y),\\
x=y&\equiv\rho(x)=\rho(y).
\end{aligned}
$$

A read relationship depends on the current heap. Slot equality does not: two
copied references remain the same location after writes. Allocation preserves
both relationships; an arbitrary write or call preserves binding equality but may
invalidate any read relationship. The checked rules conservatively discard all
read relationships on writes/calls. The syntax owner is the
[assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar); operational rules
and alias handling belong to [Program typing](PROGRAM-TYPING.md#checked-expression-postconditions).

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
