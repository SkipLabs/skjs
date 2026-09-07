# Semantics

The stateful development in [ExperimentState](lean/Verification/ExperimentState)
provides the semantic foundation for the positive-type rules specified in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md). It is independent of the production F0
verifier. [PROGRAM-TYPING.md](PROGRAM-TYPING.md) specifies the proved program
typing system and checked control-flow graphs. Extraction for the extended
language remains an integration obligation.

## Operational language

`Language.lean` defines an untyped call-by-value language with functions,
application, null/booleans, heap locations, allocation, reading, writing, shape
tests, and conditionals. Values are a subset of terms. `Step_det` proves that a
term and heap have at most one successor.

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

Program/claim extraction, a serialized certificate decoder, and integration
with the production verifier remain. A bounded in-memory producer now builds
checked evidence from supplied point annotations, with exact claim fidelity.
Global graph execution safety includes explicit edge slot mappings for scope
changes, reordering and alias retention. Graph-backed closure bodies remain an
extension. The proved program rules currently use known shape answers per overload;
general branch-environment refinement remains to be supplied. Mutable objects and refinements need a specified policy beyond invariant
cells. Parameters, bounded polymorphism, difference and negation require
additional syntax and sound rules; no generics result is claimed merely from
being able to define quantification over semantic families.
