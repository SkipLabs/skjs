# Semantics

The stateful development in [ExperimentState](lean/Verification/ExperimentState)
provides the semantic foundation for the positive-type rules specified in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md). It is independent of the production F0
verifier. The next integration obligation is program typing and checked
invariants for the extended language; subtype checking alone does not provide it.

## Operational language

`Language.lean` defines an untyped call-by-value language with functions,
application, null/booleans, heap locations, allocation, reading, writing, shape
tests, and conditionals. Values are a subset of terms. `Step_det` proves that a
term and heap have at most one successor.

The existing substitution operation is intended for closed substituted values.
A general typing environment, capture discipline and substitution theorem for
open terms have not been supplied by this development.

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

An arrow contains function-shaped values whose applications are safe for every
smaller budget, every admissible future world, every satisfying heap, and every
argument in the domain there. Quantification over future worlds is essential:
allocation and calls cannot invalidate the previously established guarantee.

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

Open-term program typing and its fundamental theorem, program/claim extraction,
a certificate producer and decoder, and integration with invariant checking
remain. Mutable objects and refinements need a specified policy beyond invariant
cells. Parameters, bounded polymorphism, difference and negation require
additional syntax and sound rules; no generics result is claimed merely from
being able to define quantification over semantic families.
