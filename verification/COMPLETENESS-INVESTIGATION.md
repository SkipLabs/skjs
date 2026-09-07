# Equality completeness for the stateful recursive-type fragment

For closed types built from `null`, `bool`, invariant references and function
types, with guarded regular recursion — including recursion through either arrow
position and mixed reference/function cycles — semantic equality in the model
described in [SEMANTICS.md](SEMANTICS.md) **is** bisimulation of the
corresponding finite graph, in both directions.

The result needs no runtime type test, no new type constructor, no extra
equation and no quotient of budgets. The observations that separate inequivalent
types are already available in the model as it stands, which is the part worth
checking.

## Exact theorem

`lean/Verification/ExperimentState/Separation.lean`, `semantic_eq_iff`:

```lean
theorem semantic_eq_iff (G : Graph (Fin m)) (i j : Fin m) :
    FamEq (denote G i) (denote G j) ↔ Eq G G i j
```

`G` is a finite graph whose nodes are `nul`, `bool`, `ref a`, or `arr a b`.
Every edge is guarded by a reference or arrow constructor. Multiple roots in
one graph represent the types being compared; separate finite type descriptions
can be represented together in a common graph.

`FamEq` is equality at **every budget, world, and value** in the existing model.
`Eq` is the cyclic structural equality judgment: existence of a bisimulation
relating the roots. For finite graphs its relation is a finite certificate.
The theorem is semantic completeness for this judgment, not merely a theorem
relating two definitions of tree equality.

The interpretation uses the existing `nulT`, `boolT`, `refT`, `arrowT`, and
step-indexed safety semantics. `denote_unfold` establishes the graph equations;
`denote_unique` proves that their solution is unique. `denote_adm` and
`denote_valOnly` establish that these are admissible value types. This does not
assume a separate tree-valued denotation and call it the operational model.

`arrow_operands_equal` is a consequence: equal interpretations of actual arrow
nodes imply equal interpretations of their two operands. The proof does **not**
assume arrow injectivity on arbitrary admissible families.

## Why separation works

First, every finite graph has a common canonical world and heap. There is one
cell for each type node, with that type as its invariant. Canonical values are
null, true, a reference to the appropriate cell, or a diverging function.
`canonical_mem`, `graphWorld_adm`, and `graphHeap_ok` prove membership,
admissibility, and heap satisfaction at every budget. This includes cyclic
heaps and negative recursive types, not just acyclic examples.

A separator is a value that belongs to one type at every budget in every world
extending this canonical world. Above a finite budget threshold it fails the
other type in every **admissible, inhabited** extension. It is closed with
respect to term variables; it can capture locations in the canonical heap.

The inhabited-world condition on the negative side matters. An admissible
extension may contain an empty contract and therefore have no satisfying heap.
An arrow's safety obligations can be vacuous there. The proof does not assume
that arbitrary admissible extensions are inhabited.

Separators lift through the constructors:

1. Different head constructors are separated by canonical values.
2. A reference to a cell with one element contract distinguishes unequal
   element contracts. Reference equality is invariant.
3. An arrow-result separator is returned by a constant function.
4. An arrow-argument separator is passed to a function which writes its
   argument into a captured cell and then diverges. The cell's invariant checks
   the argument semantically, independently of the result type.

The last construction is the decisive answer to the weak-term-language concern:

```text
fun x => let _ = write capturedCell x in diverge
```

No runtime typecase is involved. A wrong write violates heap satisfaction, which
is an explicit requirement of `Safe`. The program can continue diverging without
ever producing a runtime type error. The separation is nevertheless valid for
the indexed interpretation whose equality is being axiomatized.

`no_apart_bisim` proves that pairs without such separators form a bisimulation.
Combined with `bisim_sound`, this yields `semantic_eq_iff`. `separation` also
exports the separating-witness existence theorem for inequivalent roots.

## What happened to the budget-zero counterexample?

It remains a valid objection to injectivity on arbitrary admissible families.
It is not a counterexample for this graph-denotable fragment. The completeness
proof works on the fragment directly and never needs the false general lemma.

`ref_observes_zero` additionally proves that simply identifying families which
agree at positive budgets is not a congruence for the existing reference
constructor. A discrepancy at zero becomes a discrepancy at budget one under a
reference. No such identification was used to obtain completeness.

## What the graph fragment can express

A finite graph is a system of guarded equations `Xᵢ = nodeᵢ`, so the types it
describes are exactly the **regular trees** over the signature — trees with
finitely many distinct subtrees. Mutual recursion is native: several roots in
one graph, with no encoding.

Four things fall outside, in different ways.

- **Unguarded recursion**, excluded *by construction*: `Node` has no variable
  case, so every node carries a constructor and every cycle passes through one.
  `X = X` cannot be written. That is the right exclusion, since it has no
  denotation here.
- **Open types.** No variable node means no free parameters, hence no schemes
  and no substitution. Closed types only.
- **Irregular trees** — infinitely many distinct subtrees, which arise from
  non-uniform recursion, where a parameter grows at each turn.
- **Everything outside the four constructors.**

## Correspondence with TypeScript

Two separate questions: whether the recursion has the right shape, and whether
the signature matches.

The recursion matches for the monomorphic part, and the boundary is sharp.
Probing SKJS:

| source | verdict |
| --- | --- |
| `type R = { next: R }`, and mutual `A` / `B` | accepted — a finite graph |
| `type U = U` | rejected: *"Type alias 'U' circularly references itself"* |
| `type T<X> = { next: T<{ v: X }> }` used at `T<null>` | **accepted** |

The first two agree with the graph representation exactly, including its
exclusion of unguarded recursion. The third does not: `T<null>` unfolds to
`T<{v: null}>` to `T<{v: {v: null}}>`, every subtree distinct, so an irregular
tree and not a finite graph — and SKJS accepts it.

So SKJS's representation is neither binder syntax nor graphs but a third thing:
**named types with arguments, expanded on demand under a depth cap**. That
denotes a regular tree only while the parameters do not grow, and the cap is a
decision-procedure choice rather than a semantic one.

The signature gap is larger. `ref` is not a TypeScript type at all: it
corresponds to a **one-field mutable object**, mutability in TypeScript being a
property of a non-`readonly` field. Real object types have several fields,
optional fields and readonly views, each changing the variance story — and then
unions, intersections and literal types, which change the theory rather than
merely the coverage.

One alignment is worth recording. SKJS's cycle cache — record the pairs under
comparison, succeed on a repeat — *is* a bisimulation certificate. The shape of
the judgment already matches what the implementation does.

## Relation to the classical equational theory

The theorem characterises semantic equality by bisimulation and gives no
equational theory. One exists, and is classical.

- **Milner (1984)** — equational axioms plus a **unique-solution rule for
  guarded systems** is sound and complete for bisimulation of regular
  behaviours.
- **Salomaa (1966)** is the ancestor, for regular expressions; his fixed-point
  rule carries a side condition, the empty-word property, which is exactly the
  guardedness condition here. Without it the rule is unsound: `X = X` has many
  solutions.
- **Amadio and Cardelli (1993)**, then **Brandt and Henglein (1998)**, do it for
  recursive types specifically — sound and complete axiomatisations of equality
  *and* subtyping, with the cycle handled by an Amber-style rule over an
  assumption set.

So unfolding, unique guarded fixed points and congruence *are* complete for tree
equality. That was the shape guessed in the earlier attempt; what was missing
was the model half — whether tree-distinct types are semantically distinct — and
that is what the theorem above supplies for this fragment. The two compose:

    ⊢ t = u    ⟺    t, u bisimilar    ⟺    ⟦t⟧ = ⟦u⟧
              (Milner, Brandt–Henglein)      (semantic_eq_iff)

If a derivational theory is ever wanted in place of bisimulation certificates,
only the left equivalence is unformalised here, and it is known.

Two caveats. Completeness of the subtyping axiomatisation needs assumptions
usable only beneath a guard; and with no top, bottom or unions the relation
collapses to equality, so there is nothing yet to be complete about. Once unions
and intersections arrive this body of results stops applying — the relevant line
is then semantic subtyping (Frisch, Castagna, Benzaken), a different and harder
theory. That is the same boundary the scope section below reaches from the model
side.

## Scope and remaining work

The equality-completeness question is settled for the fragment above, subject
to reviewing the definitions as well as the Lean proofs. It does not establish:

- **Completeness of subtyping.** Equality reflection is not a proof that a
  directional subtyping procedure captures every semantic inclusion.
- **A particular executable equality checker.** The judgment uses finite
  bisimulation certificates, but no checker implementation is verified here.
- **A binder-based source-type translation.** Graphs avoid binder substitution
  in this investigation. If the input uses named aliases or mu-binders, their
  translation still needs the appropriate binding and equation results.
- **Boolean type algebra.** There are no union, intersection, difference, top,
  or empty-type syntax nodes. Adding these changes the equational theory. For
  example, an everywhere-empty argument type makes `0 → A` and `0 → B` equal;
  free tree equality then ceases to be the correct complete judgment.
- **Type parameters or generics.** There are no free parameter nodes, bounded
  quantifiers, `extends` constraints, or polymorphic functions. In particular,
  arbitrary admissible parameter interpretations cannot be treated as if they
  automatically inherit the established graph-fragment reflection theorem.
- **Structural object views, refinement rules, or the claim verifier.** These
  require their own sound rules and integration results.
- **Contextual equivalence or reachability from an empty heap.** The canonical
  heaps satisfy the invariants; this investigation does not prove that programs
  can allocate every such cyclic heap from an empty heap. Nor does it identify
  indexed equality with indistinguishability by executable contexts.

The practical recommendation is to keep the world model and the regular graph
type representation. Recursive equality for this fragment no longer needs to
be an open research gate. Investigate the required Boolean/narrowing algebra
next; give it an explicit equational theory rather than trying to preserve
free-tree equality after adding Boolean operations. Treat subtyping and bounded
generics as separate extension theorems.

## Artifacts and verification

The result lives in the semantics development under
[`lean/Verification/ExperimentState`](lean/Verification/ExperimentState), whose
construction is described in [SEMANTICS.md](SEMANTICS.md). Two modules there
carry this investigation:

- `Completeness.lean` — types as finite guarded graphs, their denotation,
  uniqueness of graph-system solutions, the bisimulation judgment and its
  soundness, canonical worlds and heaps, and focused probes.
- `Separation.lean` — separating values and full equality completeness for
  finite graphs in the stated fragment.

`lake build` passes, with no admitted goals and no new axioms; the completeness,
separation and operand-reflection theorems use only `propext`,
`Classical.choice` and `Quot.sound`. Nothing is committed.
