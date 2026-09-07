# Completeness for the stateful recursive-type fragment

For closed types built from `null`, `bool`, invariant references and function
types, with guarded regular recursion — including recursion through either arrow
position and mixed reference/function cycles — semantic equality in the model
described in [SEMANTICS.md](SEMANTICS.md) **is** bisimulation of the
corresponding finite graph, in both directions.

Adding unions in operand position keeps the pattern and turns it into a
subtyping result: semantic **inclusion** is exactly clause-to-clause covering.
That half is [below](#unions-inclusion-is-covering).

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

## Unions: inclusion is covering

`lean/Verification/ExperimentState/Union.lean`, `sim_iff_incl`:

```lean
theorem sim_iff_incl (G : Graph (Fin m)) (hwf : WF G) (S T : List (Fin m)) :
    Sim G S T ↔
      ∀ (n : Nat) (v : Val),
        denoteSet G S n (graphWorld G n) v → denoteSet G T n (graphWorld G n) v
```

Here a node's operands are *sets* of nodes read as their union, and a type is
likewise a set of nodes — so unions occur at every position, not only at the
top. `ref A ∨ ref B ≠ ref (A ∨ B)` (`ref_union_ne_union_ref`) is why they cannot
be normalised out of operand position. `Sim` is a covering certificate: a
relation on clause sets under which every clause of the source is matched by a
clause of the target — an atom by presence, a reference invariantly, an arrow
contravariantly in the domain and covariantly in the codomain, with an empty
operand waiving the comparison on the other side. The certificate is finite, and
inclusion is required only at the canonical worlds; `sim_sound` returns it at
every world.

### Why a clause-to-clause rule can be complete here

In a pure language it cannot. A function on a one-element domain either returns
a null or returns a boolean, so

    nul → (nul ∨ bool)  ≤  (nul → nul) ∨ (nul → bool)

and no rule matching one source clause against one target clause derives it.
This is the inclusion that forces semantic subtyping to decompose arrows over
unions set-theoretically.

In this model the inclusion is **false** (`no_arrow_splitting`). A function that
reads a cell declared `nul ∨ bool` lies in the source type and in neither
disjunct: an arrow quantifies over every satisfying heap, and one heap holds
`true` where another holds `null`. State supplies the branch a type test would
have supplied. So the obstacle to clause-to-clause matching is absent, and the
rule is complete rather than merely sound.

### The observations

Completeness is proved by giving each clause of the source a value that inhabits
it and escapes the *whole* target. The union is in that "whole": a single value
must fail every clause of the target at once, and the budgets above which it
fails each of them are combined by the finiteness of the clause list
(`sep_of_clauses`).

| source clause | observation |
| --- | --- |
| `nul`, `bool` | the value itself; each shape of value belongs to one shape of node |
| `ref a` | the canonical location of `a`; a target clause can accept it only by being a reference whose operand denotes the *same* family (`ref_invariance_forced`) |
| `arr a b` | a **probe**: write the argument into a cell declared at `a`, return the contents of a cell declared at `b` |
| `arr [] b` | a function that would get stuck if applied — an arrow with an empty domain is never applied |
| `arr a []` | write the argument, then diverge — an arrow with an empty codomain never returns |

The probe observes both sides of an arrow at once, which is what a union in the
target requires. A target clause `arr c d` rejects it either because some
argument in `c` cannot be written into the cell at `a` — leaving a heap no world
satisfies (`probe_escapes_dom`) — or because the observer planted in the cell at
`b` a value that `d` does not accept (`probe_escapes_cod`). The second is
available precisely because an arrow quantifies over every satisfying heap. The
two cells are distinct even when `a` and `b` are the same set, which is why the
canonical world declares two cells per operand set; sharing one would let the
write destroy the reading.

## The rule in practice

Two questions this section answers: what exactly the well-formedness restriction
rules out, and what the "equational theory" now consists of. Before unions,
equality was bisimulation, so the classical equations for bisimulation were the
whole story. With unions the judgment is a *simulation* rather than a
bisimulation, and the theory changes shape; but it does not grow a Boolean
algebra.

### The restriction, exactly

    WF G   ⟺   no node of the graph is  ref never

One syntactic, local check: look at each node, reject the single shape `ref ∅`.
`ref` is this model's one-field mutable object, so in source terms it forbids
**declaring a mutable cell whose content type is empty**.

| | |
| --- | --- |
| forbidden | `ref never` — a cell that could hold nothing |
| excluded as a consequence | `ref (ref never)`, `ref (ref (ref never))`, … — each needs the level below it as a node, so removing the base removes the tower |
| still allowed | `never` as an arrow domain (`never → A`) or codomain (`A → never`); `never` as a type in its own right — the empty clause set; an empty union anywhere except under `ref` |

What it costs: a declaration nothing could ever construct is rejected up front
instead of accepted and then unusable. No program that allocates is affected,
because no program could allocate such a cell in the first place.

Why not handle it exactly instead: the exact condition counts evaluation steps.
`ref never` is unreachable above budget zero, `ref (ref never)` above budget one,
and an arrow demands nothing below budget two (`Safe_app_one`), so the side
condition would have to say at which budget a type becomes visible — an artifact
of the step-indexed model leaking into the type rules.

What it buys: under `WF`, every non-empty clause set is inhabited, and inhabited
in a world that an actual heap satisfies (`wf_inhabited`). "There is a clause"
then implies "there is a value", which is what makes every clause observable and
so what makes the rule complete. Without it, two types could differ in a clause
that no value ever witnesses.

### The judgment, written out

`S ≤ T` is the largest relation on clause sets satisfying, for each clause of
`S`:

    null ∈ S                ⟹   null ∈ T
    bool ∈ S                ⟹   bool ∈ T
    ref a ∈ S               ⟹   ∃ ref b ∈ T.   a ≤ b   and   b ≤ a
    (a → b) ∈ S             ⟹   ∃ (c → d) ∈ T.  c = ∅
                                             or  (c ≤ a  and  (b = ∅  or  b ≤ d))

A certificate is any relation closed under those conditions and containing the
pair in question (`Sim`, `SimRel`, `Cover`). On a finite graph it is finite, and
a cycle is discharged by finding the pair already in it — which is exactly what
SKJS's cycle cache does today.

The two vacuity escapes are not decoration. `c = ∅` says an arrow that is never
applied is above every arrow; `b = ∅` says an arrow that never returns is below
every arrow with a suitable domain. `arr_empty_dom` is a checked instance where
dropping the first escape would make the rule incomplete.

### What the equational theory is

Three layers, and nothing else.

1. **Absorbed by the representation.** A type *is* a finite set of clauses, so
   `∨` is associative, commutative and idempotent with unit `never` by
   construction — those laws are never stated or applied. Recursion is a system
   of guarded equations, so fold/unfold is likewise free (`denote_unfold`).
2. **The four constructor rules above.** Atoms by presence, references
   invariantly, arrows contravariantly with the two vacuity escapes.
3. **Coinduction.** An assumption citable once a guard has been crossed. This is
   the analogue of Milner's unique-solution rule, and it is what makes the finite
   certificate legitimate rather than circular.

What is conspicuously *absent* is the machinery a pure language would need:

- **No distribution through `ref`.** `ref A ∨ ref B` and `ref (A ∨ B)` are
  different types (`ref_union_ne_union_ref`). References are invariant —
  `ref A ≤ ref C` forces `A` and `C` to denote the same family
  (`ref_invariance_forced`) — so both directions of distribution fail unless the
  union collapses. There is no law to add; the representation carries unions in
  operand position precisely because none exists.
- **No arrow decomposition over unions.** In a pure language
  `A → (B ∨ C)  ≤  (A → B) ∨ (A → C)` holds and no clause-to-clause rule derives
  it, which is what forces semantic subtyping to decompose arrows
  set-theoretically. Here the inclusion is **false** (`no_arrow_splitting`), so
  there is nothing to derive.
- **No normal form and no Boolean algebra.** No intersection, no difference, no
  top — so no DNF, no emptiness test on a Boolean combination.

### The check, and what it costs

The practical content of completeness is that the check decomposes:

    S ≤ T   ⟺   for every clause i of S, there is a clause j of T with [i] ≤ [j]

That is `sim_pairwise`, and both halves are checked. Left to right is
**union-primality** — a single clause included in a union is included in one
member of it (`sim_clause_prime`, and semantically `incl_clause_prime`). Right to
left is that a union on the left is handled clause by clause. So a checker never
reasons about a union as a whole: it enumerates clauses on both sides and, for
each source clause, searches for one target clause that matches.

Union-primality is the property that fails in a pure language: there the single
clause `nul → (nul ∨ bool)` is included in `(nul → nul) ∨ (nul → bool)` without
being included in either member, so no amount of clause matching finds the
inclusion. Here that inclusion is false, and primality survives — for the same
reason, and it is the same theorem.

What an implementation therefore needs, beyond what is already there: clause
enumeration on both sides; a per-source-clause search over target clauses, with
the matching pair for an arrow chosen together; invariant recursion under `ref`;
the two vacuity escapes; and the well-formedness pre-check. Termination is not
formalised, but nothing in the rule constructs a new clause set — every set it
compares already occurs in the graph — so the greatest covering relation is a
fixed point over a finite set of pairs.

### What this does not settle

Intersections, negation and top are absent, so this is the union fragment and
not a Boolean algebra of types. Nothing here is a decision procedure with a
proved complexity bound, and nothing connects the rule to a subsumption rule in
the typing judgment: covering is proved to characterise inclusion, but no typing
rule yet uses an inclusion to retype a term.

## Intersections: what the model already decides

Before designing a rule, it is worth knowing which laws the model will accept.
The answer is not the expected one, and it is checked in `Intersection.lean`.

**The classical arrow decomposition is unsound here.** The law every treatment
of overloaded function types has, and an instance of the Frisch–Castagna–Benzaken
decomposition, is

    (A → B) ∧ (A → C)  ≤  A → (B ∧ C)

and `arrow_inter_codomain_fails` refutes it. Allocation is the reason. A cell
carries one invariant, fixed when it is allocated, and a location belongs to
`ref X` only when the world's contract for it *equals* `⟦X⟧`. So `λx. alloc null`
inhabits both `A → ref null` and `A → ref (null | bool)` — each membership
choosing a different contract for the new cell — while `ref null ∧ ref (null |
bool)` is empty. The left-hand side contains a function that returns; the
right-hand side contains only functions that never do.

**The law holds for rigid codomains.** Where membership depends on the value and
not on the world, `arrow_inter_rigid_codomain` proves it. The argument needs
determinism of evaluation (`Step_det`, new): the two runs of the same program
take the same steps, so if either reaches a value it is the *same* value, and
rigidity carries the two judgments about it into a single world. Concretely, a
function that returns a null and returns a boolean on one domain returns nothing
there at all — it inhabits the arrow into the empty intersection
(`arrow_inter_nul_bool`).

**What else survives.** Two arrows cover the union of their domains
(`arrow_inter_dom_union`), and the clause rule that matches a source arrow
against a single target arrow stays sound (`arrow_inter_clause`).

So the rejected part is narrow and located: intersecting *world-dependent*
codomains. That is a distinction the classical theory has no vocabulary for,
which is why its rule cannot be imported, and it is the shape a rule for
intersections here would have to respect. Everything else about intersections
looks cheap: pointwise intersection is admissible already; value shapes are
disjoint, so `null ∧ ref a` is empty structurally; `ref a ∧ ref b` is empty
unless the operands denote the same family, which mutual covering decides; and an
intersection of arrows is never empty, since a diverging function inhabits every
arrow. What that costs is the well-formedness check, which stops being syntactic
and becomes an emptiness test — still decidable with the machinery above.

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

Where the layers of [The rule in practice](#the-rule-in-practice) come from. The
equality theorem characterises semantic equality by bisimulation and gives no
equational theory of its own; one exists, and is classical.

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
usable only beneath a guard; and in the union-free fragment, with no top, bottom
or unions, the relation collapses to equality, so there is nothing there to be
complete about.

With unions the classical expectation is that this line of results gives way to
semantic subtyping (Frisch, Castagna, Benzaken), whose difficulty is exactly the
set-theoretic decomposition of arrows over unions. The result above says that in
a language with state that decomposition is not needed: arrows do not split, so
a clause-to-clause rule is already complete. What would bring the harder theory
back is intersection and negation, not union.

So the theory in force here is Milner's shape — congruence, guarded unique
solutions, coinduction over an assumption set — with inclusion in place of
equality, the union laws absorbed into the representation, and *no* Boolean
layer. That is the whole of it, written out in
[The rule in practice](#the-rule-in-practice).

## Scope and remaining work

The equality-completeness question is settled for the fragment above, subject
to reviewing the definitions as well as the Lean proofs. It does not establish:

- **Completeness of subtyping beyond unions.** Covering is proved complete for
  inclusion in the union fragment. Nothing is proved about intersections,
  negation, or a directional procedure over a richer type algebra.
- **A particular executable equality checker.** The judgment uses finite
  bisimulation certificates, but no checker implementation is verified here.
- **A binder-based source-type translation.** Graphs avoid binder substitution
  in this investigation. If the input uses named aliases or mu-binders, their
  translation still needs the appropriate binding and equation results.
- **Boolean type algebra.** Unions are covered; intersection, difference and
  top are not. The vacuity these bring is already visible in the union
  fragment — an everywhere-empty argument type makes `0 → A` and `0 → B` equal,
  which is why covering waives the comparison at an empty operand, and why
  `ref never` is excluded by well-formedness rather than handled.
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
- `Union.lean` — unions in operand position: the representation, the covering
  judgment, its soundness, the canonical world and heap over clause sets, the
  probe, completeness of covering (`sim_iff_incl`), union-primality of single
  clauses (`sim_clause_prime`, `incl_clause_prime`) and the clause-by-clause
  form of the check (`sim_pairwise`).
- `Intersection.lean` — the laws the model accepts and refuses for intersections
  of arrows, ahead of any rule: `arrow_inter_codomain_fails`,
  `arrow_inter_rigid_codomain`, `arrow_inter_dom_union`, `arrow_inter_clause`.

`lake build` passes, with no admitted goals and no new axioms; the completeness,
separation, operand-reflection and covering theorems use only `propext`,
`Classical.choice` and `Quot.sound`.
