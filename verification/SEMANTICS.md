# Semantics

What a semantics for the calculus has to satisfy, the construction that
satisfies it, and how far that construction has been carried. Checked in
[`lean/Verification/ExperimentState`](lean/Verification/ExperimentState); the
roadmap and the connection to the verifier are in [DESIGN.md](DESIGN.md).

## What a recursive-type semantics must satisfy

A recursive type has to *mean* something before a checker can be trusted about
it. Four properties are needed, and the first rules out the usual way of
getting the others.

**1. Membership is not a fixed point of the unfolding operator on sets.** Once
the recursion can reach a function's argument position it occurs negatively, so
that operator is not monotone and Knaster–Tarski supplies neither the least nor
the greatest fixed point. "The greatest set consistent with one unfolding" is
therefore unavailable as a definition. A fixed point still exists — see below —
but it has to be obtained another way.

**2. `μX.t = t[μX.t]`, at every index.** A source language treats a recursive
type and its unfolding as one type, and TypeScript states the judgement
directly:

```typescript
type R = { next: R };      function unfold(x: R): { next: R } { return x; }
```

This is a condition on **membership**, not a rule to add to subtyping: if the
two denote different sets then a fold/unfold rule is unsound rather than merely
unproved. It also fixes where the index may be spent — at a dereference or a
call, never on rewriting a type.

**3. Downward closed in the index.** A value that passes at depth `n+1` must
pass at `n`, or something checked once cannot be used by anything that looks
less hard.

**4. Stable under allocation.** A function that vacuously satisfies `A → B` in
a store containing no `A` must not stop satisfying it once one is allocated.

Properties 2 and 3 are the price of property 1: where a fixed point is
available, 2 is precisely what having one means and costs nothing.

**Reading an index.** At a finite index the denotation is an approximation and
admits values the type does not — a finite null-terminated chain is in `⟦R⟧₁`
and in no `⟦R⟧ₙ` for `n ≥ 2`, so it is not in `⋂ₙ ⟦R⟧ₙ`, which is the type.
Property 2 says the two spellings agree at each index, not that different
indices agree.

## Budgets, and the guarded fixed point

A type is a **family of approximations** indexed by a budget: for each `n`, the
values that still look like the type after `n` steps of inspection. The type is
the intersection over budgets. Write `▷T` for the family one level down. The
budget is spent only where the program spends one, at a dereference or a call,
never on rewriting a type.

An operator `F` on families is **contractive** when `F(T)` at budget `n`
consults `T` only strictly below `n` — exactly "every recursive occurrence is
guarded". That makes the recursion well founded: level `n+1` depends only on
level `n`, never on itself. So the tower

    ⊤,  F(⊤),  F(F(⊤)),  …

stabilises below its own height, its diagonal is coherent, and that diagonal is
a fixed point of `F`. This is Banach's theorem, on a space where distance is
the first budget at which two families disagree.

    T ∈ Fam            =  (n : ℕ) → World n → Val → Prop

    (▷T)₀ (W, v)       ⟺  ⊤
    (▷T)ₙ₊₁ (W, v)     ⟺  Tₙ (W↾n, v)

    F contractive      ⟺  (∀ m < n. F's argument matters only at m)
                       ⟺  (∀ m < n. Tₘ = Uₘ)  ⟹  F(T)ₙ = F(U)ₙ

    iter F 0           =  ⊤
    iter F (k+1)       =  F (iter F k)
    (μF)ₙ              =  (iter F (n+1))ₙ

    F contractive      ⟹  μF = F(μF)                        at every budget

Property 2 comes from the construction: being a fixed point *is* the equation,
and uniqueness comes with it, so a recursive type is determined by its equation
rather than merely solving it. Properties 3 and 4 do not come free — they are
proved for each constructor and then lifted through the tower, so every new
constructor owes them. Property 1 is *escaped* rather than satisfied: nothing
here asks for monotonicity, so a fixed point exists even where recursion runs
through an argument position.

## What a value is judged relative to

Membership is relative to something, and the choice is not free.

Judging against a **store of values** — follow the pointer, inspect what is
there — is enough to settle recursion, and it is wrong as soon as the language
can write. Membership then depends on heap contents: overwriting one cell can
destroy the membership of values that had nothing to do with it, and there is
nothing to prove about it, because nothing says what a location was *supposed*
to hold. "This write respects the location's type" is not expressible.

So the index is a **world**: a contract for each location. Membership at a
reference consults the world, and a separate invariant relates an actual heap to
it. Membership then never mentions the heap, so no write can disturb it, and
preservation reduces to a local check at the location written. "A future state"
also acquires a meaning — more locations declared, none redeclared — replacing a
syntactic quantification over store extensions.

## Stratified worlds

A world assigns contracts to locations; a contract judges values against
worlds. The circularity is broken by stratifying on a level:

    World k  =  Loc → ( contracts that inspect worlds at any level < k )

which is one well-founded recursion.

    World k            =  List (Ctr k)
    Ctr k              =  (j : ℕ) → j < k → World j → Val → Prop

    (W ↾ j) (l)        =  λ i (hi : i < j) w. W(l) i (hi ; j ≤ k) w      j ≤ k
    W ⊑ W'             ⟺  ∃ tail. W' = W ++ tail

The choice that makes this cheap is that a contract is **uniform in the level**:
it accepts *any* `j < k` and a world at that level, rather than being pinned to
one level. Restricting a world to a lower level is then only a weakening of the
bound each contract accepts. So truncation is an equality-preserving operation
— identity at the same level, composing, and preserving extension — and no
embedding in the opposite direction is ever needed. That reverse embedding is
what defeats the naive encoding `World (n+1) = Loc → (World n → Val → Prop)`.

The coherence laws are then equalities:

    W ↾ k              =  W
    (W ↾ j) ↾ i        =  W ↾ i                              i ≤ j ≤ k
    W ⊑ W'             ⟹  W↾j ⊑ W'↾j

Truncation still discards *access* to higher-level observations; that is its
purpose. What is cheap is the operation, not the approximation.

Not every contract is a type. A contract must survive the world growing, or
allocation destroys it. This is not a technicality: a contract constraining the
*size* of the world is otherwise legal, a heap can satisfy it, and any
allocation then breaks the invariant — so no function that allocates could be
safe anywhere. Worlds appearing in execution obligations are therefore
restricted to admissible contracts.

    CtrAdm c           ⟺  ∀ j < k, W ⊑ W', v.  c j W v → c j W' v
    WorldAdm W         ⟺  ∀ l c. W(l) = c → CtrAdm c

The same requirement, one level up, says which families are types:

    Adm T              ⟺  ∀ n W v.  Tₙ₊₁ (W, v) → Tₙ (W↾n, v)          (down)
                       ∧  ∀ n W ⊑ W', v.  Tₙ (W, v) → Tₙ (W', v)        (mono)

and the constructors are then

    ⟦null⟧ₙ (W, v)     ⟺  v = null
    ⟦bool⟧ₙ (W, v)     ⟺  v = true ∨ v = false
    ⟦ref T⟧ₙ (W, v)    ⟺  ∃ l c.  v = loc l  ∧  W(l) = c
                              ∧  ∀ j < n, W'.  c j W' = Tⱼ W'

`ref` reads its element type only strictly below `n`, so it is a guard and
`μX. ref X` exists.

## Heaps

The world says what a location is for; the heap says what it holds. The
invariant relates them: every declared location holds a value meeting its
contract, at every level below the current one, with the world truncated to
match.

- **Read** yields a value meeting the location's contract.
- **Write** preserves the invariant when the new value meets that contract —
  including when the location is reachable through another reference, because
  no other location's obligation mentions the heap.
- **Allocation** preserves it provided the world's contracts are admissible.
  That requirement is load-bearing and belongs to the contracts, not to any one
  type constructor: every existing location's obligation must survive the world
  growing.

<!-- -->

    h ⊨ₙ W             ⟺  |h| = |W|
                       ∧  ∀ l c. W(l) = c →
                            ∃ v. h(l) = v ∧ ∀ j < n. c j (W↾j) v

## Execution and safety

Safety of a term at budget `n`, in a world and a heap, says that running it
never gets stuck, and that if it reaches a value with budget left, that value
is in the type. **Each step spends a level, and the world drops with it**: the
world after a step extends the truncation of the one before, and is itself
admissible.

    Safe T 0 W h t     ⟺  ⊤
    Safe T (n+1) W h t ⟺  ( t is a value ∧ Tₙ₊₁ (W, t) )
                       ∨  ∃ W' ⊒ W↾n, h', t'.  WorldAdm W'
                            ∧ (h, t) → (h', t')
                            ∧ h' ⊨ₙ W'
                            ∧ Safe T n W' h' t'

A function type is safety in every future world and every heap satisfying it,
at every strictly smaller budget.

    ⟦A → B⟧ₙ (W, v)    ⟺  v is a λ
                       ∧  ∀ j < n, W' ⊒ W↾j with WorldAdm W',
                            ∀ h ⊨ⱼ W', a ∈ ⟦A⟧ⱼ(W').
                              Safe B j W' h (v a)

Both operands are read strictly below `n`, so an arrow is a guard in its
argument *and* in its result: `μX. X → null` and `μX. null → X` both exist.

This is the repair that a step-free reading gets wrong. If the arrow relates
arguments directly to final results, the obligation on a function's body lands
one level above what the argument's own guarantees supply, and the type
collapses — `μX. X → null` becomes "returns null on every input whatsoever",
which excludes programs an ordinary typing derivation accepts. Threading the
steps makes the level a call pays for exactly the level at which the argument's
guarantees are available.

## Compatibility rules

Safety proofs are assembled from rules rather than traced:

- **Abstraction** — the body is obliged exactly one level below the argument,
  which is the level the beta step pays for. This is where the budget
  arithmetic lives, and nowhere else.
- **Application** and **beta**.
- **Allocation**, **read**, **write** — the last two stated against any
  contract *agreeing with* the type, which is what a reference type supplies.
- **Bind** — run a subterm, then continue with whatever value it produces, in
  whatever world and heap it produced them.

<!-- -->

    A ⊆ values    ∀ p+1 < k, W' ⊒ W↾(p+1) adm, h ⊨ W', a ∈ ⟦A⟧ₚ₊₁(W').
                      Safe B p (W'↾p) h (b[a])
    ───────────────────────────────────────────────────────────────────  abs
                          λb ∈ ⟦A → B⟧ₖ (W)

    v ∈ ⟦A → B⟧ₖ(W)   j < k   W' ⊒ W↾j adm   h ⊨ⱼ W'   a ∈ ⟦A⟧ⱼ(W')
    ───────────────────────────────────────────────────────────────────  app
                        Safe B j W' h (v a)

    a value    Safe B p (W↾p) h (b[a])
    ──────────────────────────────────────────  beta         W : World (p+1)
      Safe B (p+1) W h ((λb) a)

    Adm A    v value    WorldAdm W    h ⊨ₙ W    v ∈ ⟦A⟧ₙ(W)
    ───────────────────────────────────────────────────────────────────  alloc
              Safe (ref A) n W h (alloc v)

    W(l) = c    c agrees with A below n    WorldAdm W    h ⊨ₙ W
    ───────────────────────────────────────────────────────────────────  read
                    Safe A n W h (read l)

    …  and  v ∈ ⟦A⟧ₙ(W)
    ───────────────────────────────────────────────────────────────────  write
                 Safe null n W h (write l v)

    Safe A n W h a
    ∀ j ≤ n, W' ⊒ W↾j adm, h' ⊨ⱼ W', v ∈ ⟦A⟧ⱼ(W').  Safe B j W' h' (f v)
    ───────────────────────────────────────────────────────────────────  bind
                        Safe B n W h (f a)                      f value

## What is established

- A recursive reference type `R = ref R` satisfies its unfolding equation at
  every level, and has an inhabited **cyclic heap**.
- A type parameter under a reference is inhabited for *every* semantic type —
  the failure that motivated worlds is repaired, and repaired at the point where
  it broke.
- Allocation, read and write preserve the heap invariant, with admissibility
  carrying allocation.
- Function types are admissible, and a recursive function type `μX. X → null`
  is inhabited by a function that calls its own argument.
- A closure over a mutable cell stays safe after another reference writes to it.
- These compose: a program that allocates a cell, changes it through one
  reference, and reads it through a closure that captured another is safe — and
  its observed value really changes.
- A callable whose body is stuck is rejected, so none of the above is vacuous.
- Evaluation is **deterministic** (`Step_det`). Safety does not say so — it
  quantifies existentially over the world a step lands in — so it has to be
  proved, and it is what lets two runs of one program be compared.
- For closed types built from these constructors, semantic equality **is**
  bisimulation of the corresponding finite guarded graph, in both directions.
  See [COMPLETENESS-INVESTIGATION.md](COMPLETENESS-INVESTIGATION.md).
- The recursive type is unique: any family satisfying `U = F(U)` for a
  contractive `F` *is* `μF` (`fix_unique`), and `μX. ref X` and
  `μX. ref (ref X)` are therefore the same type (`R_eq_ref_ref`). Heads are
  disjoint and `ref` is injective on element types.
- With unions in operand position, **inclusion is exactly clause-to-clause
  covering** (`sim_iff_incl`), for well-formed graphs. This is a subtyping
  result, not only an equality one, and it holds because state supplies the
  observation that makes arrows fail to split.

## Unions, and why covering is complete

A type is a set of nodes read as its union, and so is every operand — which
`ref A ∨ ref B ≠ ref (A ∨ B)` makes necessary. The judgment is clause-to-clause
covering: an atom by presence, a reference invariantly, an arrow
contravariantly, with an empty operand waiving the comparison on the other
side. Covering is sound *and complete*:

    Sim G S T   ⟺   ∀ n v.  v ∈ ⟦S⟧ₙ(W_G n) → v ∈ ⟦T⟧ₙ(W_G n)

Inclusion has to hold only at the canonical worlds `W_G`; soundness gives it
back at every world. Intersections, negation and top are still absent, so this
is the union fragment and not a Boolean algebra of types.

The practical form is that the check decomposes: `S ≤ T` exactly when every
clause of `S` is below a *single* clause of `T` (`sim_pairwise`), because a
single clause included in a union is included in one member of it
(`sim_clause_prime`). The rules, the restriction they need, and what the
resulting equational theory does and does not contain are written out in
[COMPLETENESS-INVESTIGATION.md](COMPLETENESS-INVESTIGATION.md#the-rule-in-practice).

Completeness is not what a pure language would give. There, a function on a
one-element domain either returns a null or returns a boolean, so
`nul → (nul ∨ bool)` is below `(nul → nul) ∨ (nul → bool)` and no
clause-to-clause rule can derive it. Here that inclusion is **false**
(`no_arrow_splitting`): a reader of a cell declared `nul ∨ bool` lies in the
source type and in neither disjunct, because an arrow quantifies over every
satisfying heap and one heap holds `true` where another holds `null`. State
supplies the observation a type test would have.

The proof turns that observation into a construction. Every clause of the source
gets a value that inhabits it and escapes the *whole* target: an atom by itself,
a reference by the canonical location of its operand, an arrow by a **probe** —
a function that writes its argument into a cell declared at the source domain
and returns the contents of a cell declared at the source codomain. The write
fails on an argument the domain cannot hold; the returned value is one the
observer planted, since an arrow quantifies over every satisfying heap. So one
value tests both sides of an arrow at once, which is what a union in the target
demands — a single value has to escape every clause, and the budgets above which
it escapes each of them are combined by the finiteness of the clause list. The
two cells are distinct even when the two operands coincide, which is why the
canonical world declares two per operand set.

Getting there needed a restriction rather than more rules. A cell declared to
hold nothing makes an arrow's obligation vanish, and chasing that exactly leads
to a side condition that counts evaluation steps — `ref never` is unreachable
above budget zero, `ref (ref never)` above budget one, and an arrow demands
nothing below budget two. That is an artifact of the model, not a fact about
types, so such cells are excluded by well-formedness instead. What remains is the
one obvious case, an empty union, which is a syntactic check. Well-formedness
earns its keep: under it every non-empty clause set is inhabited, in a world an
actual heap satisfies (`wf_inhabited`).

## What is not

No *binder* syntax, environments or substitution, and so no general binding
discipline. Types are represented as finite graphs, which cover closed regular
recursion and nothing else: no open types, and no irregular trees of the kind a
growing type parameter produces. The unfolding equation is therefore still not a
substitution theorem for an open recursive type. The typing rules have no
subsumption rule: covering is proved to characterise inclusion, but nothing
yet uses an inclusion to retype a term. Safety under
decreasing budgets and the remaining evaluation contexts are unproved, and there
is no adequacy theorem connecting safety to ordinary execution.

Intersections are not in the type language, but the model already constrains
what a rule for them could say, and the constraint is not the expected one. The
law every treatment of overloaded functions has,

    (A → B) ∧ (A → C)  ≤  A → (B ∧ C)

is **unsound here** (`arrow_inter_codomain_fails`). Allocation is why: a cell
carries one invariant, chosen when it is allocated, so `λx. alloc null` inhabits
`A → ref null` and `A → ref (null | bool)` — each membership picking a different
contract — while the intersection of those codomains is empty, since a location
belongs to `ref X` only when its contract *equals* `⟦X⟧`. The left-hand side
contains a function that returns; the right-hand side contains only functions
that do not.

The failure is narrow, and located. For **rigid** codomains — where membership
depends on the value and not on the world — the law holds
(`arrow_inter_rigid_codomain`), by determinism: the two runs take the same steps,
so the returned value is one value and the two judgments about it combine. What
also survives is covering the union of two domains (`arrow_inter_dom_union`) and
the clause rule that matches one conjunct (`arrow_inter_clause`). So the part of
the classical decomposition this model rejects is exactly the intersection of
*world-dependent* codomains — which is a distinction that theory has no
vocabulary for, and the reason its rule cannot simply be imported.

Quantified types are definable and admissible, and a bound is just an inclusion
between families, so the semantics of generics needs no new machinery. What is
missing is the fundamental theorem — one runtime function safe under every
admissible instantiation — and variance. Definability is not universality.

## Where it is checked

| file | contents |
| --- | --- |
| `Language.lean` | terms, values, substitution, the small-step relation |
| `Worlds.lean` | stratified worlds, truncation, extension, admissible contracts |
| `Types.lean` | semantic types, admissibility, the guarded fixed point, references |
| `Heaps.lean` | the heap invariant, allocation, read, write |
| `Safety.lean` | safety, function types, contractivity in both operands |
| `Rules.lean` | the compatibility rules |
| `Examples.lean` | the recursive function type, the captured cell, the combination |
| `Completeness.lean` | types as finite guarded graphs, their denotation, bisimulation and its soundness |
| `Separation.lean` | canonical worlds and heaps, separating values, equality completeness |
| `Polymorphism.lean` | quantified types: definability, bounds, admissibility |
| `Union.lean` | unions in operand position: the representation, covering, its soundness and its completeness |
| `Intersection.lean` | what the model decides about intersections before a rule is designed |

## Names

This is **step-indexed logical relations** (Appel and McAllester 2000) under a
**guarded recursion** discipline, with `▷` the **later modality** (Nakano 2000)
and the fixed point **Banach's** on a complete bisected ultrametric space —
categorically the **topos of trees** (Birkedal, Møgelberg, Schwinghammer,
Støvring), and the machinery that carries recursive predicates in **Iris**. The
combination with semantic worlds for higher-order mutable state follows
**Ahmed**, *Semantics of Types for Mutable State* (2004).
