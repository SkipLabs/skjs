import Verification.ExperimentState.Types
/-!
# Polymorphic types

Generics ask three things of a semantics — type variables, bounds, and a
quantifier — and this model already has all three, with no new machinery. A type
variable is a position in an environment of families. A bound is semantic
inclusion between families. The quantifier is the intersection over admissible
instantiations, and it is admissible whenever its instances are, so a quantified
type is a type in exactly the same sense as everything else.

One thing is worth noticing. `allT` quantifies over **all** of `Fam` in order to
build an element of `Fam`. In a set-theoretic development that impredicativity
costs a universe bump or a domain construction; here `Prop` is impredicative and
it simply typechecks.

The quantifier is also not cosmetic: `allT_ref_empty` shows `∀X. ref X` is empty,
because one world fixes one contract and no cell can be a reference to every
type at once.

What is **not** here is the fundamental theorem -- that one runtime function is
safe under every admissible instantiation -- nor variance, nor any connection to
a type syntax. This file settles definability, and nothing beyond it.
-/

namespace Verification
namespace ExperimentState

/-- `∀X. τ(X)`: the intersection over admissible instantiations. -/
def allT (τ : Fam → Fam) : Fam := fun k W v => ∀ F : Fam, Adm F → τ F k W v

/-- `∀X ≤ B. τ(X)`. A bound is an inclusion between families; nothing else is
needed to state one. -/
def allBT (B : Fam) (τ : Fam → Fam) : Fam := fun k W v =>
  ∀ F : Fam, Adm F → (∀ j (U : WorldT j) u, F j U u → B j U u) → τ F k W v

theorem allT_adm (τ : Fam → Fam) (h : ∀ F, Adm F → Adm (τ F)) : Adm (allT τ) :=
  ⟨fun n W v hv F hF => (h F hF).down n W v (hv F hF),
   fun n W W' hx v hv F hF => (h F hF).mono n W W' hx v (hv F hF)⟩

theorem allBT_adm (B : Fam) (τ : Fam → Fam) (h : ∀ F, Adm F → Adm (τ F)) :
    Adm (allBT B τ) :=
  ⟨fun n W v hv F hF hb => (h F hF).down n W v (hv F hF hb),
   fun n W W' hx v hv F hF hb => (h F hF).mono n W W' hx v (hv F hF hb)⟩

/-- Not vacuous. -/
theorem allT_inhabited (n : Nat) (W : WorldT n) : allT (fun _ => nulT) n W .nul :=
  fun _ _ => rfl

/-- And not trivial. A single cell cannot be a `ref X` for every `X`, because one
world fixes one contract, so the quantifier really does bite. -/
theorem allT_ref_empty (n : Nat) (W : WorldT (n + 1)) (v : Val) :
    ¬ allT (fun F => refT F) (n + 1) W v := by
  intro h
  obtain ⟨l, c, rfl, hl, hag⟩ := h nulT nulT_adm
  obtain ⟨l', c', hv', hl', hag'⟩ := h boolT boolT_adm
  cases hv'
  rw [hl] at hl'
  cases hl'
  have h1 := (hag n (by omega) (trunc n (Nat.le_succ n) W) .nul).mpr rfl
  exact absurd ((hag' n (by omega) (trunc n (Nat.le_succ n) W) .nul).mp h1)
    (by simp [boolT])

end ExperimentState
end Verification
