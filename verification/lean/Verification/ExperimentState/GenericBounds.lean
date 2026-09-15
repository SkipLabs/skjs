import Verification.ExperimentState.TypeParams

/-! Finite upper-bound traversal for the source generic-copy fragment.
Every successful traversal constructs a `SubP` derivation; parameters remain
rigid and edges are never followed backwards. Fuel limits completeness only. -/
namespace Verification.ExperimentState.GenericBounds
open TypeParams PositiveGraphs

def follows (bounds : List (Nat × Nat)) : Nat → Nat → Nat → Bool
  | fuel, a, b =>
    if a = b then true else
      match fuel with
      | 0 => false
      | n + 1 => bounds.any fun (p, u) => a == p && follows bounds n u b

theorem follows_sound {G : NormalGraph Nat} {P : Nat → Bool}
    {bounds : List (Nat × Nat)}
    (hp : ∀ e ∈ bounds, P e.1 = true) {fuel a b}
    (h : follows bounds fuel a b = true) :
    SubP G P (bounds.map fun (p, u) => (p, [u])) [a] [b] := by
  induction fuel generalizing a with
  | zero =>
    simp only [follows] at h
    split at h
    · next heq => subst b; exact .subset (by intro i hi; exact hi)
    · contradiction
  | succ n ih =>
    simp only [follows] at h
    split at h
    · next heq => subst b; exact .subset (by intro i hi; exact hi)
    · obtain ⟨⟨p, u⟩, he, ht⟩ := List.any_eq_true.mp h
      have hh : a = p ∧ follows bounds n u b = true := by simpa using ht
      have eq : a = p := hh.1
      subst a
      exact .trans (.hyp (List.mem_map.mpr ⟨(p, u), he, rfl⟩) (hp (p, u) he))
        (ih hh.2)

#print axioms follows_sound
end Verification.ExperimentState.GenericBounds
