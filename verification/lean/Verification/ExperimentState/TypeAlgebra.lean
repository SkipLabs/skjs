import Verification.ExperimentState.Rules
import Verification.ExperimentState.Tower

/-! Local semantic equations used in positive normalization. Reference conjunctions
are handled by ReferenceConjunctions; finite graph normalization is implemented
and proved in PositiveNormalization and PositiveGraphs. The arrow-domain union
equation is arrowT_union_dom in Safety, rather than a duplicate proof here. -/
namespace Verification.ExperimentState.TypeAlgebra

theorem inter_union (A B C : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    interT A (unionT B C) n W v ↔ unionT (interT A B) (interT A C) n W v := by
  exact and_or_left

theorem inter_comm (A B : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    interT A B n W v ↔ interT B A n W v := and_comm

theorem inter_assoc (A B C : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    interT (interT A B) C n W v ↔ interT A (interT B C) n W v := and_assoc

theorem inter_idemp (A : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    interT A A n W v ↔ A n W v := ⟨And.left, fun h => ⟨h, h⟩⟩

theorem overload_append (L M : List (Fam × Fam)) (n : Nat) (W : WorldT n) (v : Val) :
    arrowsT (L ++ M) n W v ↔ interT (arrowsT L) (arrowsT M) n W v := by
  constructor
  · rintro ⟨hl, hp⟩
    exact ⟨⟨hl, fun p hm => hp p (List.mem_append_left M hm)⟩,
      ⟨hl, fun p hm => hp p (List.mem_append_right L hm)⟩⟩
  · rintro ⟨⟨hl, hp⟩, ⟨_, hq⟩⟩
    refine ⟨hl, ?_⟩
    intro p hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hp p hm
    · exact hq p hm

#print axioms overload_append
end Verification.ExperimentState.TypeAlgebra
