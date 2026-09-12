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

/-- Overload intersection preserves one descriptor, even when signatures
admit different actual counts. -/
theorem calls_append (L M : List (List Fam × Fam)) (n : Nat) (W : WorldT n) (v : Val) :
    callsT (L ++ M) n W v ↔ interT (callsT L) (callsT M) n W v := by
  constructor
  · rintro ⟨arity, body, loc, he, hc, hs⟩
    exact ⟨⟨arity, body, loc, he, hc, fun p hp => hs p (List.mem_append_left M hp)⟩,
      ⟨arity, body, loc, he, hc, fun p hp => hs p (List.mem_append_right L hp)⟩⟩
  · rintro ⟨⟨arity, body, loc, rfl, hc, hs⟩, ⟨arity', body', loc', he, _, ht⟩⟩
    cases he
    refine ⟨arity, body, loc, rfl, hc, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hs p hp
    · exact ht p hp

theorem overload_append (L M : List (Fam × Fam)) (n : Nat) (W : WorldT n) (v : Val) :
    arrowsT (L ++ M) n W v ↔ interT (arrowsT L) (arrowsT M) n W v := by
  simpa only [interT, ← arrowsT_callsT, ← List.map_append] using
    calls_append (L.map fun p => ([p.1], p.2)) (M.map fun p => ([p.1], p.2)) n W v

#print axioms calls_append
#print axioms overload_append
end Verification.ExperimentState.TypeAlgebra
