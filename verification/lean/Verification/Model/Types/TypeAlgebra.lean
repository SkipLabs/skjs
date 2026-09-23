import Verification.Model.Semantics.Rules
import Verification.Model.Semantics.Tower

/-! Local semantic equations used in positive normalization. Reference conjunctions
are handled by ReferenceConjunctions; finite graph normalization is implemented
and proved in PositiveNormalization and PositiveGraphs. The arrow-domain union
equation is arrowT_union_dom in Safety, rather than a duplicate proof here. -/
namespace Verification.Model.TypeAlgebra

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
theorem calls_append (L M : List (Fam × List Fam × Fam)) (n : Nat) (W : WorldT n) (v : Val) :
    callsT (L ++ M) n W v ↔ interT (callsT L) (callsT M) n W v := by
  simp only [callsT, interT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem rests_append (S T : List (Fam × List Fam × Fam × Fam)) (n : Nat) (W : WorldT n) (v : Val) :
    restsT (S ++ T) n W v ↔ interT (restsT S) (restsT T) n W v := by
  simp only [restsT, interT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem overload_append (L M : List (Fam × Fam)) (n : Nat) (W : WorldT n) (v : Val) :
    arrowsT (L ++ M) n W v ↔ interT (arrowsT L) (arrowsT M) n W v := by
  simp only [arrowsT, interT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

#print axioms calls_append
#print axioms overload_append
end Verification.Model.TypeAlgebra
