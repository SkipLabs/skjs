import Verification.ExperimentState.ReferenceConjunctions
import Verification.ExperimentState.CallableObjects

/-! Nonempty bag conjunctions and overloads on one callable value. Invariant
operands remain separate, including at budget zero; normalization must not
replace incompatible operands by bottom. -/
namespace Verification.ExperimentState.CallableConjunctions

def propsT (A : Fam) (Bs : List Fam) : Fam := fun n W v =>
  bagT A n W v ∧ ∀ B ∈ Bs, bagT B n W v

def objectsT (A : Fam) (Bs : List Fam) (L : List (Fam × Fam)) : Fam :=
  interT (propsT A Bs) (arrowsT L)

theorem props_merge (A C : Fam) (Bs Ds : List Fam) (n W v) :
    propsT A (Bs ++ C :: Ds) n W v ↔ interT (propsT A Bs) (propsT C Ds) n W v := by
  simp only [propsT, List.mem_append, List.mem_cons, or_imp, forall_and, interT, forall_eq]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩; exact ⟨⟨ha,hb⟩,hc,hd⟩
  · rintro ⟨⟨ha,hb⟩,hc,hd⟩; exact ⟨ha,hb,hc,hd⟩

theorem merge (A C : Fam) (Bs Ds : List Fam) (L M : List (Fam × Fam)) (n W v) :
    objectsT A (Bs ++ C :: Ds) (L ++ M) n W v ↔
      interT (objectsT A Bs L) (objectsT C Ds M) n W v := by
  simp only [objectsT, interT, props_merge, TypeAlgebra.overload_append]
  exact ⟨fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩,
    fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩⟩

theorem calls_merge (A : Fam) (Bs : List Fam) (L M : List (Fam × Fam)) (n W v) :
    objectsT A Bs (L ++ M) n W v ↔ interT (objectsT A Bs L) (arrowsT M) n W v := by
  simp only [objectsT, interT, TypeAlgebra.overload_append]
  exact and_assoc.symm

theorem adm (A : Fam) (Bs : List Fam) (L : List (Fam × Fam)) : Adm (objectsT A Bs L) := by
  apply interT_adm _ _ _ (arrowsT_adm L)
  constructor
  · intro n W v h
    exact ⟨(bagT_adm A).down n W v h.1,fun B hb => (bagT_adm B).down n W v (h.2 B hb)⟩
  · intro n W U hx v h
    exact ⟨(bagT_adm A).mono n W U hx v h.1,fun B hb => (bagT_adm B).mono n W U hx v (h.2 B hb)⟩

theorem congr_below {α : Type} (X Y : α → Fam) (a : α) (bs : List α) (L : List (α × α))
    (n : Nat) (h : ∀ a, Agree (X a) (Y a) n) (W : WorldT n) (v : Val) :
    objectsT (X a) (bs.map X) (L.map fun p => (X p.1,X p.2)) n W v ↔
      objectsT (Y a) (bs.map Y) (L.map fun p => (Y p.1,Y p.2)) n W v := by
  simp only [objectsT, interT]
  apply and_congr _ (arrowsT_congr L _ _ (fun p _ => ⟨h p.1,h p.2⟩) W v)
  simp only [propsT,List.forall_mem_map]
  apply and_congr (bagT_contractive n _ _ (h a) W v)
  constructor <;> intro hb b hm
  · exact (bagT_contractive n _ _ (h b) W v).mp (hb b hm)
  · exact (bagT_contractive n _ _ (h b) W v).mpr (hb b hm)

#print axioms merge
#print axioms adm
#print axioms congr_below
end Verification.ExperimentState.CallableConjunctions
