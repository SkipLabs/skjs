import Verification.Types.ReferenceConjunctions
import Verification.Programs.CallableObjects
import Verification.Semantics.CallEffects

/-! Nonempty bag conjunctions and overloads on one callable value. Invariant
operands remain separate, including at budget zero; normalization must not
replace incompatible operands by bottom. -/
namespace Verification.CallableConjunctions
open CallEffects

def propsT (A : Fields) (Bs : List Fields) : Fam := fun n W v =>
  bagT A n W v ∧ ∀ B ∈ Bs, bagT B n W v

def objectsT (Ξ : Fam) (A : Fields) (Bs : List Fields) (L : List (Arrow Fam)) : Fam :=
  interT (propsT A Bs) (CallEffects.callsT Ξ L)

theorem props_merge (A C : Fields) (Bs Ds : List Fields) (n W v) :
    propsT A (Bs ++ C :: Ds) n W v ↔ interT (propsT A Bs) (propsT C Ds) n W v := by
  simp only [propsT, List.mem_append, List.mem_cons, or_imp, forall_and, interT, forall_eq]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩; exact ⟨⟨ha,hb⟩,hc,hd⟩
  · rintro ⟨⟨ha,hb⟩,hc,hd⟩; exact ⟨ha,hb,hc,hd⟩

theorem merge (A C : Fields) (Bs Ds : List Fields) (L M : List (Arrow Fam)) (n W v) :
    objectsT Ξ A (Bs ++ C :: Ds) (L ++ M) n W v ↔
      interT (objectsT Ξ A Bs L) (objectsT Ξ C Ds M) n W v := by
  simp only [objectsT, interT, props_merge, CallEffects.callsT_append]
  exact ⟨fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩,
    fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩⟩

theorem calls_merge (A : Fields) (Bs : List Fields) (L M : List (Arrow Fam)) (n W v) :
    objectsT Ξ A Bs (L ++ M) n W v ↔ interT (objectsT Ξ A Bs L) (CallEffects.callsT Ξ M) n W v := by
  simp only [objectsT, interT, CallEffects.callsT_append]
  exact and_assoc.symm

theorem adm (A : Fields) (Bs : List Fields) (L : List (Arrow Fam)) : Adm (objectsT Ξ A Bs L) := by
  apply interT_adm _ _ _ (CallEffects.callsT_adm L)
  constructor
  · intro n W v h
    exact ⟨(bagT_adm A).down n W v h.1,fun B hb => (bagT_adm B).down n W v (h.2 B hb)⟩
  · intro n W U hx v h
    exact ⟨(bagT_adm A).mono n W U hx v h.1,fun B hb => (bagT_adm B).mono n W U hx v (h.2 B hb)⟩

theorem congr_below {Ξ Ξ' : Fam} {α : Type} (X Y : α → Fam) (a : List (PropKey × α))
    (bs : List (List (PropKey × α))) (L : List (Arrow α))
    (n : Nat) (hexc : Agree Ξ Ξ' n) (h : ∀ a, Agree (X a) (Y a) n) (W : WorldT n) (v : Val) :
    objectsT Ξ (ReferenceConjunctions.famsOf X a) (bs.map (ReferenceConjunctions.famsOf X))
        (L.map (Arrow.map X)) n W v ↔
      objectsT Ξ' (ReferenceConjunctions.famsOf Y a) (bs.map (ReferenceConjunctions.famsOf Y))
        (L.map (Arrow.map Y)) n W v := by
  simp only [objectsT, interT]
  have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
    intro As; induction As with
    | nil => exact .nil
    | cons a As ih => exact .cons (h a) ih
  apply and_congr _ (CallEffects.callsT_congr L (Arrow.map X) (Arrow.map Y) hexc (fun _ _ => rfl)
    (fun p _ => ⟨h p.receiver, hd p.arguments, h p.result⟩) W v)
  simp only [propsT,List.forall_mem_map]
  apply and_congr (bagT_contractive X Y a n h W v)
  constructor <;> intro hb b hm
  · exact (bagT_contractive X Y b n h W v).mp (hb b hm)
  · exact (bagT_contractive X Y b n h W v).mpr (hb b hm)

/-- A callability-neutral bag needs no new clause: plain bags and callable
bags with no invocation promises cover exactly the scoped bag values whose code,
if any, has `[[Call]]`. A class constructor's has only `[[Construct]]`, so a
class value is neither. -/
theorem neutral_iff (A : Fields) (Bs : List Fields) (n W v) :
    unionT (ReferenceConjunctions.refsT A Bs) (objectsT Ξ A Bs []) n W v ↔
      propsT A Bs n W v ∧ Scoped 0 v ∧
        ∀ fs c oid, v = .objAt fs c oid → c = .absent ∨ c.callable = true := by
  constructor
  · intro h
    rcases h with h | h
    · refine ⟨⟨recT_bag h.1, fun B hb => recT_bag (h.2 B hb)⟩, ?_, ?_⟩
      · obtain ⟨flds,oid,rfl,_⟩ := h.1
        trivial
      · obtain ⟨flds,oid,rfl,_⟩ := h.1
        intro fs c oid' he
        cases he
        exact .inl rfl
    · refine ⟨h.1,h.2.1.scoped, ?_⟩
      obtain ⟨fs', code, oid', he, hc, -⟩ := h.2.1
      intro fs c oid hv
      rw [hv] at he
      cases he
      exact .inr hc
  · rintro ⟨h,hs,hnc⟩
    obtain ⟨flds,code,oid,rfl,_,hr⟩ := h.1
    rcases hnc flds code oid rfl with rfl | hc
    · left
      refine ⟨hr,?_⟩
      intro B hb
      obtain ⟨flds',code,oid',he,_,hr⟩ := h.2 B hb
      cases he
      exact hr
    · right
      exact ⟨h,⟨flds,_,_,rfl,hc,hs⟩,by simp⟩

#print axioms neutral_iff
#print axioms merge
#print axioms adm
#print axioms congr_below
end Verification.CallableConjunctions
