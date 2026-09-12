import Verification.ExperimentState.ReferenceConjunctions
import Verification.ExperimentState.CallableObjects

/-! Nonempty bag conjunctions and overloads on one callable value. Invariant
operands remain separate, including at budget zero; normalization must not
replace incompatible operands by bottom. -/
namespace Verification.ExperimentState.CallableConjunctions

def propsT (A : Fam) (Bs : List Fam) : Fam := fun n W v =>
  bagT A n W v ∧ ∀ B ∈ Bs, bagT B n W v

def objectsT (A : Fam) (Bs : List Fam) (L : List (List Fam × Fam)) : Fam :=
  interT (propsT A Bs) (callsT L)

theorem props_merge (A C : Fam) (Bs Ds : List Fam) (n W v) :
    propsT A (Bs ++ C :: Ds) n W v ↔ interT (propsT A Bs) (propsT C Ds) n W v := by
  simp only [propsT, List.mem_append, List.mem_cons, or_imp, forall_and, interT, forall_eq]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩; exact ⟨⟨ha,hb⟩,hc,hd⟩
  · rintro ⟨⟨ha,hb⟩,hc,hd⟩; exact ⟨ha,hb,hc,hd⟩

/-- A callability-neutral bag needs no new clause: plain bags and callable
bags with no invocation promises cover exactly the scoped bag values. -/
theorem neutral_iff (A : Fam) (Bs : List Fam) (n W v) :
    unionT (ReferenceConjunctions.refsT A Bs) (objectsT A Bs []) n W v ↔
      propsT A Bs n W v ∧ Scoped 0 v := by
  constructor
  · intro h
    rcases h with h | h
    · refine ⟨⟨refT_bag h.1, fun B hb => refT_bag (h.2 B hb)⟩, ?_⟩
      obtain ⟨l,c,rfl,_,_⟩ := h.1
      trivial
    · exact ⟨h.1,(callsT_callable h.2).scoped⟩
  · rintro ⟨h,hs⟩
    obtain ⟨l,code,rfl,_,hr⟩ := h.1
    cases code with
    | absent =>
      left
      refine ⟨hr,?_⟩
      intro B hb
      obtain ⟨l',code,he,_,hr⟩ := h.2 B hb
      cases he
      exact hr
    | closure arity b =>
      right
      exact ⟨h,arity,b,l,rfl,(by simpa [Scoped] using hs),by simp⟩

theorem merge (A C : Fam) (Bs Ds : List Fam) (L M : List (List Fam × Fam)) (n W v) :
    objectsT A (Bs ++ C :: Ds) (L ++ M) n W v ↔
      interT (objectsT A Bs L) (objectsT C Ds M) n W v := by
  simp only [objectsT, interT, props_merge, TypeAlgebra.calls_append]
  exact ⟨fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩,
    fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩⟩

theorem calls_merge (A : Fam) (Bs : List Fam) (L M : List (List Fam × Fam)) (n W v) :
    objectsT A Bs (L ++ M) n W v ↔ interT (objectsT A Bs L) (callsT M) n W v := by
  simp only [objectsT, interT, TypeAlgebra.calls_append]
  exact and_assoc.symm

theorem adm (A : Fam) (Bs : List Fam) (L : List (List Fam × Fam)) : Adm (objectsT A Bs L) := by
  apply interT_adm _ _ _ (callsT_adm L)
  constructor
  · intro n W v h
    exact ⟨(bagT_adm A).down n W v h.1,fun B hb => (bagT_adm B).down n W v (h.2 B hb)⟩
  · intro n W U hx v h
    exact ⟨(bagT_adm A).mono n W U hx v h.1,fun B hb => (bagT_adm B).mono n W U hx v (h.2 B hb)⟩

theorem congr_below {α : Type} (X Y : α → Fam) (a : α) (bs : List α) (L : List (List α × α))
    (n : Nat) (h : ∀ a, Agree (X a) (Y a) n) (W : WorldT n) (v : Val) :
    objectsT (X a) (bs.map X) (L.map fun p => (p.1.map X,X p.2)) n W v ↔
      objectsT (Y a) (bs.map Y) (L.map fun p => (p.1.map Y,Y p.2)) n W v := by
  simp only [objectsT, interT]
  have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
    intro As; induction As with
    | nil => exact .nil
    | cons a As ih => exact .cons (h a) ih
  apply and_congr _ (callsT_congr L _ _ (fun p _ => ⟨hd p.1,h p.2⟩) W v)
  simp only [propsT,List.forall_mem_map]
  apply and_congr (bagT_contractive n _ _ (h a) W v)
  constructor <;> intro hb b hm
  · exact (bagT_contractive n _ _ (h b) W v).mp (hb b hm)
  · exact (bagT_contractive n _ _ (h b) W v).mpr (hb b hm)

#print axioms neutral_iff
#print axioms merge
#print axioms adm
#print axioms congr_below
end Verification.ExperimentState.CallableConjunctions
