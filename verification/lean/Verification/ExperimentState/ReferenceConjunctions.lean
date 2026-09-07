import Verification.ExperimentState.TypeAlgebra

/-! A nonempty conjunction of invariant reference contracts. Keeping the first
operand explicit prevents the empty conjunction from silently becoming top. -/
namespace Verification.ExperimentState.ReferenceConjunctions

def refsT (A : Fam) (Bs : List Fam) : Fam := fun n W v =>
  refT A n W v ∧ ∀ B ∈ Bs, refT B n W v

theorem singleton (A : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    refsT A [] n W v ↔ refT A n W v := by simp [refsT]

theorem merge (A C : Fam) (Bs Ds : List Fam) (n : Nat) (W : WorldT n) (v : Val) :
    refsT A (Bs ++ C :: Ds) n W v ↔ interT (refsT A Bs) (refsT C Ds) n W v := by
  simp only [refsT, List.mem_append, List.mem_cons,
    or_imp, forall_and, interT]
  simp only [forall_eq]
  constructor
  · rintro ⟨ha, hb, hc, hd⟩; exact ⟨⟨ha, hb⟩, hc, hd⟩
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩; exact ⟨ha, hb, hc, hd⟩

theorem adm (A : Fam) (Bs : List Fam) : Adm (refsT A Bs) := by
  constructor
  · intro n W v h
    exact ⟨(refT_adm A).down n W v h.1,
      fun B hb => (refT_adm B).down n W v (h.2 B hb)⟩
  · intro n W U hx v h
    exact ⟨(refT_adm A).mono n W U hx v h.1,
      fun B hb => (refT_adm B).mono n W U hx v (h.2 B hb)⟩

theorem congr_below {ι : Type} (X Y : ι → Fam) (a : ι) (bs : List ι) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    refsT (X a) (bs.map X) n W v ↔ refsT (Y a) (bs.map Y) n W v := by
  simp only [refsT, List.forall_mem_map]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨(refT_contractive n _ _ (h a) W v).mp ha,
      fun b hm => (refT_contractive n _ _ (h b) W v).mp (hb b hm)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(refT_contractive n _ _ (h a) W v).mpr ha,
      fun b hm => (refT_contractive n _ _ (h b) W v).mpr (hb b hm)⟩

/-- All constraints describe the same stored contract, so their operands agree
at the budgets at which that contract can be observed. -/
theorem operands_agree {A B : Fam} {Bs : List Fam} {n W v}
    (h : refsT A Bs n W v) (hb : B ∈ Bs) : Agree A B n := by
  obtain ⟨l, c, rfl, hl, ha⟩ := h.1
  obtain ⟨l', c', he, hl', hc⟩ := h.2 B hb
  cases he
  rw [hl] at hl'
  cases hl'
  intro j hj U u
  exact (ha j hj U u).symm.trans (hc j hj U u)

/-- A read satisfies every operand at every available lower budget. -/
theorem read_all {A : Fam} {Bs : List Fam} {n W heap l}
    (hok : HeapOk n W heap) (hr : refsT A Bs n W (.loc l)) :
    ∃ v, heap[l]? = some v ∧ ∀ j (hj : j < n),
      A j (trunc j (Nat.le_of_lt hj) W) v ∧
      ∀ B ∈ Bs, B j (trunc j (Nat.le_of_lt hj) W) v := by
  obtain ⟨k, c, he, hl, hc⟩ := hr.1
  cases he
  obtain ⟨v, hv, hm⟩ := read_sound n W heap l c hok hl
  refine ⟨v, hv, ?_⟩
  intro j hj
  have ha := (hc j hj _ v).mp (hm j hj)
  exact ⟨ha, fun B hb => (operands_agree hr hb j hj _ v).mp ha⟩

/-- Writing a value satisfying even one operand suffices: all operands agree
with the same invariant below this budget. Aliased heap satisfaction survives. -/
theorem write_first {A : Fam} {Bs : List Fam} {n W heap l v}
    (hok : HeapOk n W heap) (hr : refsT A Bs n W (.loc l))
    (hv : ∀ j (hj : j < n), A j (trunc j (Nat.le_of_lt hj) W) v) :
    HeapOk n W (heap.set l v) := by
  obtain ⟨k, c, he, hl, hc⟩ := hr.1
  cases he
  exact write_sound n W heap l c v hok hl (fun j hj => (hc j hj _ v).mpr (hv j hj))

theorem duplicate (A : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    refsT A [A] n W v ↔ refT A n W v := by simp [refsT]

/-- Both constraints on the cyclic reference are inhabited in a satisfying heap. -/
theorem cyclic_inhabited (n : Nat) :
    HeapOk n (ofList [res R]) [.loc 0] ∧
    refsT R [R] n (ofList [res R]) (.loc 0) :=
  ⟨cyclic_heap_ok n, (duplicate R n _ _).mpr ((R_unfold n _ _).mp (R_cyclic n))⟩

/-- Incompatible contracts must remain visible at zero; dropping the entire
conjunction as bottom would not preserve the current indexed interpretation. -/
theorem incompatible_at_zero :
    refsT nulT [boolT] 0 (ofList [res nulT]) (.loc 0) := by
  have hr : ∀ A : Fam, refT A 0 (ofList [res nulT]) (.loc 0) := by
    intro A
    exact ⟨0, res nulT, rfl, by simp [lookup], fun j hj => by omega⟩
  exact ⟨hr nulT, by simpa using hr boolT⟩

theorem incompatible_positive {n : Nat} (hn : 0 < n) (W : WorldT n) (v : Val) :
    ¬ refsT nulT [boolT] n W v := by
  intro h
  have he := operands_agree h (by simp : boolT ∈ [boolT]) 0 hn (ofList []) .nul
  have hb := he.mp rfl
  simp [boolT] at hb

#print axioms read_all
#print axioms cyclic_inhabited
end Verification.ExperimentState.ReferenceConjunctions
