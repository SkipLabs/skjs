import Verification.ExperimentState.Rules

/-! Regression proofs constraining the current rules: allocation forbids
unrestricted arrow-result distribution, and finite observation depth forbids
collapsing all ultimately incompatible reference results to bottom. -/
namespace Verification.ExperimentState.ModelBoundaries

/-- Allocate a fresh cell holding null, and return it. -/
def allocFn : Tm := .fn 0 (.alloc .nul)

/-- The function inhabits `A → ref B` for *every* admissible `B` that contains
null: the contract of the new cell is chosen by the membership proof, not by the
program. -/
theorem allocFn_typed {A B : Fam} (hB : Adm B)
    (hnul : ∀ (j : Nat) (W : WorldT j), B j W .nul) (k : Nat) (W : WorldT k) :
    arrowT A (refT B) k W allocFn := by
  apply fn_intro _ _ _ (by trivial)
  intro p hp U hx hu h hh a ha
  simpa [subst] using
    alloc_rule hB p U h .nul rfl hu hh (hnul _ _)

/-- Two references whose operands differ have an empty intersection: a location
belongs to `ref X` only when the world's contract for it *equals* `⟦X⟧`, and one
cell has one contract. -/
theorem ref_inter_empty (j : Nat) (hj : 0 < j) (W : WorldT j) (u : Val) :
    ¬ interT (refT nulT) (refT (unionT nulT boolT)) j W u := by
  rintro ⟨⟨l, c, he, hl, hc⟩, ⟨l', c', he', hl', hc'⟩⟩
  subst he
  cases he'
  rw [hl] at hl'
  cases hl'
  have h1 := (hc' 0 hj (ofList []) .tru).mpr (Or.inr (Or.inl rfl))
  exact absurd ((hc 0 hj (ofList []) .tru).mp h1) (by simp [nulT])

theorem trunc_empty {k j : Nat} (h : j ≤ k) :
    trunc j h (ofList ([] : List (Ctr k))) = ofList [] := by
  simp [trunc, toList_ofList]

theorem emptyWorld_adm (k : Nat) : WorldAdm (ofList ([] : List (Ctr k))) := by
  intro l c hl
  simp [lookup] at hl

/-- **The classical arrow decomposition is unsound here.** No rule may conclude
`arrowT A (B ∧ C)` from `arrowT A B` and `arrowT A C`. -/
theorem arrow_inter_codomain_fails :
    ¬ ∀ (A B C : Fam) (k : Nat) (W : WorldT k) (v : Val),
        arrowT A B k W v → arrowT A C k W v → arrowT A (interT B C) k W v := by
  intro hrule
  have h1 : arrowT nulT (refT nulT) 4 (ofList []) allocFn :=
    allocFn_typed nulT_adm (fun _ _ => rfl) 4 _
  have h2 : arrowT nulT (refT (unionT nulT boolT)) 4 (ofList []) allocFn :=
    allocFn_typed (unionT_adm nulT boolT nulT_adm boolT_adm)
      (fun _ _ => Or.inl rfl) 4 _
  have hb := hrule _ _ _ 4 (ofList []) allocFn h1 h2
  have hx : WExt (trunc 3 (by omega) (ofList ([] : List (Ctr 4)))) (ofList []) := by
    rw [trunc_empty]
    exact WExt_refl _
  have hsafe := hb.2 3 (by omega) (ofList []) hx (emptyWorld_adm 3) []
    (emptyHeapOk 3) .nul rfl
  change Safe (interT (refT nulT) (refT (unionT nulT boolT))) 3 (ofList []) [] (.alloc .nul) at hsafe
  have hs1 := hsafe
  -- the allocation
  rcases hs1 with ⟨hv, -⟩ | ⟨Q, h2', t2, hq, huq, hst2, hok2, hs2⟩
  · simp [isVal] at hv
  obtain ⟨he2, rfl⟩ := alloc_step_inv (show isVal Tm.nul = true from rfl) hst2
  subst he2
  -- a location is a value, and it would have to inhabit an empty codomain
  rcases hs2 with ⟨-, hmem⟩ | ⟨_, _, _, _, _, hst3, _, _⟩
  · exact ref_inter_empty 2 (by omega) Q _ hmem
  · exact value_no_step (show isVal (Tm.obj _ .absent) = true from rfl) hst3

/-! ## Finite observation of nested references -/

def nestedRef : Nat → Fam → Fam
  | 0, A => A
  | d + 1, A => refT (nestedRef d A)

theorem nested_agrees_cycle (d : Nat) (A : Fam) :
    ∀ n, n < d → ∀ W v, nestedRef d A n W v ↔ R n W v := by
  induction d with
  | zero => intro n hn; omega
  | succ d ih =>
    intro n hn W v
    rw [R_unfold]
    exact refT_contractive n _ _ (fun j hj U u => ih j (by omega) U u) W v


def bottomT : Fam := fun _ _ _ => False

/-- A constant body returns a location before two reference levels can be
observed. Distinct eventual contracts remain indistinguishable at these budgets. -/
theorem constant_nested_arrow (A : Fam) :
    arrowT nulT (nestedRef 2 A) 2 (ofList [res R]) (.fn 0 (.obj 0 .absent)) := by
  apply fn_intro _ _ _ (by trivial)
  intro p hp U hx hu h hh a ha
  have hr : R p U (.obj 0 .absent) := R_adm.mono p _ U hx _
    (R_adm.down_le 2 p (Nat.le_of_lt hp) _ _ (R_cyclic 2))
  exact value_safe _ p U h (.obj 0 .absent) rfl ((nested_agrees_cycle 2 A p hp U _).mpr hr)

theorem constant_not_bottom :
    ¬ arrowT nulT bottomT 2 (ofList [res R]) (.fn 0 (.obj 0 .absent)) := by
  intro ht
  have hx : WExt (trunc 1 (by omega) (ofList [res R] : WorldT 2))
      (ofList [res R] : WorldT 1) := by
    rw [trunc_res]
    exact WExt_refl _
  have hs := ht.2 1 (by omega) _ hx (cyclic_world_adm 1)
    [.obj 0 .absent] (cyclic_heap_ok 1) .nul rfl
  exact safe_value_mem (show isVal (Tm.obj 0 .absent) = true from rfl) hs

/-- It is UNSOUND to extrapolate the single-reference empty-result rule to
arbitrary reference nesting in the exact indexed interpretation. This is a
finite-budget counterexample in an admissible world with a satisfying heap. -/
theorem deeper_reference_rule_fails : ¬ (∀ n W v,
    arrowT nulT (nestedRef 2 nulT) n W v →
    arrowT nulT (nestedRef 2 boolT) n W v → arrowT nulT bottomT n W v) := by
  intro hr
  exact constant_not_bottom (hr 2 _ _ (constant_nested_arrow nulT) (constant_nested_arrow boolT))


#print axioms arrow_inter_codomain_fails
#print axioms deeper_reference_rule_fails
end Verification.ExperimentState.ModelBoundaries
