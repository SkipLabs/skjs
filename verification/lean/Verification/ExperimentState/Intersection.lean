import Verification.ExperimentState.Rules

/-!
# Intersections: what the model refuses to validate

Unions turned out to need *fewer* laws here than in a pure language, and that is
what let a clause-to-clause rule be complete (`Union.lean`). This file asks the
same question of intersections, and finds the same answer in a sharper form: the
classical arrow decomposition of semantic subtyping is **unsound** in this model.

The law at issue is the one every treatment of overloaded function types has:

    (A → B) ∧ (A → C)  ≤  A → (B ∧ C)

It is valid set-theoretically, and it is an instance of the Frisch–Castagna–
Benzaken decomposition. `arrow_inter_codomain_fails` shows it fails here.

The reason is allocation. A cell carries one invariant, chosen when it is
allocated, so a function that allocates and returns the cell inhabits `A → ref X`
for *several* different `X` — each membership picking a different contract — while
the intersection of those codomains is empty, since a location belongs to `ref X`
only when its contract *equals* `⟦X⟧`. So the intersection of the two arrow types
contains a function that returns, and the arrow into the intersected codomain
contains only functions that do not.

The failure is not blanket, which is the delicate part. With value-determined
codomains — `null` and `bool` rather than references — the law holds, because
execution is deterministic: one returned value cannot be both a null and a
boolean, so a function in both arrow types never returns on that domain and does
inhabit the arrow into the empty intersection. The law fails exactly where
codomain membership depends on the world. A complete rule for intersections has
to see that distinction, which the classical theory has no vocabulary for.
-/

namespace Verification
namespace ExperimentState
namespace Intersection

/-- Allocate a fresh cell holding null, and return it. -/
def allocFn : Tm := .lam (.alloc .nul)

/-- The function inhabits `A → ref B` for *every* admissible `B` that contains
null: the contract of the new cell is chosen by the membership proof, not by the
program. -/
theorem allocFn_typed {A B : Fam} (hAv : ValOnly A) (hB : Adm B)
    (hnul : ∀ (j : Nat) (W : WorldT j), B j W .nul) (k : Nat) (W : WorldT k) :
    arrowT A (refT B) k W allocFn := by
  apply lam_intro hAv
  intro p hp U hx hu h hh a ha
  simpa [subst] using
    alloc_rule hB p (trunc p (Nat.le_succ p) U) h .nul rfl
      (WorldAdm_trunc _ hu) (HeapOk_trunc p U h hh) (hnul _ _)

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
    allocFn_typed nulT_valOnly nulT_adm (fun _ _ => rfl) 4 _
  have h2 : arrowT nulT (refT (unionT nulT boolT)) 4 (ofList []) allocFn :=
    allocFn_typed nulT_valOnly (unionT_adm nulT boolT nulT_adm boolT_adm)
      (fun _ _ => Or.inl rfl) 4 _
  have hb := hrule _ _ _ 4 (ofList []) allocFn h1 h2
  have hx : WExt (trunc 3 (by omega) (ofList ([] : List (Ctr 4)))) (ofList []) := by
    rw [trunc_empty]
    exact WExt_refl _
  have hsafe := hb.2 3 (by omega) (ofList []) hx (emptyWorld_adm 3) []
    (emptyHeapOk 3) .nul rfl
  -- beta
  rcases hsafe with ⟨hv, -⟩ | ⟨Z, h1', t1, hz, huz, hst1, hok1, hs1⟩
  · simp [isVal] at hv
  obtain ⟨he1, rfl⟩ := beta_inv (show isVal Tm.nul = true from rfl) hst1
  subst he1
  -- the allocation
  rcases hs1 with ⟨hv, -⟩ | ⟨Q, h2', t2, hq, huq, hst2, hok2, hs2⟩
  · simp [isVal, subst] at hv
  obtain ⟨he2, rfl⟩ := alloc_step_inv (show isVal Tm.nul = true from rfl) hst2
  subst he2
  -- a location is a value, and it would have to inhabit an empty codomain
  rcases hs2 with ⟨-, hmem⟩ | ⟨_, _, _, _, _, hst3, _, _⟩
  · exact ref_inter_empty 1 (by omega) Q _ hmem
  · exact value_no_step (show isVal (Tm.loc _) = true from rfl) hst3

/-! ## The other half: where the law does hold

The failure above is not blanket. When membership in the codomain depends on the
value alone — an atom rather than a reference — two runs of the same program can
be compared, because evaluation is deterministic and the two judgments about the
result are world-free. Then a function in both arrows never returns on that
domain, and so inhabits the arrow into their empty intersection. The law is
therefore sensitive to *why* a value belongs to a type, which is a distinction
the classical decomposition does not have. -/

/-- A family that constrains the value and nothing else. -/
def Rigid (A : Fam) (P : Val → Prop) : Prop :=
  ∀ (j : Nat) (W : WorldT j) (v : Val), A j W v ↔ P v

theorem nulT_rigid : Rigid nulT (fun v => v = .nul) := fun _ _ _ => Iff.rfl

theorem boolT_rigid : Rigid boolT (fun v => v = .tru ∨ v = .fls) := fun _ _ _ => Iff.rfl

/-- **Two runs, one program.** A term safe at two rigid families is safe at their
intersection. Determinism is what makes this work: the two runs take the same
steps, so if either reaches a value it is the *same* value, and rigidity carries
the two judgments about it into one world. -/
theorem safe_rigid_inter {A B : Fam} {P Q : Val → Prop}
    (hA : Rigid A P) (hB : Rigid B Q) :
    ∀ (n : Nat) (W W' : WorldT n) (h : Heap) (t : Tm),
      Safe A n W h t → Safe B n W' h t → Safe (interT A B) n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _; trivial
  | succ p ih =>
    rintro W W' h t (⟨hv1, hAv⟩ | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩)
      (⟨hv2, hBv⟩ | ⟨Z', h2, t2, -, -, hst2, -, hcont2⟩)
    · exact Or.inl ⟨hv1, hAv, (hB (p + 1) W t).mpr ((hB (p + 1) W' t).mp hBv)⟩
    · exact absurd hst2 (value_no_step hv1)
    · exact absurd hst1 (value_no_step hv2)
    · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
      exact Or.inr ⟨Z, h1, t1, hz, huz, hst1, hok1, ih Z Z' h1 t1 hcont1 hcont2⟩

/-- **The law holds for rigid codomains.** This is the exact converse of
`arrow_inter_codomain_fails`: what breaks the law is not intersection, it is a
codomain whose membership depends on the world. -/
theorem arrow_inter_rigid_codomain {A B C : Fam} {P Q : Val → Prop}
    (hB : Rigid B P) (hC : Rigid C Q) (k : Nat) (W : WorldT k) (v : Val)
    (h1 : arrowT A B k W v) (h2 : arrowT A C k W v) :
    arrowT A (interT B C) k W v := by
  refine ⟨h1.1, ?_⟩
  intro j hj W' hx hu h hh a ha
  exact safe_rigid_inter hB hC j W' W' h _
    (h1.2 j hj W' hx hu h hh a ha) (h2.2 j hj W' hx hu h hh a ha)

/-- The concrete reading: a function that returns a null and returns a boolean on
the same domain returns nothing at all there. -/
theorem arrow_inter_nul_bool {A : Fam} (k : Nat) (W : WorldT k) (v : Val)
    (h1 : arrowT A nulT k W v) (h2 : arrowT A boolT k W v) :
    arrowT A (interT nulT boolT) k W v :=
  arrow_inter_rigid_codomain nulT_rigid boolT_rigid k W v h1 h2

/-! ## What does survive

The failure is specific to *intersecting* codomains. Combining two arrows over
the union of their domains is sound, and so is the simple clause rule that picks
one conjunct. So the part of the classical decomposition this model rejects is
narrow, and worth locating exactly before a rule is designed. -/

/-- **Two arrows cover the union of their domains.** -/
theorem arrow_inter_dom_union {A B C D : Fam} (k : Nat) (W : WorldT k) (v : Val)
    (h1 : arrowT A B k W v) (h2 : arrowT C D k W v) :
    arrowT (unionT A C) (unionT B D) k W v := by
  refine ⟨h1.1, ?_⟩
  intro j hj W' hx hu h hh a ha
  rcases ha with haA | haC
  · exact Safe_mono j (fun _ _ _ _ hb => Or.inl hb) W' h _ (h1.2 j hj W' hx hu h hh a haA)
  · exact Safe_mono j (fun _ _ _ _ hd => Or.inr hd) W' h _ (h2.2 j hj W' hx hu h hh a haC)

/-- **One conjunct suffices.** The clause rule that matches a source arrow
against a single target arrow is sound for intersections too. -/
theorem arrow_inter_clause {A B C D : Fam} (k : Nat) (W : WorldT k) (v : Val)
    (hdom : ∀ (j : Nat) (W' : WorldT j) (u : Val), C j W' u → A j W' u)
    (hcod : ∀ (j : Nat) (W' : WorldT j) (u : Val), B j W' u → D j W' u)
    (h1 : arrowT A B k W v) : arrowT C D k W v := by
  refine ⟨h1.1, ?_⟩
  intro j hj W' hx hu h hh a ha
  exact Safe_mono j (fun m _ U u hb => hcod m U u hb) W' h _
    (h1.2 j hj W' hx hu h hh a (hdom j W' a ha))

end Intersection
end ExperimentState
end Verification
