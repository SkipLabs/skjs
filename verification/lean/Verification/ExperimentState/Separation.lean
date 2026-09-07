import Verification.ExperimentState.Completeness

/-!
Equality completeness for closed guarded regular types in the existing stateful
model. No changes to that model and no additional type or term constructors.

The canonical world contains one invariant cell for each graph node. A separating
value is a term closed with respect to variables (it may capture those locations).
It belongs to one type at every budget and in every world extending the canonical
world. Above a finite threshold it fails the other type in every admissible,
inhabited extension. Requiring inhabited extensions on the negative side is
essential: a future world with an empty contract can make arrow obligations
vacuous. `graphHeap_ok` supplies actual initial heaps.

References compare contracts; arrow arguments are tested by writing to an
invariant cell then diverging; arrow results are tested by returning an existing
separator. Thus complements of separability form a bisimulation. This proves
`semantic_eq_iff` without postulating injectivity on arbitrary semantic families.

The result is about indexed family equality, not contextual equivalence: a
contract-violating write can separate types even if the term never gets stuck.
-/

namespace Verification.ExperimentState.Completeness

def Over (G : Graph (Fin m)) (n : Nat) (U : WorldT n) := WExt (graphWorld G n) U

theorem over_trunc {G : Graph (Fin m)} {n j : Nat} {U : WorldT n}
    (hx : Over G n U) (hj : j ≤ n) : Over G j (trunc j hj U) := by
  have ht := WExt_trunc hj hx
  rwa [graphWorld_trunc] at ht

theorem over_ext {G : Graph (Fin m)} {n : Nat} {U V : WorldT n}
    (hx : Over G n U) (hy : WExt U V) : Over G n V := WExt_trans hx hy

def Sep (G : Graph (Fin m)) (i j : Fin m) : Prop :=
  ∃ v N, Closed v ∧
    (∀ n U, Over G n U → denote G i n U v) ∧
    (∀ n, N ≤ n → ∀ U h, Over G n U → WorldAdm U → HeapOk n U h → ¬ denote G j n U v)

def Apart (G : Graph (Fin m)) (i j : Fin m) := Sep G i j ∨ Sep G j i

theorem sep_ne {G : Graph (Fin m)} {i j} (hs : Sep G i j) : ¬ FamEq (denote G i) (denote G j) := by
  rintro he
  obtain ⟨v, N, _, hp, hn⟩ := hs
  exact hn N (Nat.le_refl N) _ _ (WExt_refl _) (graphWorld_adm G N) (graphHeap_ok G N)
    ((he N _ v).mp (hp N _ (WExt_refl _)))

theorem canonical_closed (G : Graph (Fin m)) (i : Fin m) : Closed (canonical G i) := by
  intro k a
  unfold canonical
  cases G i <;> simp [subst, omegaTm, delta]

theorem canonical_over (G : Graph (Fin m)) (i : Fin m) (n : Nat) (U : WorldT n)
    (hx : Over G n U) : denote G i n U (canonical G i) :=
  (denote_adm G i).mono n _ U hx _ (canonical_mem G i n)

theorem different_heads {G : Graph (Fin m)} {i j} (hd : head (G i) ≠ head (G j)) : Sep G i j := by
  refine ⟨canonical G i, 0, canonical_closed G i, canonical_over G i, ?_⟩
  intro n hn U h hx hu hh hv
  have hv' := (denote_unfold G j n U _).mp hv
  unfold layer canonical at hv'
  generalize hi : G i = gi at hd hv'
  generalize hj : G j = gj at hd hv'
  cases gi <;> cases gj <;> simp_all [head, nodeSem, nulT, boolT, refT, arrowT]

theorem reference_sep {G : Graph (Fin m)} {i j a b}
    (hi : G i = .ref a) (hj : G j = .ref b) (hs : Apart G a b) : Sep G i j := by
  classical
  have hne : ¬ FamEq (denote G a) (denote G b) := by
    rcases hs with hs | hs
    · exact sep_ne hs
    · exact fun he => sep_ne hs (fun n U v => (he n U v).symm)
  have hw : ∃ N U v, ¬ (denote G a N U v ↔ denote G b N U v) := by
    apply Classical.byContradiction
    intro hn
    apply hne
    intro N U v
    apply Classical.byContradiction
    exact fun he => hn ⟨N, U, v, he⟩
  obtain ⟨N, V, w, hbad⟩ := hw
  refine ⟨.loc a.val, N + 1, by intro k x; rfl, ?_, ?_⟩
  · intro n U hx
    apply (denote_unfold G i n U _).mpr
    simp only [layer, hi, nodeSem]
    exact ⟨a.val, res (denote G a), rfl,
      WExt_lookup hx (graphWorld_lookup G n a), fun _ _ _ _ => Iff.rfl⟩
  · intro n hn U h hx hu hh hv
    have hv' := (denote_unfold G j n U _).mp hv
    simp only [layer, hj, nodeSem] at hv'
    obtain ⟨l, c, he, hl, hc⟩ := hv'
    cases he
    have ha := WExt_lookup hx (graphWorld_lookup G n a)
    rw [ha] at hl
    cases hl
    exact hbad (hc N (by omega) V w)

theorem arrow_result_sep {G : Graph (Fin m)} {i j a b c d}
    (hi : G i = .arr a b) (hj : G j = .arr c d) (hs : Sep G b d) : Sep G i j := by
  obtain ⟨v, N, hclosed, hp, hn⟩ := hs
  have hval : isVal v = true := denote_valOnly G b 0 _ v (hp 0 _ (WExt_refl _))
  refine ⟨.lam v, N + 3, ?_, ?_, ?_⟩
  · intro k x
    exact congrArg Tm.lam (hclosed (k + 1) x)
  · intro n U hx
    apply (denote_unfold G i n U _).mpr
    simp only [layer, hi, nodeSem]
    apply lam_intro (denote_valOnly G a)
    intro p hpn V hx' hv h hh x hA
    rw [hclosed]
    have ho := over_ext (over_trunc hx (Nat.le_of_lt hpn)) hx'
    exact value_safe _ p _ h v hval (hp p _ (over_trunc ho (Nat.le_succ p)))
  · intro n hN U h hx hu hh hv
    have ht := (denote_unfold G j n U _).mp hv
    simp only [layer, hj, nodeSem] at ht
    let V := trunc (N + 2) (by omega) U
    have ho : Over G (N + 2) V := over_trunc hx (by omega)
    have hhv : HeapOk (N + 2) V h := heap_down hh (N + 2) (by omega)
    have huv : WorldAdm V := WorldAdm_trunc (show N + 2 ≤ n by omega) hu
    have ha := canonical_over G c (N + 2) V ho
    have hav := denote_valOnly G c (N + 2) V _ ha
    have hs := ht.2 (N + 2) (by omega) V (WExt_refl _) huv h hhv _ ha
    rcases hs with ⟨hbad, _⟩ | ⟨Z, h', t, hz, huz, hs, hhz, hst⟩
    · simp [isVal] at hbad
    obtain ⟨rfl, ht⟩ := beta_inv hav hs
    rw [hclosed] at ht
    subst ht
    have hoz := over_ext (over_trunc ho (Nat.le_succ (N+1))) hz
    exact hn (N+1) (by omega) Z _ hoz huz hhz (safe_value_mem hval hst)

theorem arrow_argument_sep {G : Graph (Fin m)} {i j a b c d}
    (hi : G i = .arr a b) (hj : G j = .arr c d) (hs : Sep G c a) : Sep G i j := by
  obtain ⟨v, N, _, hp, hn⟩ := hs
  have hval : isVal v = true := denote_valOnly G c 0 _ v (hp 0 _ (WExt_refl _))
  refine ⟨tester a.val, N + 4, closed_tester _, ?_, ?_⟩
  · intro n U hx
    apply (denote_unfold G i n U _).mpr
    simp only [layer, hi, nodeSem]
    apply tester_typed (denote_adm G a) (denote_valOnly G a)
    exact ⟨a.val, res (denote G a), rfl,
      WExt_lookup hx (graphWorld_lookup G n a), fun _ _ _ _ => Iff.rfl⟩
  · intro n hN U h hx hu hh hv
    have ht := (denote_unfold G j n U _).mp hv
    simp only [layer, hj, nodeSem] at ht
    let V := trunc (N + 3) (by omega) U
    have ho : Over G (N + 3) V := over_trunc hx (by omega)
    have hhv : HeapOk (N + 3) V h := heap_down hh (N + 3) (by omega)
    have huv : WorldAdm V := WorldAdm_trunc (show N + 3 ≤ n by omega) hu
    have hs := ht.2 (N + 3) (by omega) V (WExt_refl _) huv h hhv v (hp _ _ ho)
    rcases hs with ⟨hbad, _⟩ | ⟨Z, h', t, hz, _, hs, _, hst⟩
    · simp [isVal] at hbad
    obtain ⟨he, rfl⟩ := tester_step_inv hval hs
    subst h'
    have hoz := over_ext (over_trunc ho (Nat.le_succ (N+2))) hz
    rcases hst with ⟨hbad, _⟩ | ⟨Q, h'', t', hq, huq, hs', hhq, _⟩
    · simp [isVal] at hbad
    obtain ⟨he, _, hlt⟩ := write_step_inv hval hs'
    subst h''
    have hoq := over_ext (over_trunc hoz (Nat.le_succ (N+1))) hq
    have hl := WExt_lookup hoq (graphWorld_lookup G (N+1) a)
    obtain ⟨w, hw, hm⟩ := hhq.2 a.val (res (denote G a)) hl
    simp [hlt] at hw
    subst w
    have ham := hm N (show N < N + 1 by omega)
    exact hn N (Nat.le_refl N) _ _ (over_trunc hoq (Nat.le_succ N))
      (WorldAdm_trunc (Nat.le_succ N) huq) (HeapOk_trunc N Q _ hhq) ham

theorem no_apart_bisim (G : Graph (Fin m)) : Bisim G G (fun i j => ¬ Apart G i j) := by
  classical
  intro i j hij
  have hh : head (G i) = head (G j) := by
    by_cases hh : head (G i) = head (G j)
    · exact hh
    · exact False.elim (hij (Or.inl (different_heads hh)))
  cases hi : G i with
  | nul =>
    cases hj : G j <;> simp_all [head, Match.nul]
  | bool =>
    cases hj : G j <;> simp_all [head, Match.bool]
  | ref a =>
    cases hj : G j with
    | nul => simp [hi, hj, head] at hh
    | bool => simp [hi, hj, head] at hh
    | arr b c => simp [hi, hj, head] at hh
    | ref b =>
      exact .ref (fun hs => hij (Or.inl (reference_sep hi hj hs)))
  | arr a b =>
    cases hj : G j with
    | nul => simp [hi, hj, head] at hh
    | bool => simp [hi, hj, head] at hh
    | ref c => simp [hi, hj, head] at hh
    | arr c d =>
      apply Match.arr
      · intro hs
        rcases hs with hs | hs
        · exact hij (Or.inr (arrow_argument_sep hj hi hs))
        · exact hij (Or.inl (arrow_argument_sep hi hj hs))
      · intro hs
        rcases hs with hs | hs
        · exact hij (Or.inl (arrow_result_sep hi hj hs))
        · exact hij (Or.inr (arrow_result_sep hj hi hs))

/-- FULL equality completeness for the stated finite graph fragment: null,
bool, invariant references, arrows, and arbitrary guarded regular recursion.
There is no arrow-injectivity assumption and no additional equation or term
constructor. Roots to be compared are represented in one common finite graph. -/
theorem semantic_eq_iff (G : Graph (Fin m)) (i j : Fin m) :
    FamEq (denote G i) (denote G j) ↔ Eq G G i j := by
  constructor
  · intro he
    refine ⟨fun a b => ¬ Apart G a b, no_apart_bisim G, ?_⟩
    rintro (hs | hs)
    · exact sep_ne hs he
    · exact sep_ne hs (fun n U v => (he n U v).symm)
  · rintro ⟨R, hb, hr⟩
    exact bisim_sound G G R hb hr

/-- Inequivalent regular types have a separator that works at all budgets on
one side, and fails at all sufficiently large budgets in every admissible,
inhabited extension of the canonical world on the other side. -/
theorem separation (G : Graph (Fin m)) (i j : Fin m) (hne : ¬ Eq G G i j) : Apart G i j := by
  classical
  by_cases hs : Apart G i j
  · exact hs
  · exact False.elim (hne ⟨_, no_apart_bisim G, hs⟩)

/-- At actual arrow nodes, semantic equality reflects equality of both
operands. This is a consequence, not a premise, of completeness. -/
theorem arrow_operands_equal {G : Graph (Fin m)} {i j a b c d}
    (hi : G i = .arr a b) (hj : G j = .arr c d)
    (he : FamEq (denote G i) (denote G j)) :
    FamEq (denote G a) (denote G c) ∧ FamEq (denote G b) (denote G d) := by
  obtain ⟨R, hb, hr⟩ := (semantic_eq_iff G i j).mp he
  have hm := hb i j hr
  rw [hi, hj] at hm
  cases hm with
  | arr hac hbd => exact ⟨bisim_sound G G R hb hac, bisim_sound G G R hb hbd⟩

end Verification.ExperimentState.Completeness
