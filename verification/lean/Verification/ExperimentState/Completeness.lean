import Verification.ExperimentState.Rules

/-!
Equality completeness for the recursive types of this model. Regular types are
finite graphs whose edges pass through a reference
or arrow constructor; this makes guardedness explicit without a binder encoding.
The results below concern equality of the existing indexed families, not
contextual equivalence or completeness of the program verifier.

`Separation.lean` proves full equality completeness for this finite graph
language, using the infrastructure and inhabitants developed here.
-/
namespace Verification.ExperimentState.Completeness

def FamEq (A B : Fam) : Prop := ∀ n W v, A n W v ↔ B n W v

inductive Node (ι : Type) where
  | nul | bool | ref (a : ι) | arr (a b : ι)
  deriving DecidableEq

abbrev Graph (ι : Type) := ι → Node ι

def nodeSem (X : ι → Fam) : Node ι → Fam
  | .nul => nulT
  | .bool => boolT
  | .ref a => refT (X a)
  | .arr a b => arrowT (X a) (X b)

def layer (G : Graph ι) (X : ι → Fam) (i : ι) : Fam := nodeSem X (G i)

theorem layer_congr (G : Graph ι) (X Y : ι → Fam) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (i : ι) (W : WorldT n) (v : Val) :
    layer G X i n W v ↔ layer G Y i n W v := by
  unfold layer
  cases G i with
  | nul => rfl
  | bool => rfl
  | ref a => exact refT_contractive n _ _ (h a) W v
  | arr a b =>
    exact (arrowT_contractive (X b) n _ _ (h a) W v).trans
      (arrowT_cod_contractive (Y a) n _ _ (h b) W v)

def approx (G : Graph ι) : Nat → ι → Fam
  | 0 => fun _ => topF
  | k + 1 => layer G (approx G k)

theorem approx_stable (G : Graph ι) (n : Nat) :
    ∀ k l, n < k → n < l → ∀ i W v,
      approx G k i n W v ↔ approx G l i n W v := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k l hk hl i W v
    cases k with
    | zero => omega
    | succ k =>
      cases l with
      | zero => omega
      | succ l =>
        exact layer_congr G _ _ n (fun a m hm U u =>
          ih m hm k l (by omega) (by omega) a U u) i W v

def denote (G : Graph ι) (i : ι) : Fam := fun n => approx G (n + 1) i n

theorem denote_unfold (G : Graph ι) (i : ι) (n : Nat) (W : WorldT n) (v : Val) :
    denote G i n W v ↔ layer G (denote G) i n W v := by
  exact layer_congr G _ _ n (fun a m hm U u =>
    approx_stable G m n (m + 1) hm (by omega) a U u) i W v

/-- The graph interpretation is the unique solution of its guarded equations
in the existing family model. It is not an alternative tree-valued semantics. -/
theorem denote_unique (G : Graph ι) (X : ι → Fam)
    (hx : ∀ i n W v, X i n W v ↔ layer G X i n W v) (i : ι) :
    FamEq (X i) (denote G i) := by
  intro n
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    intro W v
    rw [hx, denote_unfold]
    exact layer_congr G X (denote G) n (fun a j hj U u => ih j hj a U u) i W v

theorem layer_adm (G : Graph ι) (X : ι → Fam) (i : ι) : Adm (layer G X i) := by
  unfold layer
  cases G i with
  | nul => exact nulT_adm
  | bool => exact boolT_adm
  | ref a => exact refT_adm _
  | arr a b => exact arrowT_adm _ _

theorem denote_adm (G : Graph ι) (i : ι) : Adm (denote G i) := by
  constructor
  · intro n W v hv
    exact (denote_unfold G i n _ v).mpr ((layer_adm G (denote G) i).down n W v
      ((denote_unfold G i (n + 1) W v).mp hv))
  · intro n W W' hx v hv
    exact (denote_unfold G i n W' v).mpr ((layer_adm G (denote G) i).mono n W W' hx v
      ((denote_unfold G i n W v).mp hv))

theorem denote_valOnly (G : Graph ι) (i : ι) : ValOnly (denote G i) := by
  intro n W v hv
  have hh := (denote_unfold G i n W v).mp hv
  unfold layer at hh
  cases hg : G i <;> rw [hg] at hh
  · exact nulT_valOnly n W v hh
  · exact boolT_valOnly n W v hh
  · exact refT_valOnly _ n W v hh
  · exact arrowT_valOnly _ _ n W v hh

/-- A finite relation on finite graphs is an ordinary checkable cyclic equality
certificate. The semantic proof also works for infinite index sets. -/
inductive Match (R : ι → κ → Prop) : Node ι → Node κ → Prop where
  | nul : Match R .nul .nul
  | bool : Match R .bool .bool
  | ref : R a b → Match R (.ref a) (.ref b)
  | arr : R a c → R b d → Match R (.arr a b) (.arr c d)

def Bisim (G : Graph ι) (H : Graph κ) (R : ι → κ → Prop) : Prop :=
  ∀ i j, R i j → Match R (G i) (H j)

/-- The cyclic structural equality judgment. For finite graphs its witness is
a finite relation. No equality axiom is postulated in the semantic model. -/
def Eq (G : Graph ι) (H : Graph κ) (i : ι) (j : κ) : Prop :=
  ∃ R, Bisim G H R ∧ R i j

theorem match_sem {R : ι → κ → Prop} {X : ι → Fam} {Y : κ → Fam}
    {a : Node ι} {b : Node κ} (hm : Match R a b) (n : Nat)
    (h : ∀ i j, R i j → Agree (X i) (Y j) n) (W : WorldT n) (v : Val) :
    nodeSem X a n W v ↔ nodeSem Y b n W v := by
  cases hm with
  | nul => rfl
  | bool => rfl
  | ref hab => exact refT_contractive n _ _ (h _ _ hab) W v
  | arr hac hbd =>
    exact (arrowT_contractive _ n _ _ (h _ _ hac) W v).trans
      (arrowT_cod_contractive _ n _ _ (h _ _ hbd) W v)

theorem bisim_sound (G : Graph ι) (H : Graph κ) (R : ι → κ → Prop)
    (hb : Bisim G H R) {i j} (hij : R i j) : FamEq (denote G i) (denote H j) := by
  intro n
  induction n using Nat.strongRecOn generalizing i j with
  | ind n ih =>
    intro W v
    rw [denote_unfold, denote_unfold]
    exact match_sem (hb i j hij) n (fun _ _ hr m hm U u => ih m hm hr U u) W v

theorem ref_injective {A B : Fam} (h : FamEq (refT A) (refT B)) : FamEq A B := by
  intro n W v
  have hr : refT A (n + 1) (ofList [res A]) (.loc 0) :=
    ⟨0, res A, rfl, by simp [lookup], fun _ _ _ _ => Iff.rfl⟩
  obtain ⟨l, c, hv, hl, hc⟩ := (h (n + 1) _ _).mp hr
  cases hv
  simp only [lookup, toList_ofList, List.getElem?_cons_zero, Option.some.injEq] at hl
  subst hl
  exact hc n (by omega) W v

def head : Node ι → Nat
  | .nul => 0 | .bool => 1 | .ref _ => 2 | .arr _ _ => 3

theorem equal_heads {X : ι → Fam} {Y : κ → Fam} {a : Node ι} {b : Node κ}
    (h : FamEq (nodeSem X a) (nodeSem Y b)) : head a = head b := by
  have hn := h 0 (ofList [res topF]) .nul
  have ht := h 0 (ofList [res topF]) .tru
  have hl := h 0 (ofList [res topF]) (.loc 0)
  have hf := h 0 (ofList [res topF]) (.lam .nul)
  cases a <;> cases b <;>
    simp_all [nodeSem, head, nulT, boolT, refT, arrowT, lookup]

def NoArrows (G : Graph ι) : Prop := ∀ i a b, G i ≠ .arr a b

/-- Complete for the entire reference-only graph language, including cycles.
This is equality of denotations iff bisimilarity, not just a syntax theorem. -/
theorem reference_complete (G : Graph ι) (H : Graph κ)
    (hG : NoArrows G) :
    Bisim G H (fun i j => FamEq (denote G i) (denote H j)) := by
  intro i j hij
  have he : FamEq (nodeSem (denote G) (G i)) (nodeSem (denote H) (H j)) :=
    fun n W v => (denote_unfold G i n W v).symm.trans
      ((hij n W v).trans (denote_unfold H j n W v))
  have hh := equal_heads he
  generalize hg : G i = gi at he hh ⊢
  generalize hk : H j = hj at he hh ⊢
  cases gi with
  | nul => cases hj <;> simp_all [head, Match.nul]
  | bool => cases hj <;> simp_all [head, Match.bool]
  | ref a =>
    cases hj with
    | nul => simp [head] at hh
    | bool => simp [head] at hh
    | arr b c => simp [head] at hh
    | ref b => exact .ref (ref_injective he)
  | arr a b => exact False.elim (hG i a b hg)

theorem reference_eq_iff (G : Graph ι) (H : Graph κ)
    (hG : NoArrows G) (hH : NoArrows H) (i : ι) (j : κ) :
    FamEq (denote G i) (denote H j) ↔ ∃ R, Bisim G H R ∧ R i j := by
  constructor
  · intro he
    exact ⟨_, reference_complete G H hG, he⟩
  · rintro ⟨R, hb, hr⟩
    exact bisim_sound G H R hb hr

/-- A sufficient condition isolating the distinction between graph-denotable
operands and arbitrary admissible families. The full proof in `Separation.lean`
does not assume this condition: it constructs separators instead. -/
def ArrowReflection (G : Graph ι) (H : Graph κ) : Prop :=
  ∀ a b c d,
    FamEq (arrowT (denote G a) (denote G b)) (arrowT (denote H c) (denote H d)) →
      FamEq (denote G a) (denote H c) ∧ FamEq (denote G b) (denote H d)

theorem complete_of_arrow_reflection (G : Graph ι) (H : Graph κ)
    (ha : ArrowReflection G H) {i j} (hij : FamEq (denote G i) (denote H j)) :
    Eq G H i j := by
  refine ⟨fun a b => FamEq (denote G a) (denote H b), ?_, hij⟩
  intro a b hab
  have he : FamEq (nodeSem (denote G) (G a)) (nodeSem (denote H) (H b)) :=
    fun n W v => (denote_unfold G a n W v).symm.trans
      ((hab n W v).trans (denote_unfold H b n W v))
  have hh := equal_heads he
  generalize hg : G a = ga at he hh ⊢
  generalize hk : H b = hb at he hh ⊢
  cases ga with
  | nul => cases hb <;> simp_all [head, Match.nul]
  | bool => cases hb <;> simp_all [head, Match.bool]
  | ref x =>
    cases hb with
    | nul => simp [head] at hh
    | bool => simp [head] at hh
    | arr y z => simp [head] at hh
    | ref y => exact .ref (ref_injective he)
  | arr x y =>
    cases hb with
    | nul => simp [head] at hh
    | bool => simp [head] at hh
    | ref z => simp [head] at hh
    | arr z w => exact .arr (ha x y z w he).1 (ha x y z w he).2

/-! Every type in a finite graph has an inhabitant in a common, admissible,
inhabited world. This includes mixed reference/arrow cycles and negative
recursion, not just the reference-only completeness fragment. -/

def graphWorld (G : Graph (Fin m)) (n : Nat) : WorldT n :=
  ofList (List.ofFn (fun i => (res (denote G i) : Ctr n)))

def canonical (G : Graph (Fin m)) (i : Fin m) : Val :=
  match G i with
  | .nul => .nul
  | .bool => .tru
  | .ref a => .loc a.val
  | .arr _ _ => .lam omegaTm

theorem graphWorld_lookup (G : Graph (Fin m)) (n : Nat) (i : Fin m) :
    lookup (graphWorld G n) i.val = some (res (denote G i)) := by
  simp [graphWorld, lookup]

theorem graphWorld_trunc (G : Graph (Fin m)) {n j : Nat} (hj : j ≤ n) :
    trunc j hj (graphWorld G n) = graphWorld G j := by
  simp only [graphWorld, trunc, toList_ofList, List.map_ofFn]
  rfl

theorem canonical_mem (G : Graph (Fin m)) (i : Fin m) (n : Nat) :
    denote G i n (graphWorld G n) (canonical G i) := by
  apply (denote_unfold G i n _ _).mpr
  unfold layer canonical
  cases hg : G i with
  | nul => rfl
  | bool => exact Or.inl rfl
  | ref a =>
    exact ⟨a.val, res (denote G a), rfl, graphWorld_lookup G n a, fun _ _ _ _ => Iff.rfl⟩
  | arr a b => exact diverging_arrow (denote_valOnly G a) n _

theorem graphWorld_adm (G : Graph (Fin m)) (n : Nat) : WorldAdm (graphWorld G n) := by
  intro l c hl
  have hlt : l < m := by
    have := (List.getElem?_eq_some_iff.mp hl).1
    simpa [lookup, graphWorld] using this
  have he := graphWorld_lookup G n ⟨l, hlt⟩
  rw [hl] at he
  cases he
  exact fun j _ U U' hx v hv => (denote_adm G ⟨l, hlt⟩).mono j U U' hx v hv

def graphHeap (G : Graph (Fin m)) : Heap := List.ofFn (canonical G)

theorem graphHeap_ok (G : Graph (Fin m)) (n : Nat) : HeapOk n (graphWorld G n) (graphHeap G) := by
  refine ⟨by simp [graphHeap, graphWorld], ?_⟩
  intro l c hl
  have hlt : l < m := by
    have := (List.getElem?_eq_some_iff.mp hl).1
    simpa [lookup, graphWorld] using this
  have he := graphWorld_lookup G n ⟨l, hlt⟩
  rw [hl] at he
  cases he
  refine ⟨canonical G ⟨l, hlt⟩, by simp [graphHeap, hlt], ?_⟩
  intro j hj
  change denote G ⟨l, hlt⟩ j _ _
  rw [graphWorld_trunc]
  exact canonical_mem G ⟨l, hlt⟩ j

def cellWorld (A : Fam) (n : Nat) : WorldT n := ofList [res A]

theorem cellWorld_ref (A : Fam) (n : Nat) : refT A n (cellWorld A n) (.loc 0) :=
  ⟨0, res A, rfl, by simp [cellWorld, lookup], fun _ _ _ _ => Iff.rfl⟩

theorem cellWorld_adm {A : Fam} (ha : Adm A) (n : Nat) : WorldAdm (cellWorld A n) := by
  intro l c hl
  cases l with
  | zero =>
    simp only [cellWorld, lookup, toList_ofList, List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    exact fun j _ U U' hx v hv => ha.mono j U U' hx v hv
  | succ l => simp [cellWorld, lookup] at hl

theorem nullCell_heap (n : Nat) : HeapOk n (cellWorld nulT n) [.nul] := by
  refine ⟨by simp [cellWorld], ?_⟩
  intro l c hl
  cases l with
  | zero =>
    simp only [cellWorld, lookup, toList_ofList, List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    exact ⟨.nul, rfl, fun _ _ => rfl⟩
  | succ l => simp [cellWorld, lookup] at hl

theorem tester_beta_inv {h h' t} (hs : Step h (.app (tester 0) .tru) h' t) :
    h' = h ∧ t = .app (.lam omegaTm) (.write (.loc 0) .tru) := by
  cases hs with
  | appL hs => cases hs
  | appR _ hs => cases hs
  | beta => exact ⟨rfl, rfl⟩

theorem tester_write_inv {h' t}
    (hs : Step [.nul] (.app (.lam omegaTm) (.write (.loc 0) .tru)) h' t) :
    h' = [.tru] ∧ t = .app (.lam omegaTm) .nul := by
  cases hs with
  | appL hs => cases hs
  | beta hv => simp [isVal] at hv
  | appR _ hs =>
    cases hs with
    | writeC1 hs => cases hs
    | writeC2 _ hs => cases hs
    | writeV => exact ⟨rfl, rfl⟩

theorem tester_rejects_bool (B : Fam) :
    ¬ arrowT boolT B 4 (cellWorld nulT 4) (tester 0) := by
  intro ht
  have he : WExt (trunc 3 (by omega) (cellWorld nulT 4)) (cellWorld nulT 3) := by
    simpa [cellWorld, trunc_res] using WExt_refl (cellWorld nulT 3)
  have hs := ht.2 3 (by omega) (cellWorld nulT 3) he
    (cellWorld_adm nulT_adm 3) [.nul] (nullCell_heap 3) .tru (Or.inl rfl)
  rcases hs with ⟨hv, _⟩ | ⟨U, h, t, hx, _, hs, _, ht⟩
  · simp [isVal] at hv
  obtain ⟨rfl, rfl⟩ := tester_beta_inv hs
  have hr := refT_transfer (cellWorld_ref nulT 3) 2 (by omega) U hx
  rcases ht with ⟨hv, _⟩ | ⟨V, h', t', hx', _, hs', hh', _⟩
  · simp [isVal] at hv
  obtain ⟨rfl, rfl⟩ := tester_write_inv hs'
  have hr' := refT_transfer hr 1 (by omega) V hx'
  obtain ⟨l, c, hv, hl, hc⟩ := hr'
  cases hv
  obtain ⟨v, hv, hm⟩ := hh'.2 0 c hl
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
  subst hv
  have hm0 := hm 0 (show 0 < 1 by decide)
  have hn := (hc 0 (show 0 < 1 by decide) _ .tru).mp hm0
  cases hn

/-- The separation holds for EVERY codomain, even a recursive codomain, and
uses an admissible world with an inhabited heap. It is not based on a typecase. -/
theorem arrow_domain_separation (B : Fam) :
    ¬ FamEq (arrowT nulT B) (arrowT boolT B) := by
  intro he
  exact tester_rejects_bool B ((he 4 (cellWorld nulT 4) (tester 0)).mp
    (tester_typed nulT_adm nulT_valOnly 4 _ 0 (cellWorld_ref nulT 4)))

/-! ## A closed, recursive type-syntax instance -/

/-- Nodes 2 and 3 are `null → R` and `bool → R`, where `R = R → null`.
There are no free parameters or extra semantic type constructors. -/
def recursiveExample : Graph (Fin 5) := fun i =>
  match i.val with
  | 0 => .nul
  | 1 => .bool
  | 2 => .arr 0 4
  | 3 => .arr 1 4
  | _ => .arr 4 0

theorem recursive_example_distinct :
    ¬ FamEq (denote recursiveExample 2) (denote recursiveExample 3) := by
  intro he
  apply arrow_domain_separation (denote recursiveExample 4)
  intro n W v
  have h2 := denote_unfold recursiveExample 2 n W v
  have h3 := denote_unfold recursiveExample 3 n W v
  have hn : ∀ j U u, denote recursiveExample 0 j U u ↔ nulT j U u :=
    fun j U u => denote_unfold recursiveExample 0 j U u
  have hb : ∀ j U u, denote recursiveExample 1 j U u ↔ boolT j U u :=
    fun j U u => denote_unfold recursiveExample 1 j U u
  have ha := arrowT_contractive (denote recursiveExample 4) n _ _
    (fun j _ U u => hn j U u) W v
  have hc := arrowT_contractive (denote recursiveExample 4) n _ _
    (fun j _ U u => hb j U u) W v
  exact ha.symm.trans (h2.symm.trans ((he n W v).trans (h3.trans hc)))

/-! ## Why dropping budget zero is not a congruence -/

def bump (A : Fam) : Fam
  | 0, _, _ => True
  | n + 1, W, v => A (n + 1) W v

theorem bump_adm {A : Fam} (ha : Adm A) : Adm (bump A) := by
  constructor
  · intro n W v hv
    cases n with
    | zero => trivial
    | succ n => exact ha.down (n + 1) W v hv
  · intro n W W' hx v hv
    cases n with
    | zero => trivial
    | succ n => exact ha.mono (n + 1) W W' hx v hv

theorem bump_agrees_positive (A : Fam) (n : Nat) (W : WorldT (n + 1)) (v : Val) :
    bump A (n + 1) W v ↔ A (n + 1) W v := Iff.rfl

/-- A discrepancy confined to budget zero becomes a positive-budget discrepancy
under `ref`. Thus equality at positive budgets is not a constructor congruence. -/
theorem ref_observes_zero :
    ¬ (refT (bump nulT) 1 (cellWorld (bump nulT) 1) (.loc 0) ↔
       refT nulT 1 (cellWorld (bump nulT) 1) (.loc 0)) := by
  intro he
  obtain ⟨l, c, hv, hl, hc⟩ := he.mp (cellWorld_ref (bump nulT) 1)
  cases hv
  simp only [cellWorld, lookup, toList_ofList, List.getElem?_cons_zero, Option.some.injEq] at hl
  subst hl
  have hn := (hc 0 (by decide) (ofList []) .tru).mp trivial
  cases hn

end Verification.ExperimentState.Completeness
