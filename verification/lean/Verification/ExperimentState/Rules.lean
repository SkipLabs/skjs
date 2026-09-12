import Verification.ExperimentState.Safety
/-!
# Compatibility rules

The rules a program's safety proof should be assembled from, rather than traced
by hand. Application spends the beta step and uses the function guarantee one level
below the current budget. Abstraction proves the substituted body safe.

`Safe_bind_appR` is the bind: run a subterm, then continue with whatever value it
produces, in whatever world and heap it produced them. It is what lets composite
programs be built compositionally.
-/
namespace Verification
namespace ExperimentState

/-- The invocation code of an existing object establishes safety at every smaller
budget. Application, rather than this obligation, spends the beta step. -/
theorem fn_intro {l : Nat} {A B : Fam} (b : Tm) (k : Nat) (W : WorldT k) (hc : Scoped 1 b)
    (h : ∀ (j : Nat) (hj : j < k) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U →
      ∀ (heap : Heap), HeapOk j U heap → ∀ a, A j U a →
        Safe B j U heap (subst 0 a b)) : arrowT A B k W (.fn l b) :=
  ⟨⟨b, l, rfl, hc⟩, h⟩

/-- Same-budget application compatibility, the rule needed for the fundamental
 theorem under semantic environments. Both values are available at the current
budget; beta consumes one step and uses the function guarantee below it. -/
theorem app_elim {A B : Fam} (hA : Adm A) (hAv : ValOnly A)
    {n : Nat} {W : WorldT n} {f a : Tm} {heap : Heap}
    (hf : arrowT A B n W f) (ha : A n W a)
    (hw : WorldAdm W) (hh : HeapOk n W heap) : Safe B n W heap (.app f a) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact Or.inr ⟨trunc n (Nat.le_succ n) W, heap, callBody f a,
      WExt_refl _, WorldAdm_trunc _ hw, hf.1.step (hAv _ _ _ ha) heap,
      HeapOk_trunc n W heap hh,
      hf.2 n (Nat.lt_succ_self n) _ (WExt_refl _) (WorldAdm_trunc _ hw) heap
        (HeapOk_trunc n W heap hh) a (hA.down n W a ha)⟩

/-- **Beta.** -/
theorem beta_rule {l : Nat} {B : Fam} (b a : Tm) (hval : isVal a = true) (p : Nat) (W : WorldT (p + 1))
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h)
    (hb : Safe B p (trunc p (Nat.le_succ p) W) h (subst 0 a b)) :
    Safe B (p + 1) W h (.app (.fn l b) a) :=
  Or.inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hadm, .beta hval,
    HeapOk_trunc p W h hok, hb⟩

/-- A binding consumes one step after its initializer has become a value. -/
theorem let_rule {B : Fam} (b a : Tm) (hval : isVal a = true) (p : Nat) (W : WorldT (p + 1))
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h)
    (hb : Safe B p (trunc p (Nat.le_succ p) W) h (subst 0 a b)) :
    Safe B (p + 1) W h (.letE a b) :=
  Or.inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hadm, .letV hval,
    HeapOk_trunc p W h hok, hb⟩

/-- **Evaluation inside the argument of an application.** The bind rule the
composite programs need: run the argument, then continue with whatever value it
produces, in whatever world and heap it produced them. -/
theorem Safe_bind_appR {A B : Fam} (f : Tm) (hfv : isVal f = true) :
    ∀ (n : Nat) (W : WorldT n) (h : Heap) (a : Tm),
      WorldAdm W → HeapOk n W h → Safe A n W h a →
      (∀ (j : Nat) (hj : j ≤ n) (W' : WorldT j), WExt (trunc j hj W) W' → WorldAdm W' →
        ∀ (h' : Heap) (v : Tm), HeapOk j W' h' → A j W' v → Safe B j W' h' (.app f v)) →
      Safe B n W h (.app f a) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _; trivial
  | succ p ih =>
    intro W h a hadm hok hsafe hcont
    rcases hsafe with ⟨hv, hA⟩ | ⟨W', h', a', hx, hadm', hstep, hok', hsafe'⟩
    · exact hcont (p + 1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hadm h a hok hA
    · refine Or.inr ⟨W', h', .app f a', hx, hadm', .appR hfv hstep, hok', ?_⟩
      refine ih W' h' a' hadm' hok' hsafe' ?_
      intro j hj W'' hW hadm'' h'' v hok'' hAv
      refine hcont j (by omega) W'' ?_ hadm'' h'' v hok'' hAv
      refine WExt_trans ?_ hW
      have : trunc j hj W' = trunc j hj W' := rfl
      have hx' : WExt (trunc j hj (trunc p (Nat.le_succ p) W)) (trunc j hj W') :=
        WExt_trunc hj hx
      rwa [trunc_trunc] at hx'

/-! ## Storage -/


/-- **Read.** -/
theorem read_rule {code : CallCode} {A : Fam} (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u) :
    Safe A n W h (.read (.obj l code)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v := (hag p (by omega) _ v).mp (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .readV hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl ⟨hA _ _ _ hAv, hAv⟩

/-- **Write.** -/
theorem write_rule {code : CallCode} {A : Fam} (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) :
    Safe nulT n W h (.write (.obj l code) v) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨w, hw, -⟩ := hok.2 l c hl
    have hlt : l < h.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; omega
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h.set l v, .nul, WExt_refl _,
      WorldAdm_trunc _ hadm, .writeV hval hlt, ?_, Safe_nul p _ _⟩
    refine write_sound p _ h l _ v (HeapOk_trunc p W h hok)
      (lookup_trunc (Nat.le_succ p) W l c hl) ?_
    intro i hi
    show c i _ _ v
    refine (hag i (by omega) _ v).mpr ?_
    have := hA.down_le (p + 1) i (by omega) W v hv
    rw [trunc_trunc]
    exact this

/-- **Allocation.** Storing a value of type `A` yields a reference to `A`, and
the world grows by exactly that contract. -/
theorem alloc_rule {A : Fam} (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (v : Tm)
    (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : A n W v) :
    Safe (refT A) n W h (.alloc v) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : CtrAdm (res A : Ctr p) := fun i _ U U' hx w hw => hA.mono i U U' hx w hw
    have hlen : h.length = (toList (trunc p (Nat.le_succ p) W)).length := by
      have := hok.1; simp [trunc] at this ⊢; omega
    have hcont : ∀ (i : Nat) (hi : i < p),
        (res A : Ctr p) i hi
          (trunc i (Nat.le_of_lt hi) (appendW (trunc p (Nat.le_succ p) W) (res A))) v := by
      intro i hi
      show A i _ v
      rw [trunc_appendW, trunc_trunc]
      exact hA.mono i _ _ (WExt_appendW _ _) v (hA.down_le (p + 1) i (by omega) W v hv)
    refine Or.inr ⟨appendW (trunc p (Nat.le_succ p) W) (res A), h ++ [v], .obj h.length .absent,
      WExt_appendW _ _, WorldAdm_append (WorldAdm_trunc _ hadm) hcadm, .allocV hval,
      heap_alloc p _ h (res A) v (HeapOk_trunc p W h hok) (WorldAdm_trunc _ hadm) hcont,
      ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl ⟨rfl, ⟨h.length, res A, rfl, ?_, fun _ _ _ _ => Iff.rfl⟩⟩
      simp only [lookup, appendW, toList_ofList]
      rw [List.getElem?_append_right (by omega)]
      simp [hlen]

theorem refT_transfer {A : Fam} {k : Nat} {W : WorldT k} {l : Nat}
    (hr : refT A k W (.obj l .absent)) (j : Nat) (hj : j ≤ k) (W' : WorldT j)
    (hW : WExt (trunc j hj W) W') : refT A j W' (.obj l .absent) :=
  (refT_adm A).mono j _ _ hW _ ((refT_adm A).down_le k j hj W _ hr)

/-- A function that ignores its argument and diverges inhabits *every* arrow
type: applied to anything, it never returns, and that is safe at any result. -/
theorem ignore_safe (B : Fam) (n : Nat) (W : WorldT n) (h : Heap)
    (ha : WorldAdm W) (hh : HeapOk n W h) (v : Val) (hv : isVal v = true) :
    Safe B n W h (.app (.fn 0 omegaTm) v) := by
  cases n with
  | zero => trivial
  | succ n =>
    apply beta_rule _ _ hv n W h ha hh
    simpa [omegaTm, delta, subst] using
      omega_safe B n _ h (WorldAdm_trunc _ ha) (HeapOk_trunc n W h hh)

theorem diverging_arrow {A B : Fam} (n : Nat) (W : WorldT n) :
    arrowT A B n W (.fn 0 omegaTm) := by
  apply fn_intro _ _ _ (by simp [omegaTm, delta, Scoped])
  intro p hp U hx hu h hh a hA
  simpa [omegaTm, delta, subst] using
    omega_safe B p U h hu hh

/-- Being stuck is exactly what `Safe` forbids. -/
theorem stuck_not_safe (B : Fam) (k : Nat) (W : WorldT (k + 1)) (h : Heap) :
    ¬ Safe B (k + 1) W h (.app .nul .nul) := by
  rintro (⟨hv, -⟩ | ⟨_, _, _, _, _, hs, _, _⟩)
  · simp [isVal] at hv
  · exact stuck_no_step hs

/-- An arrow with an uninhabited domain constrains nothing: every function has
that type, including one that would get stuck if it were ever applied. -/
theorem vacuous_arrow {l : Nat} {A B : Fam} (hA : ∀ (j : Nat) (W : WorldT j) (v : Val), ¬ A j W v)
    (b : Tm) (k : Nat) (W : WorldT k) (hc : Scoped 1 b) : arrowT A B k W (.fn l b) :=
  ⟨⟨b, l, rfl, hc⟩, fun _ _ _ _ _ _ _ a ha => absurd ha (hA _ _ a)⟩

/-! ## Testing a value's shape, and branching on the answer

The two constructs a narrowing source language needs. A test of a value answers
in one step; a branch on that answer takes one more. Both are ordinary reduction
steps, so each spends a budget, which is why the rule below starts two above the
budget its branches are checked at. -/

/-- **A shape test answers.** -/
theorem test_value_safe (k : Tag) (v : Val) (hv : isVal v = true) (p : Nat)
    (W : WorldT (p + 1)) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) :
    Safe boolT (p + 1) W h (.test k v) := by
  refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
    .testV hv, HeapOk_trunc p W h hok, ?_⟩
  cases p with
  | zero => trivial
  | succ q =>
    refine Or.inl ⟨?_, ?_⟩ <;> cases tagHolds k v <;> simp [boolT, isVal]

/-- **Branching on a shape test.** The two branches are checked under the answer
they run in, which is what makes this narrowing rather than a plain conditional:
the `then` branch may assume the test succeeded. -/
theorem ite_test_rule {B : Fam} (k : Tag) (a : Val) (hv : isVal a = true) (u e : Tm)
    (p : Nat) (W : WorldT (p + 2)) (h : Heap) (hadm : WorldAdm W)
    (hok : HeapOk (p + 2) W h)
    (hthen : tagHolds k a = true → Safe B p (trunc p (by omega) W) h u)
    (helse : tagHolds k a = false → Safe B p (trunc p (by omega) W) h e) :
    Safe B (p + 2) W h (.ite (.test k a) u e) := by
  refine Or.inr ⟨trunc (p + 1) (Nat.le_succ _) W, h, _, WExt_refl _,
    WorldAdm_trunc _ hadm, .iteC (.testV hv), HeapOk_trunc (p + 1) W h hok, ?_⟩
  have hadm' : WorldAdm (trunc (p + 1) (Nat.le_succ _) W) := WorldAdm_trunc _ hadm
  have hok' : HeapOk (p + 1) (trunc (p + 1) (Nat.le_succ _) W) h := HeapOk_trunc (p + 1) W h hok
  cases hb : tagHolds k a with
  | true =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) _, h, u, WExt_refl _, WorldAdm_trunc _ hadm',
      by simp; exact Step.iteT, HeapOk_trunc p _ h hok', ?_⟩
    rw [trunc_trunc]
    exact hthen hb
  | false =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) _, h, e, WExt_refl _, WorldAdm_trunc _ hadm',
      by simp; exact Step.iteF, HeapOk_trunc p _ h hok', ?_⟩
    rw [trunc_trunc]
    exact helse hb


/-- An arrow below every conjunct is below the intersection: one function serves
a whole overloaded type when its domain covers every domain and its codomain
sits inside every codomain. -/
theorem arrowsT_of_arrow {L : List (Fam × Fam)} {A B : Fam}
    (hdom : ∀ p ∈ L, FamLe p.1 A) (hcod : ∀ p ∈ L, FamLe B p.2) :
    FamLe (arrowT A B) (arrowsT L) := by
  rintro n W v ⟨hl, h⟩
  refine ⟨hl, ?_⟩
  intro p hp j hj W' hx hu hh hok a ha
  exact Safe_mono j (fun m _ U u hb => hcod p hp m U u hb) W' hh _
    (h j hj W' hx hu hh hok a (hdom p hp j W' a ha))

/-- The diverging function inhabits every intersection of arrows, as a direct check that these types admit safe nontermination. -/
theorem diverging_in_arrowsT (L : List (Fam × Fam))
    (k : Nat) (W : WorldT k) : arrowsT L k W (.fn 0 omegaTm) := by
  refine ⟨⟨omegaTm, 0, rfl, by simp [omegaTm, delta, Scoped]⟩, ?_⟩
  intro p hp j hj W' hx hu hh hok a ha
  exact (diverging_arrow (A := p.1) (B := p.2) k W).2 j hj W' hx hu hh hok a ha


#print axioms let_rule

end ExperimentState
end Verification
