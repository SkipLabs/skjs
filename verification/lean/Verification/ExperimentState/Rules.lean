import Verification.ExperimentState.Safety
/-!
# Compatibility rules

The rules a program's safety proof should be assembled from, rather than traced
by hand. Abstraction is where the budget arithmetic lives: applying a lambda
costs the beta step, so the body is obliged exactly one level below the argument.

`Safe_bind_appR` is the bind: run a subterm, then continue with whatever value it
produces, in whatever world and heap it produced them. It is what lets composite
programs be built compositionally.
-/
namespace Verification
namespace ExperimentState

/-- **Abstraction.** The body is obliged one level below the argument, which is
the level the beta step pays for. -/
theorem lam_intro {A B : Fam} (hA : ValOnly A) (b : Tm) (k : Nat) (W : WorldT k)
    (h : ∀ (p : Nat) (hp : p + 1 < k) (W' : WorldT (p + 1)),
      WExt (trunc (p + 1) (Nat.le_of_lt hp) W) W' → WorldAdm W' →
      ∀ (hp' : Heap), HeapOk (p + 1) W' hp' → ∀ a, A (p + 1) W' a →
        Safe B p (trunc p (Nat.le_succ p) W') hp' (subst 0 a b)) :
    arrowT A B k W (.lam b) := by
  refine ⟨⟨b, rfl⟩, ?_⟩
  intro j hj W' hW hadm hh hok a ha
  cases j with
  | zero => trivial
  | succ p =>
    exact Or.inr ⟨trunc p (Nat.le_succ p) W', hh, subst 0 a b, WExt_refl _,
      WorldAdm_trunc _ hadm, .beta (hA _ _ _ ha), HeapOk_trunc p W' hh hok,
      h p hj W' hW hadm hh hok a ha⟩

/-- **Application.** -/
theorem app_elim {A B : Fam} {k j : Nat} {W : WorldT k} {v : Tm}
    (hv : arrowT A B k W v) (hj : j < k) {W' : WorldT j}
    (hW : WExt (trunc j (Nat.le_of_lt hj) W) W') (hadm : WorldAdm W')
    {h : Heap} (hok : HeapOk j W' h) {a : Tm} (ha : A j W' a) :
    Safe B j W' h (.app v a) := hv.2 j hj W' hW hadm h hok a ha

/-- **Beta.** -/
theorem beta_rule {B : Fam} (b a : Tm) (hval : isVal a = true) (p : Nat) (W : WorldT (p + 1))
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h)
    (hb : Safe B p (trunc p (Nat.le_succ p) W) h (subst 0 a b)) :
    Safe B (p + 1) W h (.app (.lam b) a) :=
  Or.inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hadm, .beta hval,
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
theorem read_rule {A : Fam} (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u) :
    Safe A n W h (.read (.loc l)) := by
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
theorem write_rule {A : Fam} (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) :
    Safe nulT n W h (.write (.loc l) v) := by
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
    refine Or.inr ⟨appendW (trunc p (Nat.le_succ p) W) (res A), h ++ [v], .loc h.length,
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
    (hr : refT A k W (.loc l)) (j : Nat) (hj : j ≤ k) (W' : WorldT j)
    (hW : WExt (trunc j hj W) W') : refT A j W' (.loc l) :=
  (refT_adm A).mono j _ _ hW _ ((refT_adm A).down_le k j hj W _ hr)

end ExperimentState
end Verification
