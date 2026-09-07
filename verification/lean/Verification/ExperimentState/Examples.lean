import Verification.ExperimentState.Rules
/-!
# Worked examples

Three things are checked here. That a recursive *function* type behaves --
`μX. X → null` is the case a fixed-point reading cannot have at all, since its
recursion sits in an argument position. That a closure over a mutable cell stays
safe when another reference writes to it. And that these compose into a program
which allocates, mutates and reads back, with the observed value genuinely
changing.

`badFn_not_in_arrow` is the guard on the other side: everything above is an
implication and would hold of a `Safe` that accepted anything, so a callable
whose body is stuck is shown to be rejected.
-/
namespace Verification
namespace ExperimentState

/-! ## A recursive function type -/


def Rf : Fam := fixF (fun X => arrowT X nulT)

theorem Rf_unfold (n : Nat) (W : WorldT n) (v : Val) : Rf n W v ↔ arrowT Rf nulT n W v :=
  fix_unfold _ (arrowT_contractive nulT) n W v

theorem Rf_lam {n W t} (h : Rf n W t) : ∃ b, t = .lam b := ((Rf_unfold n W t).mp h).1

def hFn : Tm := .lam .nul

def kFn : Tm := .lam (.app (.var 0) hFn)

theorem hFn_in_Rf : ∀ (n : Nat) (W : WorldT n), Rf n W hFn := by
  intro n W
  refine (Rf_unfold n W hFn).mpr ⟨⟨.nul, rfl⟩, ?_⟩
  intro j _ W' _ hadm h hok a ha
  cases j with
  | zero => trivial
  | succ p =>
    obtain ⟨c, rfl⟩ := Rf_lam ha
    exact Or.inr ⟨trunc p (Nat.le_succ p) W', h, .nul,
      WExt_refl _, WorldAdm_trunc _ hadm, .beta rfl, HeapOk_trunc p W' h hok,
      Safe_nul p _ h⟩

/-- **The recursive-function example, in the same model as the worlds and the
heap.** The level the beta step pays for is exactly the level at which the
argument's own arrow property is available. -/
theorem kFn_in_Rf : ∀ (n : Nat) (W : WorldT n), Rf n W kFn := by
  intro n W
  refine (Rf_unfold n W kFn).mpr ⟨⟨_, rfl⟩, ?_⟩
  intro j _ W' _ hadm h hok a ha
  cases j with
  | zero => trivial
  | succ p =>
    obtain ⟨c, rfl⟩ := Rf_lam ha
    refine Or.inr ⟨trunc p (Nat.le_succ p) W', h, .app (.lam c) hFn,
      WExt_refl _, WorldAdm_trunc _ hadm, .beta rfl, HeapOk_trunc p W' h hok, ?_⟩
    exact ((Rf_unfold _ W' _).mp ha).2 p (by omega) (trunc p (Nat.le_succ p) W')
      (WExt_refl _) (WorldAdm_trunc _ hadm) h (HeapOk_trunc p W' h hok) hFn
      (hFn_in_Rf p _)

/-! ## A closure over a mutable cell -/


/-- `capFn` ignores its argument and reads location 0. -/
def capFn : Tm := .lam (.read (.loc 0))

/-- It inhabits `null → null` against any world extending one that declares
location 0 to hold `null` -- **in every heap satisfying that world**, not in one
particular heap. -/
theorem capFn_in_arrow (n : Nat) : arrowT nulT nulT n (ofList [res nulT]) capFn := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro j hj W' hW hadm h hok a ha
  have ha' : a = .nul := ha
  subst ha'
  cases j with
  | zero => trivial
  | succ p =>
    rw [trunc_res] at hW
    have hl0 : lookup W' 0 = some (res nulT) :=
      WExt_lookup hW (by simp [lookup])
    refine Or.inr ⟨trunc p (Nat.le_succ p) W', h, .read (.loc 0),
      WExt_refl _, WorldAdm_trunc _ hadm, .beta rfl, HeapOk_trunc p W' h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      obtain ⟨v, hv, hmem⟩ := hok.2 0 (res nulT) hl0
      have hvnul : v = .nul := hmem 0 (by omega)
      subst hvnul
      refine Or.inr ⟨trunc q (Nat.le_succ q) _, h, .nul,
        WExt_refl _, WorldAdm_trunc _ (WorldAdm_trunc _ hadm), .readV hv, ?_,
        Safe_nul q _ h⟩
      exact HeapOk_trunc q _ h (HeapOk_trunc (q + 1) W' h hok)

/-- **And it survives an alias writing to that cell.** The write preserves heap
satisfaction, and `capFn`'s safety was stated against satisfaction rather than
against a particular heap -- so the closure is still safe in the new one. -/
theorem capFn_survives_alias_write (n j : Nat) (hj : j < n) (W' : WorldT j) (h : Heap)
    (hW : WExt (trunc j (Nat.le_of_lt hj) (ofList [res nulT])) W')
    (hadm : WorldAdm W') (hok : HeapOk j W' h) (c : Ctr j) (hl : lookup W' 0 = some c)
    (hv : ∀ (i : Nat) (hi : i < j), c i hi (trunc i (Nat.le_of_lt hi) W') .nul) :
    Safe nulT j W' (h.set 0 .nul) (.app capFn .nul) :=
  (capFn_in_arrow n).2 j hj W' hW hadm (h.set 0 .nul)
    (write_sound j W' h 0 c .nul hok hl hv) .nul rfl

/-! ## The combination

    let r = alloc true in
    (fun _ => read r) (write r false)

Allocate a cell, change it through one reference, read it through a closure that
captured another. -/


def inner : Tm := .lam (.read (.var 1))

def body : Tm := .app inner (.write (.var 0) .fls)

def prog : Tm := .app (.lam body) (.alloc .tru)

/-- Reading through the captured closure, at any level and admissible world in
which the cell is a boolean reference. -/
theorem closure_read {l : Nat} : ∀ (j : Nat) (W : WorldT j) (h : Heap),
    refT boolT j W (.loc l) → WorldAdm W → HeapOk j W h →
    ∀ v, isVal v = true → Safe boolT j W h (.app (.lam (.read (.loc l))) v) := by
  intro j W h hr hadm hok v hv
  cases j with
  | zero => trivial
  | succ r =>
    refine beta_rule _ v hv r W h hadm hok ?_
    have hr' := refT_transfer hr r (Nat.le_succ r) _ (WExt_refl _)
    obtain ⟨l', c, hvl, hl, hag⟩ := hr'
    injection hvl with hll
    subst hll
    exact read_rule boolT_valOnly r _ h l (WorldAdm_trunc _ hadm)
      (HeapOk_trunc r W h hok) hl hag

/-- **The target.** -/
theorem prog_safe : ∀ (n : Nat) (W : WorldT n) (h : Heap),
    WorldAdm W → HeapOk n W h → Safe boolT n W h prog := by
  intro n W h hadm hok
  refine Safe_bind_appR (A := refT boolT) _ rfl n W h _ hadm hok
    (alloc_rule boolT_adm n W h .tru rfl hadm hok (Or.inl rfl)) ?_
  intro j _ W' _ hadm' h' v hok' hv
  obtain ⟨l, c, rfl, hl, hag⟩ := hv
  have hr : refT boolT j W' (.loc l) := ⟨l, c, rfl, hl, hag⟩
  cases j with
  | zero => trivial
  | succ q =>
    refine beta_rule _ _ rfl q W' h' hadm' hok' ?_
    show Safe boolT q _ h' (.app (.lam (.read (.loc l))) (.write (.loc l) .fls))
    have hrq : refT boolT q (trunc q (Nat.le_succ q) W') (.loc l) :=
      refT_transfer hr q (Nat.le_succ q) _ (WExt_refl _)
    have hrqc := hrq
    obtain ⟨l2, c2, hvl2, hl2, hag2⟩ := hrqc
    injection hvl2 with hll2
    subst hll2
    refine Safe_bind_appR (A := nulT) _ rfl q _ h' _ (WorldAdm_trunc _ hadm')
      (HeapOk_trunc q W' h' hok') ?_ ?_
    · exact write_rule boolT_adm q _ h' l .fls rfl (WorldAdm_trunc _ hadm')
        (HeapOk_trunc q W' h' hok') hl2 hag2 (Or.inr rfl)
    · intro i hi W'' hW'' hadm'' h'' u hok'' hu
      have hu' : u = .nul := hu
      subst hu'
      exact closure_read i W'' h''
        (refT_transfer hrq i hi W'' hW'') hadm'' hok'' .nul rfl

/-- **The mutation is observable.** The program allocates `true`, overwrites it
through one reference, and the closure reads `false` back -- so the cell's
contents really change, rather than being rewritten with the value they had. -/
theorem prog_runs :
    Step [] prog [.tru] (.app (.lam body) (.loc 0)) ∧
      Step [.tru] (.app (.lam body) (.loc 0)) [.tru]
        (.app (.lam (.read (.loc 0))) (.write (.loc 0) .fls)) ∧
      Step [.tru] (.app (.lam (.read (.loc 0))) (.write (.loc 0) .fls)) [.fls]
        (.app (.lam (.read (.loc 0))) .nul) ∧
      Step [.fls] (.app (.lam (.read (.loc 0))) .nul) [.fls] (.read (.loc 0)) ∧
      Step [.fls] (.read (.loc 0)) [.fls] .fls :=
  ⟨.appR rfl (.allocV rfl), .beta rfl, .appR rfl (.writeV rfl (by simp)),
    .beta rfl, .readV rfl⟩

/-- And the whole thing really is a function of that type. -/
theorem prog_lam_arrow (k : Nat) (W : WorldT k) :
    arrowT (refT boolT) boolT k W (.lam body) := by
  refine lam_intro (refT_valOnly boolT) _ k W ?_
  intro p hp W' hW hadm hh hok a ha
  obtain ⟨l, c, rfl, hl, hag⟩ := ha
  have hr : refT boolT (p + 1) W' (.loc l) := ⟨l, c, rfl, hl, hag⟩
  show Safe boolT p _ hh (.app (.lam (.read (.loc l))) (.write (.loc l) .fls))
  have hrp : refT boolT p (trunc p (Nat.le_succ p) W') (.loc l) :=
    refT_transfer hr p (Nat.le_succ p) _ (WExt_refl _)
  have hrpc := hrp
  obtain ⟨l2, c2, hvl2, hl2, hag2⟩ := hrpc
  injection hvl2 with hll2
  subst hll2
  refine Safe_bind_appR (A := nulT) _ rfl p _ hh _ (WorldAdm_trunc _ hadm)
    (HeapOk_trunc p W' hh hok) ?_ ?_
  · exact write_rule boolT_adm p _ hh l .fls rfl (WorldAdm_trunc _ hadm)
      (HeapOk_trunc p W' hh hok) hl2 hag2 (Or.inr rfl)
  · intro i hi W'' hW'' hadm'' h'' u hok'' hu
    have hu' : u = .nul := hu
    subst hu'
    exact closure_read i W'' h'' (refT_transfer hrp i hi W'' hW'') hadm'' hok'' .nul rfl

/-! ## `Safe` is doing real work -/


def badFn : Tm := .lam (.app .nul .nul)

theorem badFn_not_in_arrow : ¬ arrowT nulT nulT 3 (ofList []) badFn := by
  intro hb
  have h2 := hb.2 2 (by omega) (ofList []) (by rw [trunc_nil]; exact WExt_refl _)
    WorldAdm_nil [] (emptyHeapOk 2) .nul rfl
  rcases h2 with ⟨hv, -⟩ | ⟨W'', h', t', -, -, hstep, -, hsafe⟩
  · simp [isVal] at hv
  · cases hstep with
    | appL hs => exact lam_no_step hs
    | appR _ hs => exact nul_no_step hs
    | beta _ =>
      rcases hsafe with ⟨hv, -⟩ | ⟨W3, h3, t3, -, -, hstep3, -, -⟩
      · simp [subst, isVal] at hv
      · cases hstep3 with
        | appL hs => exact nul_no_step hs
        | appR _ hs => exact nul_no_step hs



end ExperimentState
end Verification
