import Verification.ExperimentState.Rules
/-!
# Worked examples

Three things are checked here. That a recursive *function* type behaves --
`μX. X → null` exercises the guarded fixed point with recursion in an
argument position, where a monotonicity-based construction is unavailable. That a closure over a mutable cell stays
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

theorem Rf_callable {n W t} (h : Rf n W t) : Callable t :=
  ((Rf_unfold n W t).mp h).1

def hFn : Tm := .fn 0 .nul

/-- Slot 0 is the receiver, slot 1 the argument. -/
def kFn : Tm := .fn 0 (.app (.var 1) hFn)

theorem Rf_adm : Adm Rf := fix_adm _ (arrowT_contractive nulT) (fun _ _ => arrowT_adm _ _)

theorem Rf_valOnly : ValOnly Rf := fun n W v h =>
  arrowT_valOnly _ _ n W v ((Rf_unfold n W v).mp h)

theorem hFn_in_Rf (n : Nat) (W : WorldT n) : Rf n W hFn := by
  apply (Rf_unfold n W hFn).mpr
  apply fn_intro _ _ _ (by simp [Scoped])
  intro j hj U hx hu h hh a ha
  exact Safe_nul j U h

theorem kFn_in_Rf (n : Nat) (W : WorldT n) : Rf n W kFn := by
  apply (Rf_unfold n W kFn).mpr
  apply fn_intro _ _ _ (by simp [Scoped, hFn])
  intro j hj U hx hu h hh a ha
  -- The argument is a closed value, so binding the receiver after it leaves it.
  have hs : Scoped 0 a := (Rf_callable ha).invocable.scoped
  have ht : subst 0 Tm.undef (subst 1 a (.app (.var 1) hFn)) = .app a hFn := by
    simp [subst, hFn, subst_above hs (Nat.zero_le 0)]
  rw [ht]
  exact app_elim Rf_adm Rf_valOnly ((Rf_unfold j U a).mp ha) (hFn_in_Rf j U) hu hh

/-! ## A closure over a mutable cell -/


/-- `capFn` ignores its argument and reads location 0. -/
def capFn : Tm := .fn 0 (.read (.obj 0 .absent))

/-- It inhabits `null → null` against any world extending one that declares
location 0 to hold `null` -- **in every heap satisfying that world**, not in one
particular heap. -/
theorem capFn_in_arrow (n : Nat) : arrowT nulT nulT n (ofList [res nulT]) capFn := by
  apply fn_intro _ _ _ (by trivial)
  intro j hj U hx hu heap hh a ha
  have hl : lookup U 0 = some (res nulT) := by
    rw [trunc_res] at hx
    exact WExt_lookup hx (by simp [lookup])
  exact read_rule nulT_valOnly j U heap 0 hu hh (lookup_value 0) hl (fun _ _ _ _ => Iff.rfl)

/-- **And it survives an alias writing to that cell.** The write preserves heap
satisfaction, and `capFn`'s safety was stated against satisfaction rather than
against a particular heap -- so the closure is still safe in the new one. -/
theorem capFn_survives_alias_write (n j : Nat) (hj : j < n) (W' : WorldT j) (h : Heap)
    (hW : WExt (trunc j (Nat.le_of_lt hj) (ofList [res nulT])) W')
    (hadm : WorldAdm W') (hok : HeapOk j W' h) (c : Ctr j) (hl : lookup W' 0 = some c)
    (hv : ∀ (i : Nat) (hi : i < j), c i hi (trunc i (Nat.le_of_lt hi) W') .nul) :
    Safe nulT j W' (h.set 0 .nul) (.app capFn .nul) :=
  app_elim nulT_adm nulT_valOnly
    ((arrowT_adm nulT nulT).mono j _ W' hW _
      ((arrowT_adm nulT nulT).down_le n j (Nat.le_of_lt hj) _ _ (capFn_in_arrow n)))
    rfl hadm (write_sound j W' h 0 c .nul hok hl hv)

/-! ## The combination

    let r = alloc true in
    (fun _ => read r) (write r false)

Allocate a cell, change it through one reference, read it through a closure that
captured another. -/


/-- Under `[this, x]` and then the enclosing frame `[this, r]`: `r` is slot 3. -/
def inner : Tm := .fn 0 (.read (.var 3))

def body : Tm := .app inner (.write (.var 1) .fls)

def prog : Tm := .app (.fn 0 body) (.alloc .tru)

/-- Reading through the captured closure, at any level and admissible world in
which the cell is a boolean reference. -/
theorem closure_read {flds : List (String × Nat)} : ∀ (j : Nat) (W : WorldT j) (h : Heap),
    refT boolT j W (.objAt flds .absent) → WorldAdm W → HeapOk j W h →
    ∀ v, isVal v = true → Safe boolT j W h (.app (.fn 0 (.read (.objAt flds .absent))) v) := by
  intro j W h hr hadm hok v hv
  cases j with
  | zero => trivial
  | succ r =>
    refine beta_rule _ v hv r W h hadm hok ?_
    have hr' := refT_transfer hr r (Nat.le_succ r) _ (WExt_refl _)
    obtain ⟨flds', l, c, hvl, hf, hl, hag⟩ := refT_iff.mp hr'
    injection hvl with hll
    subst hll
    exact read_rule boolT_valOnly r _ h l (WorldAdm_trunc _ hadm)
      (HeapOk_trunc r W h hok) hf hl hag

/-- **The target.** -/
theorem prog_safe : ∀ (n : Nat) (W : WorldT n) (h : Heap),
    WorldAdm W → HeapOk n W h → Safe boolT n W h prog := by
  intro n W h hadm hok
  refine Safe_bind_appR (A := refT boolT) _ rfl n W h _ hadm hok
    (alloc_rule boolT_adm n W h .tru rfl hadm hok (Or.inl rfl)) ?_
  intro j _ W' _ hadm' h' v hok' hv
  obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ := refT_iff.mp hv
  have hr : refT boolT j W' (.objAt flds .absent) := refT_iff.mpr ⟨flds, l, c, rfl, hf, hl, hag⟩
  cases j with
  | zero => trivial
  | succ q =>
    refine beta_rule _ _ rfl q W' h' hadm' hok' ?_
    show Safe boolT q _ h'
      (.app (.fn 0 (.read (.objAt flds .absent))) (.write (.objAt flds .absent) .fls))
    have hrq : refT boolT q (trunc q (Nat.le_succ q) W') (.objAt flds .absent) :=
      refT_transfer hr q (Nat.le_succ q) _ (WExt_refl _)
    obtain ⟨flds2, l2, c2, hvl2, hf2, hl2, hag2⟩ := refT_iff.mp hrq
    injection hvl2 with hll2
    subst hll2
    refine Safe_bind_appR (A := nulT) _ rfl q _ h' _ (WorldAdm_trunc _ hadm')
      (HeapOk_trunc q W' h' hok') ?_ ?_
    · exact write_rule boolT_adm q _ h' l2 .fls rfl (WorldAdm_trunc _ hadm')
        (HeapOk_trunc q W' h' hok') hf2 hl2 hag2 (Or.inr rfl)
    · intro i hi W'' hW'' hadm'' h'' u hok'' hu
      have hu' : u = .nul := hu
      subst hu'
      exact closure_read i W'' h''
        (refT_transfer hrq i hi W'' hW'') hadm'' hok'' .nul rfl

/-- **The mutation is observable.** The program allocates `true`, overwrites it
through one reference, and the closure reads `false` back -- so the cell's
contents really change, rather than being rewritten with the value they had. -/
theorem prog_runs :
    Step [] prog [.tru] (.app (.fn 0 body) (.obj 0 .absent)) ∧
      Step [.tru] (.app (.fn 0 body) (.obj 0 .absent)) [.tru]
        (.app (.fn 0 (.read (.obj 0 .absent))) (.write (.obj 0 .absent) .fls)) ∧
      Step [.tru] (.app (.fn 0 (.read (.obj 0 .absent))) (.write (.obj 0 .absent) .fls)) [.fls]
        (.app (.fn 0 (.read (.obj 0 .absent))) .nul) ∧
      Step [.fls] (.app (.fn 0 (.read (.obj 0 .absent))) .nul) [.fls] (.read (.obj 0 .absent)) ∧
      Step [.fls] (.read (.obj 0 .absent)) [.fls] .fls :=
  ⟨.appR rfl (.makeV rfl), .beta rfl, .appR rfl (.writeV rfl (by simp)),
    .beta rfl, .readV rfl⟩

/-- And the whole thing really is a function of that type. -/
theorem prog_lam_arrow (k : Nat) (W : WorldT k) :
    arrowT (refT boolT) boolT k W (.fn 0 body) := by
  apply fn_intro _ _ _ (by simp [body, inner, Scoped])
  intro p hp U hx hu heap hh a ha
  obtain ⟨flds, l, c, rfl, hf, hl, hc⟩ := refT_iff.mp ha
  have hr : refT boolT p U (.objAt flds .absent) := refT_iff.mpr ⟨flds, l, c, rfl, hf, hl, hc⟩
  change Safe boolT p U heap
    (.app (.fn 0 (.read (.objAt flds .absent))) (.write (.objAt flds .absent) .fls))
  apply Safe_bind_appR (A := nulT) _ rfl p U heap _ hu hh
    (write_rule boolT_adm p U heap l .fls rfl hu hh hf hl hc (Or.inr rfl))
  intro j hj V hV hVadm h' v hh' hv
  exact closure_read j V h' (refT_transfer hr j hj V hV) hVadm hh' v (nulT_valOnly _ _ _ hv)

/-! ## `Safe` is doing real work -/


def badFn : Tm := .fn 0 (.app .nul .nul)

theorem badFn_not_in_arrow : ¬ arrowT nulT nulT 2 (ofList []) badFn := by
  intro hb
  have hs := hb.2 1 (by omega) (ofList []) (by rw [trunc_nil]; exact WExt_refl _)
    WorldAdm_nil [] (emptyHeapOk 1) .nul rfl
  exact stuck_not_safe nulT 0 (ofList []) [] hs

end ExperimentState
end Verification
