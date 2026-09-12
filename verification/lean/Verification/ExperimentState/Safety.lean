import Verification.ExperimentState.Bindings
import Verification.ExperimentState.Heaps
/-!
# Safety and function types

`Safe T n W h t` says that running `t` for `n` steps never gets stuck, and that
if it reaches a value with budget left, that value is in `T`. Each step spends a
level and the world drops with it; the world reached after a step must extend the
truncation of the one before, and must itself be admissible.

A function type requires closed code, either a lambda or a function object, whose substituted body is safe in
every *future* world and every heap satisfying
it, at every strictly smaller budget. Requiring admissibility here is what lets a
function allocate: without it, a world carrying a contract like `badCtr` could be
supplied, and no allocating function would be safe anywhere.

The level a call spends is the level at which the argument's own guarantees are
available. That correspondence is what makes ordinary typing derivations go
through, and it is why the arrow is stated over `Safe` rather than over an
abstract relation from arguments to results.

Since safety consults a type only at the budgets it can still reach, an arrow
reads **both** of its operands strictly below the current budget. So a function
type is a guard in its result as well as its argument, and a recursion may run
through either position.
-/
namespace Verification
namespace ExperimentState

/-- Running `t` for `n` steps never gets stuck; each step spends a level, and
the world drops with it. -/
def Safe (T : Fam) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n + 1, W, h, t =>
      (isVal t = true ∧ T (n + 1) W t) ∨
      (∃ (W' : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) W' ∧ WorldAdm W' ∧ Step h t h' t' ∧
          HeapOk n W' h' ∧ Safe T n W' h' t')

theorem Safe_nul : ∀ (n : Nat) (W : WorldT n) (h : Heap), Safe nulT n W h .nul
  | 0, _, _ => trivial
  | _ + 1, _, _ => Or.inl ⟨rfl, rfl⟩

/-- The body executed after a call's beta step. This is a semantic helper,
not an additional runtime operation. Arrow membership separately requires a
callable shape, so the fallback branch is never used for typed application. -/
def callBody (v a : Tm) : Tm := match v with
  | .lam b | .obj _ (.lam b) => subst 0 a b
  | _ => .app .nul .nul

/-- Closed executable code, with or without an allocated object identity.
The lambda case supports administrative bindings; source function objects use
an immutable call slot. This predicate alone promises no bag invariant. -/
def Callable (v : Val) : Prop :=
  ∃ b, (v = .lam b ∨ ∃ l, v = .obj l (.lam b)) ∧ Scoped 1 b

theorem Callable.val {v : Val} (h : Callable v) : isVal v = true := by
  rcases h with ⟨b, (rfl | ⟨l, rfl⟩), _⟩ <;> rfl

theorem Callable.scoped {v : Val} (h : Callable v) : Scoped 0 v := by
  rcases h with ⟨b, (rfl | ⟨l, rfl⟩), hc⟩ <;> exact hc

theorem Callable.step {v a : Val} (h : Callable v) (ha : isVal a = true) (heap : Heap) :
    Step heap (.app v a) heap (callBody v a) := by
  rcases h with ⟨b, (rfl | ⟨l, rfl⟩), _⟩
  · exact .beta ha
  · exact .betaC ha

/-- `A → B` contains closed callables whose substituted bodies are safe in every
future world and satisfying heap, at every strictly smaller level. The actual
application pays beta before using this body guarantee. -/
def arrowT (A B : Fam) : Fam := fun k W v =>
  Callable v ∧
    ∀ (j : Nat) (hj : j < k) (W' : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) W' →
      WorldAdm W' → ∀ (h : Heap), HeapOk j W' h → ∀ a, A j W' a → Safe B j W' h (callBody v a)

theorem arrowT_contractive (B : Fam) : Contractive (fun X => arrowT X B) := by
  intro n T U hag W v
  simp only [arrowT]
  constructor <;> rintro ⟨hl, h⟩ <;> refine ⟨hl, ?_⟩ <;>
      intro j hj W' hW hadm hp hok a ha
  · exact h j hj W' hW hadm hp hok a ((hag j hj W' a).mpr ha)
  · exact h j hj W' hW hadm hp hok a ((hag j hj W' a).mp ha)

/-- Safety depends on the type only through its behaviour at the budgets it can
still reach. -/
theorem Safe_congr {B C : Fam} (n : Nat) (hag : Agree B C n) :
    ∀ (j : Nat), j < n → ∀ (W : WorldT j) (h : Heap) (t : Tm),
      Safe B j W h t ↔ Safe C j W h t := by
  intro j
  induction j with
  | zero => intro _ _ _ _; exact Iff.rfl
  | succ p ih =>
    intro hj W h t
    simp only [Safe]
    constructor <;> rintro (⟨hv, hB⟩ | ⟨W', h', t', hx, ha, hs, hok, hsafe⟩)
    · exact Or.inl ⟨hv, (hag (p + 1) hj W t).mp hB⟩
    · exact Or.inr ⟨W', h', t', hx, ha, hs, hok, (ih (by omega) W' h' t').mp hsafe⟩
    · exact Or.inl ⟨hv, (hag (p + 1) hj W t).mpr hB⟩
    · exact Or.inr ⟨W', h', t', hx, ha, hs, hok, (ih (by omega) W' h' t').mpr hsafe⟩

/-- Safety is monotone in the type, at every budget it can still reach. -/
theorem Safe_mono {B C : Fam} : ∀ (j : Nat),
    (∀ m, m ≤ j → ∀ (W : WorldT m) (v : Val), B m W v → C m W v) →
    ∀ (W : WorldT j) (h : Heap) (t : Tm), Safe B j W h t → Safe C j W h t := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _; trivial
  | succ p ih =>
    intro hbc W h t hs
    rcases hs with ⟨hv, hB⟩ | ⟨W', h', t', hx, ha, hst, hok, hsafe⟩
    · exact Or.inl ⟨hv, hbc (p + 1) (Nat.le_refl _) W t hB⟩
    · exact Or.inr ⟨W', h', t', hx, ha, hst, hok,
        ih (fun m hm => hbc m (by omega)) W' h' t' hsafe⟩

/-- An arrow is a guard in its **result** as well as its argument, so a
recursive type may run through either position. -/
theorem arrowT_cod_contractive (A : Fam) : Contractive (fun X => arrowT A X) := by
  intro n T U hag W v
  simp only [arrowT]
  constructor <;> rintro ⟨hl, hh⟩ <;> refine ⟨hl, ?_⟩ <;>
      intro j hj W'' hW hadm hp hok a ha
  · exact (Safe_congr n hag j hj W'' hp _).mp (hh j hj W'' hW hadm hp hok a ha)
  · exact (Safe_congr n hag j hj W'' hp _).mpr (hh j hj W'' hW hadm hp hok a ha)

/-- **Arrow types are admissible.** -/
theorem arrowT_adm (A B : Fam) : Adm (arrowT A B) := by
  constructor
  · rintro n W v ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro j hj W' hW hadm hp hok a ha
    refine h j (by omega) W' ?_ hadm hp hok a ha
    rwa [trunc_trunc] at hW
  · rintro n W W' hx v ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro j hj W'' hW hadm hp hok a ha
    exact h j hj W'' (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hW) hadm hp hok a ha

theorem arrowT_valOnly (A B : Fam) : ValOnly (arrowT A B) := by
  rintro _ _ _ ⟨hc, -⟩; exact hc.val

/-! ## Unions and the arrow

A union in the domain splits into an intersection of arrows. This equation
supports domain normalization. Unrestricted distribution in the result position
is not assumed. -/

theorem arrowT_union_dom (A B C : Fam) (k : Nat) (W : WorldT k) (v : Val) :
    arrowT (unionT A B) C k W v ↔ interT (arrowT A C) (arrowT B C) k W v := by
  simp only [arrowT, interT, unionT]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨⟨hl, ?_⟩, ⟨hl, ?_⟩⟩
    · intro j hj W' hW hadm hp hok a ha
      exact h j hj W' hW hadm hp hok a (Or.inl ha)
    · intro j hj W' hW hadm hp hok a ha
      exact h j hj W' hW hadm hp hok a (Or.inr ha)
  · rintro ⟨⟨hl, hA⟩, ⟨_, hB⟩⟩
    refine ⟨hl, ?_⟩
    intro j hj W' hW hadm hp hok a ha
    rcases ha with h | h
    · exact hA j hj W' hW hadm hp hok a h
    · exact hB j hj W' hW hadm hp hok a h

/-! ## Comparing two runs of one program

Two obligations discharged at the same world and heap are two runs of the *same*
program, so determinism makes them take the same steps. What they force about
the value it may return is then whatever both judgments force at the first
world — and no more, since the worlds diverge as soon as anything is allocated.
The subtype rules use a conservative syntactic sufficient condition for this
property. `ModelBoundaries.lean` records why unrestricted result intersection
is invalid; no decision procedure for exact cross-world compatibility is assumed. -/

def CrossCompatUpTo (n : Nat) (B C D : Fam) : Prop :=
  ∀ (j : Nat), j ≤ n → ∀ (W W' : WorldT j) (h : Heap), HeapOk j W h → HeapOk j W' h →
    ∀ (u : Val), B j W u → C j W' u → D j W u

theorem safe_cross_upto {B C D : Fam} : ∀ (n : Nat), CrossCompatUpTo n B C D →
    ∀ (W W' : WorldT n) (h : Heap) (t : Tm), HeapOk n W h → HeapOk n W' h →
      Safe B n W h t → Safe C n W' h t → Safe D n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _; trivial
  | succ p ih =>
    intro hc W W' h t hok hok'
    rintro (⟨hv1, hBv⟩ | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩)
      (⟨hv2, hCv⟩ | ⟨Z', h2, t2, -, -, hst2, hok2, hcont2⟩)
    · exact Or.inl ⟨hv1, hc (p + 1) (Nat.le_refl _) W W' h hok hok' t hBv hCv⟩
    · exact absurd hst2 (value_no_step hv1)
    · exact absurd hst1 (value_no_step hv2)
    · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
      exact Or.inr ⟨Z, h1, t1, hz, huz, hst1, hok1,
        ih (fun j hj => hc j (by omega)) Z Z' h1 t1 hok1 hok2 hcont1 hcont2⟩

/-! ## Overloaded function types

The intersection of finitely many arrows, with the shared callable-shape
condition factored out. `arrowsT [(A, B)]` is `arrowT A B`, and `arrowsT []` is
the type of all functions. This is the node a representation carrying
intersections has to have, so it comes with the same structural properties the
fixed point needs of `arrowT`. -/

def arrowsT (L : List (Fam × Fam)) : Fam := fun k W v =>
  Callable v ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
    WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' → ∀ (h : Heap), HeapOk j W' h →
      ∀ a, p.1 j W' a → Safe p.2 j W' h (callBody v a)

theorem arrowsT_singleton (A B : Fam) (k : Nat) (W : WorldT k) (v : Val) :
    arrowsT [(A, B)] k W v ↔ arrowT A B k W v := by
  constructor
  · rintro ⟨hl, h⟩
    exact ⟨hl, fun j hj W' hx hu hp hh a ha => h (A, B) (by simp) j hj W' hx hu hp hh a ha⟩
  · rintro ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro p hp
    rw [List.mem_singleton.mp hp]
    exact fun j hj W' hx hu hh hok a ha => h j hj W' hx hu hh hok a ha

/-- Membership in every conjunct is membership in the intersection. -/
theorem arrowsT_of_all {L : List (Fam × Fam)} {k : Nat} {W : WorldT k} {v : Val} {b : Tm}
    (hlam : v = .lam b) (hclosed : Scoped 1 b) (h : ∀ p ∈ L, arrowT p.1 p.2 k W v) : arrowsT L k W v :=
  ⟨⟨b, Or.inl hlam, hclosed⟩, fun p hp j hj W' hx hu hp' hok a ha => (h p hp).2 j hj W' hx hu hp' hok a ha⟩

theorem arrowsT_valOnly (L : List (Fam × Fam)) : ValOnly (arrowsT L) := by
  rintro j W a ⟨hc, -⟩
  exact hc.val

theorem arrowsT_adm (L : List (Fam × Fam)) : Adm (arrowsT L) := by
  constructor
  · rintro n W v ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro p hp j hj W' hx hu hh hok a ha
    exact h p hp j (by omega) W' (by rwa [trunc_trunc] at hx) hu hh hok a ha
  · rintro n W W' hx v ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro p hp j hj W'' hx' hu hh hok a ha
    exact h p hp j hj W'' (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hx') hu hh hok a ha

/-- The congruence the tower needs: agreement below the budget on every operand
is agreement on the type. -/
theorem arrowsT_congr {α : Type} (l : List α) (f g : α → Fam × Fam) {n : Nat}
    (h : ∀ x ∈ l, Agree (f x).1 (g x).1 n ∧ Agree (f x).2 (g x).2 n)
    (W : WorldT n) (v : Val) : arrowsT (l.map f) n W v ↔ arrowsT (l.map g) n W v := by
  constructor <;> rintro ⟨hl, hobl⟩ <;> refine ⟨hl, ?_⟩ <;>
      intro p hp j hj W' hx hu hh hok a ha
  · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hp
    obtain ⟨hd, hc⟩ := h x hx'
    have hcj : Agree (g x).2 (f x).2 (j + 1) := fun m hm U u => (hc m (by omega) U u).symm
    exact (Safe_congr (j + 1) hcj j (Nat.lt_succ_self j) W' hh _).mpr
      (hobl (f x) (List.mem_map_of_mem hx') j hj W' hx hu hh hok a ((hd j hj W' a).mpr ha))
  · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hp
    obtain ⟨hd, hc⟩ := h x hx'
    have hcj : Agree (f x).2 (g x).2 (j + 1) := fun m hm U u => hc m (by omega) U u
    exact (Safe_congr (j + 1) hcj j (Nat.lt_succ_self j) W' hh _).mpr
      (hobl (g x) (List.mem_map_of_mem hx') j hj W' hx hu hh hok a ((hd j hj W' a).mp ha))

theorem omega_safe (B : Fam) : ∀ (n : Nat) (W : WorldT n) (h : Heap),
    WorldAdm W → HeapOk n W h → Safe B n W h omegaTm := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ha hh
    exact Or.inr ⟨trunc n (Nat.le_succ n) W, h, omegaTm, WExt_refl _,
      WorldAdm_trunc _ ha, omega_step h, HeapOk_trunc n W h hh,
      ih _ h (WorldAdm_trunc _ ha) (HeapOk_trunc n W h hh)⟩

theorem value_safe (B : Fam) (n : Nat) (U : WorldT n) (h : Heap) (v : Val)
    (hv : isVal v = true) (hb : B n U v) : Safe B n U h v := by
  cases n with
  | zero => trivial
  | succ n => exact Or.inl ⟨hv, hb⟩

theorem safe_value_mem {B : Fam} {n : Nat} {U : WorldT (n+1)} {h : Heap} {v : Val}
    (hv : isVal v = true) (hs : Safe B (n+1) U h v) : B (n+1) U v := by
  rcases hs with ⟨_, hb⟩ | ⟨_, _, _, _, _, hs, _, _⟩
  · exact hb
  · exact False.elim (value_no_step hv hs)

end ExperimentState
end Verification
