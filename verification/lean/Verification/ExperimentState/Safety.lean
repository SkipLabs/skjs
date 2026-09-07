import Verification.ExperimentState.Heaps
/-!
# Safety and function types

`Safe T n W h t` says that running `t` for `n` steps never gets stuck, and that
if it reaches a value with budget left, that value is in `T`. Each step spends a
level and the world drops with it; the world reached after a step must extend the
truncation of the one before, and must itself be admissible.

A function type is then safety in every *future* world and every heap satisfying
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

/-- `A → B` over these worlds: safe in every future world and every heap
satisfying it, at every strictly smaller level. -/
def arrowT (A B : Fam) : Fam := fun k W v =>
  (∃ b, v = .lam b) ∧
    ∀ (j : Nat) (hj : j < k) (W' : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) W' →
      WorldAdm W' → ∀ (h : Heap), HeapOk j W' h → ∀ a, A j W' a → Safe B j W' h (.app v a)

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
  rintro _ _ _ ⟨⟨b, rfl⟩, -⟩; rfl

end ExperimentState
end Verification
