import Verification.ExperimentState.Worlds
/-!
# Semantic types

A type is a family of approximations indexed by a budget, judged against a world
of the same level. `Adm` says which families are types: downward closed with the
world truncated to match, and stable under the world growing.

A reference is built from a *semantic* element type and compares the stored
contract with it at strictly lower budget. Nothing syntactic is involved, so a
type parameter under a reference is interpreted rather than ignored --
`ref_param_universal` -- which is the failure that motivated worlds in the first
place.

Because a reference reads its element type only below the current budget it is a
**guard**, so `refT` is contractive and the guarded fixed point applies: the
tower `⊤, F ⊤, F (F ⊤), …` stabilises below its own height, its diagonal is
coherent, and that diagonal is a fixed point. This is Banach's theorem on a
space where distance is the first budget at which two families disagree, and it
needs no monotonicity -- which is how it survives recursion through negative
positions.

The fixed point is also *unique*: any family satisfying the equation is it. So a
recursive type is determined by its equation rather than merely solving it, and
two spellings of one recursion are the same type.
-/
namespace Verification
namespace ExperimentState

abbrev Fam := (k : Nat) → WorldT k → Val → Prop

/-- Every semantic type restricts to a contract at any level. No approximation
is lost: the restriction just refuses to be asked above its level. -/
def res {k : Nat} (T : Fam) : Ctr k := fun j _ W' v => T j W' v

/-- **A reference, built from a semantic element type.** The stored contract is
compared with the element family itself, at strictly lower budget. Taking the
element type semantically rather than syntactically is what makes the clause
depend on the environment interpreting it, so a type parameter under a
reference is interpreted rather than ignored. -/
def refT (T : Fam) : Fam := fun k W v =>
  ∃ (l : Nat) (c : Ctr k), v = .loc l ∧ lookup W l = some c ∧
    ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ T j W' u

def nulT : Fam := fun _ _ v => v = .nul

/-- A cell that can actually change observably. -/
def boolT : Fam := fun _ _ v => v = .tru ∨ v = .fls

/-! ### A rigid parameter under a reference -/


theorem ref_param_inhabited (F : Fam) (k : Nat) :
    refT F k (ofList [res F]) (.loc 0) :=
  ⟨0, res F, rfl, by simp [lookup], fun _ _ _ _ => Iff.rfl⟩

theorem ref_param_universal :
    ∀ (F : Fam) (k : Nat), ∃ (W : WorldT k) (v : Val), refT F k W v :=
  fun F k => ⟨ofList [res F], .loc 0, ref_param_inhabited F k⟩

/-! ## The guarded fixed point -/


def topF : Fam := fun _ _ _ => True

def Agree (T U : Fam) (n : Nat) : Prop := ∀ m, m < n → ∀ W v, T m W v ↔ U m W v

def Contractive (F : Fam → Fam) : Prop :=
  ∀ n T U, Agree T U n → ∀ W v, F T n W v ↔ F U n W v

def iter (F : Fam → Fam) : Nat → Fam
  | 0 => topF
  | k + 1 => F (iter F k)

def fixF (F : Fam → Fam) : Fam := fun n => iter F (n + 1) n

private theorem natStrong {G : Nat → Prop} (h : ∀ n, (∀ m, m < n → G m) → G n) :
    ∀ n, G n := by
  have aux : ∀ n, ∀ m, m < n → G m := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ k ih =>
      intro m hm
      by_cases hk : m = k
      · subst hk; exact h m ih
      · exact ih m (by omega)
  exact fun n => h n (aux n)

theorem iter_stable (F : Fam → Fam) (hF : Contractive F) :
    ∀ m k j, m < k → m < j → ∀ W v, iter F k m W v ↔ iter F j m W v := by
  refine natStrong ?_
  intro m ih k j hk hj W v
  cases k with
  | zero => omega
  | succ k' =>
    cases j with
    | zero => omega
    | succ j' =>
      show F (iter F k') m W v ↔ F (iter F j') m W v
      exact hF m _ _ (fun m' hm' W' v' => ih m' hm' k' j' (by omega) (by omega) W' v') W v

theorem fix_unfold (F : Fam → Fam) (hF : Contractive F) (n : Nat) (W : WorldT n) (v : Val) :
    fixF F n W v ↔ F (fixF F) n W v := by
  show F (iter F n) n W v ↔ F (fixF F) n W v
  exact hF n _ _ (fun m hm W' v' => iter_stable F hF m n (m + 1) hm (by omega) W' v') W v

/-- A reference reads its element type only strictly below the current level,
so it is a guard. -/
theorem refT_contractive : Contractive refT := by
  intro n T U hag W v
  simp only [refT]
  constructor <;> rintro ⟨l, c, rfl, hl, h⟩ <;> refine ⟨l, c, rfl, hl, ?_⟩ <;>
      intro j hj W' u
  · exact (h j hj W' u).trans (hag j hj W' u)
  · exact (h j hj W' u).trans (hag j hj W' u).symm

/-- **The fixed point is unique.** Any family satisfying the equation *is* it,
so a recursive type is determined by its equation and not merely a solution of
it. -/
theorem fix_unique (F : Fam → Fam) (hF : Contractive F) (U : Fam)
    (hU : ∀ (n : Nat) (W : WorldT n) (v : Val), U n W v ↔ F U n W v) :
    ∀ (n : Nat) (W : WorldT n) (v : Val), U n W v ↔ fixF F n W v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W v
    rw [hU n W v, fix_unfold F hF n W v]
    exact hF n U (fixF F) (fun m hm W' v' => ih m hm W' v') W v

/-! ## `R = ref R` -/


def R : Fam := fixF refT

theorem R_unfold (n : Nat) (W : WorldT n) (v : Val) : R n W v ↔ refT R n W v :=
  fix_unfold refT refT_contractive n W v

/-- Inhabited by a genuinely cyclic world: one location whose contract is `R`
itself, holding a reference to that same location. -/
theorem R_cyclic (n : Nat) : R n (ofList [res R]) (.loc 0) :=
  (R_unfold n _ _).mpr ⟨0, res R, rfl, by simp [lookup], fun _ _ _ _ => Iff.rfl⟩

/-- And `R` is not everything: a non-location is excluded at every level. -/
theorem R_not_trivial (n : Nat) (W : WorldT n) : ¬ R n W .nul := by
  intro h
  obtain ⟨l, c, hv, -, -⟩ := (R_unfold n W _).mp h
  exact absurd hv (by simp)

/-- A reference respects equality of its element type. -/
theorem refT_congr {A B : Fam} (h : ∀ (n : Nat) (W : WorldT n) (v : Val), A n W v ↔ B n W v) :
    ∀ (n : Nat) (W : WorldT n) (v : Val), refT A n W v ↔ refT B n W v :=
  fun n => refT_contractive n A B (fun m _ W v => h m W v)

theorem refT_refT_contractive : Contractive (fun X => refT (refT X)) := by
  intro n T U hag W v
  exact refT_contractive n (refT T) (refT U)
    (fun m hm => refT_contractive m T U (fun m' hm' => hag m' (by omega))) W v

/-- **`μX. ref X` and `μX. ref (ref X)` are the same type**: an instance of
uniqueness, and the smallest case where two spellings of one recursive type
must be identified. -/
theorem R_eq_ref_ref :
    ∀ (n : Nat) (W : WorldT n) (v : Val), R n W v ↔ fixF (fun X => refT (refT X)) n W v := by
  refine fix_unique _ refT_refT_contractive R ?_
  intro n W v
  exact (R_unfold n W v).trans
    (refT_contractive n R (refT R) (fun m _ W' v' => R_unfold m W' v') W v)

/-- Allocation cannot invalidate a reference claim: a future world keeps every
contract it already had. -/
theorem refT_mono (T : Fam) (k : Nat) (W W' : WorldT k) (h : WExt W W') (v : Val)
    (hv : refT T k W v) : refT T k W' v := by
  obtain ⟨l, c, rfl, hl, hag⟩ := hv
  obtain ⟨tail, ht⟩ := h
  refine ⟨l, c, rfl, ?_, hag⟩
  simp only [lookup] at hl ⊢
  rw [ht]
  have := (List.getElem?_eq_some_iff.mp hl).1
  simpa [List.getElem?_append, this] using hl

/-! ## Admissibility -/


structure Adm (T : Fam) : Prop where
  down : ∀ (n : Nat) (W : WorldT (n + 1)) (v : Val),
    T (n + 1) W v → T n (trunc n (Nat.le_succ n) W) v
  mono : ∀ (n : Nat) (W W' : WorldT n), WExt W W' → ∀ v, T n W v → T n W' v

theorem nulT_adm : Adm nulT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem boolT_adm : Adm boolT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem topF_adm : Adm topF := ⟨fun _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩

/-- A reference is admissible whatever its element type is: the level drop is
absorbed by restricting the stored contract, and allocation only appends. -/
theorem refT_adm (T : Fam) : Adm (refT T) := by
  refine ⟨?_, fun n W W' hx v hv => refT_mono T n W W' hx v hv⟩
  rintro n W v ⟨l, c, rfl, hl, hag⟩
  refine ⟨l, _, rfl, lookup_trunc (Nat.le_succ n) W l c hl, ?_⟩
  intro j hj W' u
  exact hag j (by omega) W' u

theorem iter_adm (F : Fam → Fam) (hF : ∀ T, Adm T → Adm (F T)) : ∀ k, Adm (iter F k)
  | 0 => topF_adm
  | k + 1 => hF _ (iter_adm F hF k)

theorem fix_adm (F : Fam → Fam) (hC : Contractive F) (hF : ∀ T, Adm T → Adm (F T)) :
    Adm (fixF F) := by
  constructor
  · intro n W v hv
    have h1 : iter F (n + 2) n (trunc n (Nat.le_succ n) W) v :=
      (iter_adm F hF (n + 2)).down n W v hv
    exact (iter_stable F hC n (n + 2) (n + 1) (by omega) (by omega) _ v).mp h1
  · intro n W W' hx v hv
    exact (iter_adm F hF (n + 1)).mono n W W' hx v hv

theorem R_adm : Adm R := fix_adm refT refT_contractive (fun T _ => refT_adm T)

theorem Adm.down_le {A : Fam} (hA : Adm A) :
    ∀ (n i : Nat) (h : i ≤ n) (W : WorldT n) (v : Val), A n W v → A i (trunc i h W) v := by
  intro n
  induction n with
  | zero =>
    intro i h W v hv
    have hi : i = 0 := by omega
    subst hi; rw [trunc_id]; exact hv
  | succ p ih =>
    intro i h W v hv
    by_cases hip : i = p + 1
    · subst hip; rw [trunc_id]; exact hv
    · have hle : i ≤ p := by omega
      have := ih i hle (trunc p (Nat.le_succ p) W) v (hA.down p W v hv)
      rwa [trunc_trunc] at this

/-! ## Types whose members are values -/


/-- A type whose members are values. Needed wherever a term must beta-reduce or
be stored. -/
def ValOnly (A : Fam) : Prop := ∀ (j : Nat) (W : WorldT j) (a : Val), A j W a → isVal a = true

theorem nulT_valOnly : ValOnly nulT := by rintro _ _ _ rfl; rfl

theorem boolT_valOnly : ValOnly boolT := by rintro _ _ _ (rfl | rfl) <;> rfl

theorem refT_valOnly (A : Fam) : ValOnly (refT A) := by
  rintro _ _ _ ⟨l, c, rfl, -, -⟩; rfl

/-- Restricting a semantic type to a contract is level-independent. -/
theorem trunc_res {k j : Nat} (h : j ≤ k) (T : Fam) :
    trunc j h (ofList [res T]) = ofList [res T] := by
  simp only [trunc, toList_ofList, List.map_cons, List.map_nil]
  rfl

end ExperimentState
end Verification
