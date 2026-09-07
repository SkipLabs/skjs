import Verification.ExperimentState.Safety

/-!
# The guarded fixed point, over any one-step semantics

A recursive type is interpreted as the limit of finite approximations. The
construction is independent of the node syntax: the operator must consult its
recursive arguments only strictly below the current budget (`LayerCongr`) and
preserve admissibility (`LayerAdm`). Positive graph interpretations supply
these two properties.
-/

namespace Verification
namespace ExperimentState
namespace Tower

/-- A set of nodes denotes the union of its members. -/
def setSem {ι : Type} (X : ι → Fam) (S : List ι) : Fam := fun n W v => ∃ i ∈ S, X i n W v

theorem setSem_congr {ι : Type} {X Y : ι → Fam} (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (S : List ι) : Agree (setSem X S) (setSem Y S) n := by
  intro m hm W v
  constructor <;> rintro ⟨i, hi, hd⟩
  · exact ⟨i, hi, (h i m hm W v).mp hd⟩
  · exact ⟨i, hi, (h i m hm W v).mpr hd⟩

theorem setSem_adm {ι : Type} {X : ι → Fam} (h : ∀ i, Adm (X i)) (S : List ι) :
    Adm (setSem X S) := by
  constructor
  · rintro n W v ⟨i, hi, hd⟩; exact ⟨i, hi, (h i).down n W v hd⟩
  · rintro n W W' hx v ⟨i, hi, hd⟩; exact ⟨i, hi, (h i).mono n W W' hx v hd⟩

/-- Contractivity, in the form the tower needs: agreement below the budget on
the operands is agreement on the result. -/
def LayerCongr {ι : Type} (F : (ι → Fam) → ι → Fam) : Prop :=
  ∀ (X Y : ι → Fam) (n : Nat), (∀ i, Agree (X i) (Y i) n) →
    ∀ (i : ι) (W : WorldT n) (v : Val), F X i n W v ↔ F Y i n W v

/-- Admissibility is preserved by one step. -/
def LayerAdm {ι : Type} (F : (ι → Fam) → ι → Fam) : Prop :=
  ∀ (X : ι → Fam), (∀ i, Adm (X i)) → ∀ i, Adm (F X i)

def approx {ι : Type} (F : (ι → Fam) → ι → Fam) : Nat → ι → Fam
  | 0 => fun _ => topF
  | k + 1 => F (approx F k)

theorem approx_stable {ι : Type} {F : (ι → Fam) → ι → Fam} (hF : LayerCongr F) (n : Nat) :
    ∀ k l, n < k → n < l → ∀ (i : ι) (W : WorldT n) (v : Val),
      approx F k i n W v ↔ approx F l i n W v := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k l hk hl i W v
    cases k with
    | zero => omega
    | succ k =>
      cases l with
      | zero => omega
      | succ l =>
        exact hF _ _ n (fun a m hm U u => ih m hm k l (by omega) (by omega) a U u) i W v

/-- The fixed point: a type at budget `n` is its `n+1`st approximation. -/
def denote {ι : Type} (F : (ι → Fam) → ι → Fam) (i : ι) : Fam := fun n => approx F (n + 1) i n

/-- **It satisfies its own equation.** -/
theorem denote_unfold {ι : Type} {F : (ι → Fam) → ι → Fam} (hF : LayerCongr F)
    (i : ι) (n : Nat) (W : WorldT n) (v : Val) :
    denote F i n W v ↔ F (denote F) i n W v :=
  hF _ _ n (fun a m hm U u => approx_stable hF m n (m + 1) hm (by omega) a U u) i W v

theorem approx_adm {ι : Type} {F : (ι → Fam) → ι → Fam} (hA : LayerAdm F) :
    ∀ k i, Adm (approx F k i)
  | 0, _ => topF_adm
  | k + 1, i => hA _ (approx_adm hA k) i

theorem denote_adm {ι : Type} {F : (ι → Fam) → ι → Fam} (hF : LayerCongr F) (hA : LayerAdm F)
    (i : ι) : Adm (denote F i) := by
  constructor
  · intro n W v hv
    have h1 := (approx_adm hA (n + 2) i).down n W v hv
    exact (approx_stable hF n (n + 2) (n + 1) (by omega) (by omega) i _ v).mp h1
  · intro n W W' hx v hv
    exact (approx_adm hA (n + 1) i).mono n W W' hx v hv

end Tower
end ExperimentState
end Verification
