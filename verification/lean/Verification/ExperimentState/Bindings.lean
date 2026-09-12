import Verification.ExperimentState.Language

/-!
# Binding discipline

`Scoped d t` says that the free de Bruijn indices of `t` are below `d`.
Unlike `isVal`, it rules out callable code containing free variables. Substitution
in the machine is valid for closed arguments; the lemmas here state that
precondition explicitly.
-/
namespace Verification.ExperimentState

def Scoped (d : Nat) : Tm → Prop
  | .var i => i < d
  | .obj _ .absent => True
  | .obj _ (.closure b) => Scoped (d + 1) b
  | .attach b a => Scoped (d + 1) b ∧ Scoped d a
  | .letE a b => Scoped d a ∧ Scoped (d + 1) b
  | .app f a => Scoped d f ∧ Scoped d a
  | .alloc a | .read a | .test _ a => Scoped d a
  | .write a b => Scoped d a ∧ Scoped d b
  | .ite c a b => Scoped d c ∧ Scoped d a ∧ Scoped d b
  | _ => True

theorem Scoped.mono {t : Tm} {d e : Nat} (h : Scoped d t) (hde : d ≤ e) :
    Scoped e t := by
  induction t using Tm.induct generalizing d e <;> simp only [Scoped] at *
  case var i => omega
  case objClosure l b ih => exact ih h (by omega)
  case app f a ihf iha => exact ⟨ihf h.1 hde, iha h.2 hde⟩
  case letE a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 (by omega)⟩
  case attach f a ihf iha => exact ⟨ihf h.1 (by omega), iha h.2 hde⟩
  case write a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 hde⟩
  case ite c a b ihc iha ihb => exact ⟨ihc h.1 hde, iha h.2.1 hde, ihb h.2.2 hde⟩
  case alloc a ih => exact ih h hde
  case read a ih => exact ih h hde
  case test k a ih => exact ih h hde
  all_goals trivial

theorem subst_above {t : Tm} {d j : Nat} (h : Scoped d t) (hj : d ≤ j) (a : Tm) :
    subst j a t = t := by
  induction t using Tm.induct generalizing d j <;> simp only [Scoped, subst] at *
  case var i => simp [show i ≠ j by omega, show ¬j < i by omega]
  case objClosure l b ih => rw [ih h (by omega)]
  case app f b ihf ihb => rw [ihf h.1 hj, ihb h.2 hj]
  case letE x b ihx ihb => rw [ihx h.1 hj, ihb h.2 (by omega)]
  case attach f b ihf ihb => rw [ihf h.1 (by omega), ihb h.2 hj]
  case write b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case ite c b e ihc ihb ihe => rw [ihc h.1 hj, ihb h.2.1 hj, ihe h.2.2 hj]
  case alloc b ih => rw [ih h hj]
  case read b ih => rw [ih h hj]
  case test k b ih => rw [ih h hj]
  all_goals rfl

theorem Scoped.closed {t : Tm} (h : Scoped 0 t) : Closed t :=
  fun j a => subst_above h (Nat.zero_le j) a

theorem subst_scoped {t a : Tm} {d j : Nat} (ht : Scoped (d + 1) t)
    (ha : Scoped 0 a) (hj : j ≤ d) : Scoped d (subst j a t) := by
  induction t using Tm.induct generalizing d j <;> simp only [Scoped, subst] at *
  case var i =>
    split
    · exact ha.mono (Nat.zero_le d)
    · rename_i hn
      have hne : i ≠ j := by simpa using hn
      split <;> simp only [Scoped] <;> omega
  case objClosure l b ih => exact ih ht (by omega)
  case app f b ihf ihb => exact ⟨ihf ht.1 hj, ihb ht.2 hj⟩
  case letE x b ihx ihb => exact ⟨ihx ht.1 hj, ihb ht.2 (by omega)⟩
  case attach f b ihf ihb => exact ⟨ihf ht.1 (by omega), ihb ht.2 hj⟩
  case write b c ihb ihc => exact ⟨ihb ht.1 hj, ihc ht.2 hj⟩
  case ite c b e ihc ihb ihe => exact ⟨ihc ht.1 hj, ihb ht.2.1 hj, ihe ht.2.2 hj⟩
  case alloc b ih => exact ih ht hj
  case read b ih => exact ih ht hj
  case test k b ih => exact ih ht hj
  all_goals trivial

abbrev Env := Nat → Tm

def push (a : Tm) (ρ : Env) : Env
  | 0 => a
  | i + 1 => ρ i

/-- Simultaneous closing substitution, leaving `d` enclosing binders intact. -/
def instantiate (d : Nat) (ρ : Env) : Tm → Tm
  | .var i => if i < d then .var i else ρ (i - d)
  | .letE a b => .letE (instantiate d ρ a) (instantiate (d + 1) ρ b)
  | .obj l .absent => .obj l .absent
  | .obj l (.closure b) => .obj l (.closure (instantiate (d + 1) ρ b))
  | .app f a => .app (instantiate d ρ f) (instantiate d ρ a)
  | .attach b a => .attach (instantiate (d + 1) ρ b) (instantiate d ρ a)
  | .alloc a => .alloc (instantiate d ρ a)
  | .read a => .read (instantiate d ρ a)
  | .write a b => .write (instantiate d ρ a) (instantiate d ρ b)
  | .test k a => .test k (instantiate d ρ a)
  | .ite c a b => .ite (instantiate d ρ c) (instantiate d ρ a) (instantiate d ρ b)
  | t => t

theorem instantiate_scoped (ρ : Env) (hρ : ∀ i, Scoped 0 (ρ i)) (t : Tm) (d : Nat) :
    Scoped d (instantiate d ρ t) := by
  induction t using Tm.induct generalizing d <;> simp only [instantiate, Scoped] at *
  case var i => split <;> first | assumption | exact (hρ _).mono (Nat.zero_le d)
  case objClosure l b ih => exact ih _
  case app f a ihf iha => exact ⟨ihf _, iha _⟩
  case letE a b iha ihb => exact ⟨iha _, ihb _⟩
  case attach f a ihf iha => exact ⟨ihf _, iha _⟩
  case write a b iha ihb => exact ⟨iha _, ihb _⟩
  case ite c a b ihc iha ihb => exact ⟨ihc _, iha _, ihb _⟩
  case alloc a ih => exact ih d
  case read a ih => exact ih d
  case test k a ih => exact ih d
  all_goals trivial

/-- Closing a lambda and applying it agrees with extending its environment. -/
theorem instantiate_beta (ρ : Env) (hρ : ∀ i, Scoped 0 (ρ i)) (a t : Tm) (d : Nat) :
    subst d a (instantiate (d + 1) ρ t) = instantiate d (push a ρ) t := by
  induction t using Tm.induct generalizing d <;> simp only [instantiate, subst] at *
  case var i =>
    by_cases h : i < d
    · simp [show i < d + 1 by omega, h, subst, show i ≠ d by omega, show ¬d < i by omega]
    · by_cases he : i = d
      · subst i; simp [subst, push]
      · have hi : ¬ i < d + 1 := by omega
        have heq : i - d = (i - (d + 1)) + 1 := by omega
        simp only [if_neg hi, if_neg h, heq, push]
        exact (hρ _).closed d a
  case objClosure l b ih => rw [ih]
  case app f b ihf ihb => rw [ihf, ihb]
  case letE a b iha ihb => rw [iha, ihb]
  case attach f b ihf ihb => rw [ihf, ihb]
  case write b c ihb ihc => rw [ihb, ihc]
  case ite c b e ihc ihb ihe => rw [ihc, ihb, ihe]
  case alloc b ih => rw [ih]
  case read b ih => rw [ih]
  case test k b ih => rw [ih]
  all_goals rfl

/-- Put parameters in declaration order before the captured environment.
Slot zero is the first parameter, not the last argument evaluated. -/
def prependArgs (args : List Tm) (ρ : Env) : Env := args.foldr push ρ

theorem prependArgs_scoped (hargs : ∀ a ∈ args, Scoped 0 a)
    (hρ : ∀ i, Scoped 0 (ρ i)) : ∀ i, Scoped 0 (prependArgs args ρ i) := by
  induction args with
  | nil => exact hρ
  | cons a args ih =>
    intro i
    cases i with
    | zero => exact hargs a (by simp)
    | succ i => exact ih (fun a ha => hargs a (by simp [ha])) i

/-- Closing captures and then binding any number of parameters agrees with a
single simultaneous substitution. The theorem includes nested closure bodies. -/
theorem instantiate_args (ρ : Env) (hρ : ∀ i, Scoped 0 (ρ i))
    (hargs : ∀ a ∈ args, Scoped 0 a) (t : Tm) (d : Nat) :
    bindArgs d args (instantiate (d + args.length) ρ t) =
      instantiate d (prependArgs args ρ) t := by
  induction args generalizing d with
  | nil => simp [bindArgs, prependArgs]
  | cons a args ih =>
    have hrest : ∀ a ∈ args, Scoped 0 a := fun a ha => hargs a (by simp [ha])
    have level : d + (a::args).length = (d + 1) + args.length := by simp; omega
    simp only [bindArgs, level]
    rw [ih hrest (d + 1)]
    exact instantiate_beta _ (prependArgs_scoped hrest hρ) a t d

theorem instantiate_above {t : Tm} {d : Nat} (ht : Scoped d t) (ρ : Env) :
    instantiate d ρ t = t := by
  induction t using Tm.induct generalizing d <;> simp only [Scoped, instantiate] at *
  case var i => simp [ht]
  case objClosure l b ih => rw [ih ht]
  case app f a ihf iha => rw [ihf ht.1, iha ht.2]
  case letE a b iha ihb => rw [iha ht.1, ihb ht.2]
  case attach f a ihf iha => rw [ihf ht.1, iha ht.2]
  case write a b iha ihb => rw [iha ht.1, ihb ht.2]
  case ite c a b ihc iha ihb => rw [ihc ht.1, iha ht.2.1, ihb ht.2.2]
  case alloc a ih => rw [ih ht]
  case read a ih => rw [ih ht]
  case test k a ih => rw [ih ht]
  all_goals rfl

/-- Binding closed arguments closes exactly their parameter slots, leaving the
specified enclosing binders. Captures were already closed by the descriptor. -/
theorem bindArgs_scoped (ht : Scoped (d + args.length) t)
    (hargs : ∀ a ∈ args, Scoped 0 a) : Scoped d (bindArgs d args t) := by
  let ρ : Env := fun _ => .nul
  have hρ : ∀ i, Scoped 0 (ρ i) := fun _ => trivial
  rw [← instantiate_above ht ρ, instantiate_args ρ hρ hargs]
  exact instantiate_scoped _ (prependArgs_scoped hargs hρ) t d

#print axioms instantiate_args
#print axioms bindArgs_scoped

end Verification.ExperimentState
