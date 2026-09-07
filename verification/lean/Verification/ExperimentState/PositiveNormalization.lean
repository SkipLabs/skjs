import Verification.ExperimentState.ReferenceConjunctions

/-! Finite positive normalization with nonempty reference conjunctions. Operands
are parameters: normalization never distributes through invariant contracts or
arrow results. Taking operands to be graph-label lists supports recursive graphs.
-/
namespace Verification.ExperimentState.PositiveNormalization
open ReferenceConjunctions Tower

inductive Clause (α : Type) where
  | nul | bool
  | refs (first : α) (rest : List α)
  | arrs (arrows : List (α × α))
  | boolLit (value : Bool)
  deriving Repr, DecidableEq

def sem (X : α → Fam) : Clause α → Fam
  | .nul => nulT
  | .bool => boolT
  | .boolLit b => fun _ _ v => v = (if b then .tru else .fls)
  | .refs a bs => refsT (X a) (bs.map X)
  | .arrs L => arrowsT (L.map fun p => (X p.1, X p.2))

def semList (X : α → Fam) (L : List (Clause α)) : Fam := setSem (sem X) L

inductive Formula (α : Type) where
  | bot
  | atom (c : Clause α)
  | union (a b : Formula α)
  | inter (a b : Formula α)
  deriving Repr, DecidableEq

def eval (X : α → Fam) : Formula α → Fam
  | .bot => fun _ _ _ => False
  | .atom c => sem X c
  | .union a b => unionT (eval X a) (eval X b)
  | .inter a b => interT (eval X a) (eval X b)

/-- Intersection of clauses: preserve all constraints of the same shape. -/
def meet : Clause α → Clause α → List (Clause α)
  | .nul, .nul => [.nul]
  | .bool, .bool => [.bool]
  | .bool, .boolLit b | .boolLit b, .bool => [.boolLit b]
  | .boolLit a, .boolLit b => if a == b then [.boolLit a] else []
  | .refs a bs, .refs c ds => [.refs a (bs ++ c :: ds)]
  | .arrs L, .arrs M => [.arrs (L ++ M)]
  | _, _ => []

def meetLists (A B : List (Clause α)) : List (Clause α) :=
  A.flatMap fun a => B.flatMap fun b => meet a b

def normalize : Formula α → List (Clause α)
  | .bot => []
  | .atom c => [c]
  | .union a b => normalize a ++ normalize b
  | .inter a b => meetLists (normalize a) (normalize b)

private theorem singleton_sem (X : α → Fam) (c : Clause α) (n W v) :
    semList X [c] n W v ↔ sem X c n W v := by simp [semList, setSem]

private theorem nil_sem (X : α → Fam) (n W v) : ¬ semList X [] n W v := by
  simp [semList, setSem]

def shape : Clause α → Nat
  | .nul => 0 | .bool | .boolLit _ => 1 | .refs .. => 2 | .arrs .. => 3

def valueShape : Val → Nat
  | .nul => 0 | .tru | .fls => 1 | .loc _ => 2 | .lam _ => 3 | _ => 4

theorem sem_shape {X : α → Fam} {c : Clause α} {n W v}
    (h : sem X c n W v) : valueShape v = shape c := by
  cases c with
  | nul => cases h; rfl
  | bool => rcases h with h | h <;> cases h <;> rfl
  | boolLit b => cases b <;> cases h <;> rfl
  | refs a bs => obtain ⟨l, _, rfl, _⟩ := h.1; rfl
  | arrs L => obtain ⟨b, rfl, _⟩ := h.1; rfl

theorem meet_sound (X : α → Fam) (a b : Clause α) (n : Nat) (W : WorldT n) (v : Val) :
    semList X (meet a b) n W v ↔ interT (sem X a) (sem X b) n W v := by
  by_cases hs : shape a = shape b
  · cases a <;> cases b <;> simp only [shape] at hs
    all_goals try contradiction
    · simp [meet, singleton_sem, sem, interT]
    · simp [meet, singleton_sem, sem, interT]
    · rename_i b
      cases b <;> simp [meet, singleton_sem, sem, interT, boolT]
      all_goals intro hv; subst v; simp
    · simp only [meet, singleton_sem, sem, List.map_append, List.map_cons]
      exact merge _ _ _ _ n W v
    · simp only [meet, singleton_sem, sem, List.map_append]
      exact TypeAlgebra.overload_append _ _ n W v
    · rename_i b
      cases b <;> simp [meet, singleton_sem, sem, interT, boolT]
      all_goals intro hv; subst v; simp
    · rename_i b c
      cases b <;> cases c <;> simp [meet, sem, interT, semList, setSem]
      all_goals intro hv; subst v; simp
  · have hm : meet a b = [] := by
      cases a <;> cases b <;> simp_all [shape, meet]
    rw [hm]
    constructor
    · intro h; exact False.elim (nil_sem X n W v h)
    · rintro ⟨ha, hb⟩
      exact False.elim (hs ((sem_shape ha).symm.trans (sem_shape hb)))

theorem meetLists_sound (X : α → Fam) (A B : List (Clause α)) (n W v) :
    semList X (meetLists A B) n W v ↔ interT (semList X A) (semList X B) n W v := by
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨a, ha, b, hb, hm⟩ : ∃ a ∈ A, ∃ b ∈ B, c ∈ meet a b := by
      simpa [meetLists, List.mem_flatMap] using hc
    have hh := (meet_sound X a b n W v).mp ⟨c, hm, hv⟩
    exact ⟨⟨a, ha, hh.1⟩, ⟨b, hb, hh.2⟩⟩
  · rintro ⟨⟨a, ha, hva⟩, ⟨b, hb, hvb⟩⟩
    obtain ⟨c, hc, hv⟩ := (meet_sound X a b n W v).mpr ⟨hva, hvb⟩
    exact ⟨c, by simp [meetLists, List.mem_flatMap]; exact ⟨a, ha, b, hb, hc⟩, hv⟩

theorem normalize_sound (X : α → Fam) (f : Formula α) (n W v) :
    semList X (normalize f) n W v ↔ eval X f n W v := by
  induction f with
  | bot => simp [normalize, semList, setSem, eval]
  | atom c => exact singleton_sem X c n W v
  | union a b ih ih' =>
    have hu : semList X (normalize a ++ normalize b) n W v ↔
        semList X (normalize a) n W v ∨ semList X (normalize b) n W v := by
      simp [semList, setSem, List.mem_append, or_and_right, exists_or]
    exact hu.trans (or_congr ih ih')
  | inter a b ih ih' => exact (meetLists_sound X _ _ n W v).trans (and_congr ih ih')

/-- All constructors remain admissible, without assumptions on the operand
families. Invariant comparison and arrow guards supply the required stability. -/
theorem sem_adm (X : α → Fam) (c : Clause α) : Adm (sem X c) := by
  cases c with
  | nul => exact nulT_adm
  | bool => exact boolT_adm
  | boolLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | refs a bs => exact adm _ _
  | arrs L => exact arrowsT_adm _

theorem sem_congr (X Y : α → Fam) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n)
    (c : Clause α) (W : WorldT n) (v : Val) : sem X c n W v ↔ sem Y c n W v := by
  cases c with
  | nul => rfl
  | bool => rfl
  | boolLit _ => rfl
  | refs a bs => exact congr_below X Y a bs n h W v
  | arrs L => exact arrowsT_congr L _ _ (fun p _ => ⟨h p.1, h p.2⟩) W v

#print axioms normalize_sound
end Verification.ExperimentState.PositiveNormalization
