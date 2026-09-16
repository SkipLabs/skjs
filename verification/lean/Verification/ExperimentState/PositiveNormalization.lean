import Verification.ExperimentState.CallableConjunctions

/-! Finite positive normalization with nonempty reference conjunctions. Operands
are parameters: normalization never distributes through invariant contracts or
arrow results. Taking operands to be graph-label lists supports recursive graphs.
-/
namespace Verification.ExperimentState.PositiveNormalization
open ReferenceConjunctions Tower

inductive Clause (α : Type) where
  | nul | bool
  /-- A location under one or more record contracts. An operand is a finite map
  from field names to labels and names only the fields it constrains, so
  operands naming different fields describe different locations of the same
  object rather than one location twice. -/
  | refs (first : List (String × α)) (rest : List (List (String × α)))
  | arrs (arrows : List (List α × α))
  | boolLit (value : Bool)
  /-- Numbers, and one number. The spelling is canonical, so `numLit` singletons
  are distinct exactly when the numbers are. -/
  | num
  | numLit (bits : UInt64)
  /-- The value a body produces by completing rather than returning. -/
  | undef
  | callable (first : List (String × α)) (rest : List (List (String × α)))
      (arrows : List (List α × α))
  deriving Repr, DecidableEq

def sem (X : α → Fam) : Clause α → Fam
  | .nul => nulT
  | .undef => undefT
  | .bool => boolT
  | .boolLit b => fun _ _ v => v = (if b then .tru else .fls)
  | .num => numT
  | .numLit b => fun _ _ v => v = .num b
  | .refs a bs => refsT (famsOf X a) (bs.map (famsOf X))
  | .arrs L => callsT (L.map fun p => (p.1.map X, X p.2))
  | .callable a bs L =>
      CallableConjunctions.objectsT (famsOf X a) (bs.map (famsOf X))
        (L.map fun p => (p.1.map X,X p.2))

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
  | .undef, .undef => [.undef]
  | .bool, .bool => [.bool]
  | .bool, .boolLit b | .boolLit b, .bool => [.boolLit b]
  | .boolLit a, .boolLit b => if a == b then [.boolLit a] else []
  | .num, .num => [.num]
  | .num, .numLit b | .numLit b, .num => [.numLit b]
  | .numLit a, .numLit b => if a == b then [.numLit a] else []
  | .refs a bs, .refs c ds => [.refs a (bs ++ c :: ds)]
  | .arrs L, .arrs M => [.arrs (L ++ M)]
  | .callable a bs L, .callable c ds M => [.callable a (bs ++ c :: ds) (L ++ M)]
  | .callable a bs L, .arrs M => [.callable a bs (L ++ M)]
  | .arrs L, .callable a bs M => [.callable a bs (M ++ L)]
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
  | .nul => 0 | .bool | .boolLit _ => 1 | .refs .. => 2 | .arrs .. | .callable .. => 3
  | .undef => 4 | .num | .numLit _ => 5

def valueShape : Val → Nat
  | .nul => 0 | .tru | .fls => 1 | .objAt _ .absent => 2 | .undef => 4
  | .objAt _ (.closure _ _) => 3
  | .num _ => 5
  | _ => 6

theorem sem_shape {X : α → Fam} {c : Clause α} {n W v}
    (h : sem X c n W v) : valueShape v = shape c := by
  cases c with
  | nul => cases h; rfl
  | bool => rcases h with h | h <;> cases h <;> rfl
  | boolLit b => cases b <;> cases h <;> rfl
  | num => obtain ⟨b, rfl⟩ := h; rfl
  | numLit b => cases h; rfl
  | refs a bs => obtain ⟨flds, rfl, _⟩ := h.1; rfl
  | arrs L => rcases callsT_callable h with ⟨arity, b, l, rfl, _⟩; rfl
  | undef => cases h; rfl
  | callable a bs L => rcases callsT_callable h.2 with ⟨arity,b,l,rfl,_⟩; rfl

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
      exact TypeAlgebra.calls_append _ _ n W v
    · simp only [meet, singleton_sem, sem, List.map_append]
      exact (CallableConjunctions.calls_merge _ _ _ _ n W v).trans and_comm
    · rename_i b
      cases b <;> simp [meet, singleton_sem, sem, interT, boolT]
      all_goals intro hv; subst v; simp
    · rename_i b c
      cases b <;> cases c <;> simp [meet, sem, interT, semList, setSem]
      all_goals intro hv; subst v; simp
    · -- num ∩ num
      simp [meet, singleton_sem, sem, interT, numT]
    · -- num ∩ numLit: the singleton already implies the family
      rename_i b
      simp [meet, singleton_sem, sem, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ num
      rename_i b
      simp [meet, singleton_sem, sem, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ numLit: equal spellings are equal numbers
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [meet, singleton_sem, sem, interT]
      · simp [meet, semList, setSem, sem, interT, hab]
        intro hv; subst hv; simp [hab]
    · simp [meet, singleton_sem, sem, interT]
    · simp only [meet, singleton_sem, sem, List.map_append]
      exact CallableConjunctions.calls_merge _ _ _ _ n W v
    · simp only [meet, singleton_sem, sem, List.map_append, List.map_cons]
      exact CallableConjunctions.merge _ _ _ _ _ _ n W v
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
  | num => exact numT_adm
  | numLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | refs a bs => exact adm _ _
  | arrs L => exact callsT_adm _
  | callable a bs L => exact CallableConjunctions.adm _ _ _
  | undef => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem sem_congr (X Y : α → Fam) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n)
    (c : Clause α) (W : WorldT n) (v : Val) : sem X c n W v ↔ sem Y c n W v := by
  cases c with
  | nul => rfl
  | bool => rfl
  | boolLit _ => rfl
  | num => rfl
  | numLit _ => rfl
  | undef => rfl
  | refs a bs => exact congr_below X Y a bs n h W v
  | arrs L =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact callsT_congr L _ _ (fun p _ => ⟨hd p.1, h p.2⟩) W v
  | callable a bs L => exact CallableConjunctions.congr_below X Y a bs L n h W v

#print axioms normalize_sound
end Verification.ExperimentState.PositiveNormalization
