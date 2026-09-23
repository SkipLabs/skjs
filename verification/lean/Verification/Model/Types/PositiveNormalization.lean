import Verification.Model.Types.CallableConjunctions
import Verification.Model.Programs.RestCalls

/-! Finite positive normalization with nonempty reference conjunctions. Operands
are parameters: normalization never distributes through invariant contracts or
arrow results. Taking operands to be graph-label lists supports recursive graphs.
-/
namespace Verification.Model.PositiveNormalization
open ReferenceConjunctions Tower

/-- A tuple contract: required positions, optional positions, and the contract
any further position must hold, if the array may have any. -/
structure Tuple (α : Type) where
  required : List α
  optional : List α
  rest : Option α
  readonly : Bool
  deriving DecidableEq, Repr

/-- The families a tuple contract denotes, position by position. -/
def tupleFams {α : Type} (X : α → Fam) (t : Tuple α) : TupleF :=
  ⟨t.required.map X, t.optional.map X, t.rest.map X, t.readonly⟩

inductive Clause (α : Type) where
  | nul | bool
  /-- A location under one or more record contracts. An operand is a finite map
  from field names to labels and names only the fields it constrains, so
  operands naming different fields describe different locations of the same
  object rather than one location twice. -/
  | refs (first : List (String × α)) (rest : List (List (String × α)))
      (views : List (String × α))
  /-- A plain object with invariant named fields, readonly named views, and
  readonly string-index views. The index operands apply to every present own
  field, including named ones. A first record operand fixes the object shape;
  it may be empty for a pure dictionary. -/
  | dict (first : List (String × α)) (rest : List (List (String × α)))
      (views : List (String × α)) (indexes : List α)
  /-- A callable value meeting every fixed signature, `(receiver, parameters,
  result)`, and every variadic one, `(receiver, fixed parameters, element,
  result)`: the receiver a call may pass, the contract of each actual, and
  the result. They describe the calls a caller may write, not the callee's
  code; a signature indifferent to its receiver has receiver `top`. -/
  | arrs (arrows : List (α × List α × α)) (variadic : List (α × List α × α × α))
  | boolLit (value : Bool)
  /-- Numbers, and one number. The spelling is canonical, so `numLit` singletons
  are distinct exactly when the numbers are. -/
  | num
  | numLit (bits : UInt64)
  /-- The value a body produces by completing rather than returning. -/
  | undef
  | callable (first : List (String × α)) (rest : List (List (String × α)))
      (arrows : List (α × List α × α)) (variadic : List (α × List α × α × α))
  /-- Semantic top: every value. Membership grants no operation, so nothing
  reads, calls or tests through it without a narrowing fact. `unknown`
  denotes it; a `void` result forgets its guarantee into it. -/
  | top
  /-- Strings, and one string; appended last so every earlier case order holds. -/
  | str
  | strLit (value : String)
  /-- An array store under one or more tuple contracts. The array object
  holds the store in its store field; the contracts describe the store. -/
  | list (first : Tuple α) (rest : List (Tuple α))
  deriving Repr, DecidableEq

/-- Every value. A closed value, as every member of every family is. -/
def topT : Fam := fun _ _ v => isVal v = true ∧ Scoped 0 v

def sem (X : α → Fam) : Clause α → Fam
  | .top => topT
  | .list a bs => fun n W v => listT (tupleFams X a) n W v ∧ ∀ b ∈ bs, listT (tupleFams X b) n W v
  | .nul => nulT
  | .undef => undefT
  | .bool => boolT
  | .boolLit b => fun _ _ v => v = (if b then .tru else .fls)
  | .num => numT
  | .numLit b => fun _ _ v => v = .num b
  | .str => strT
  | .strLit s => fun _ _ v => v = .str s
  | .refs a bs vs => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧ viewT (famsOf X vs) n W v
  | .dict a bs vs ds => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧
      viewT (famsOf X vs) n W v ∧ ∀ d ∈ ds, dictViewT (X d) n W v
  | .arrs L S => interT (callsT (L.map fun p => (X p.1, p.2.1.map X, X p.2.2)))
      (restsT (S.map fun s => (X s.1, s.2.1.map X, X s.2.2.1, X s.2.2.2)))
  | .callable a bs L S =>
      interT (CallableConjunctions.objectsT (famsOf X a) (bs.map (famsOf X))
        (L.map fun p => (X p.1, p.2.1.map X, X p.2.2)))
        (restsT (S.map fun s => (X s.1, s.2.1.map X, X s.2.2.1, X s.2.2.2)))

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
  | .top, c | c, .top => [c]
  | .list a bs, .list c ds => [.list a (bs ++ c :: ds)]
  | .nul, .nul => [.nul]
  | .undef, .undef => [.undef]
  | .bool, .bool => [.bool]
  | .bool, .boolLit b | .boolLit b, .bool => [.boolLit b]
  | .boolLit a, .boolLit b => if a == b then [.boolLit a] else []
  | .num, .num => [.num]
  | .num, .numLit b | .numLit b, .num => [.numLit b]
  | .numLit a, .numLit b => if a == b then [.numLit a] else []
  | .str, .str => [.str]
  | .str, .strLit s | .strLit s, .str => [.strLit s]
  | .strLit a, .strLit b => if a == b then [.strLit a] else []
  | .refs a bs vs, .refs c ds ws => [.refs a (bs ++ c :: ds) (vs ++ ws)]
  | .refs a bs vs, .dict c ds ws ix => [.dict a (bs ++ c :: ds) (vs ++ ws) ix]
  | .dict a bs vs ix, .refs c ds ws => [.dict a (bs ++ c :: ds) (vs ++ ws) ix]
  | .dict a bs vs ix, .dict c ds ws iy => [.dict a (bs ++ c :: ds) (vs ++ ws) (ix ++ iy)]
  | .arrs L S, .arrs M T => [.arrs (L ++ M) (S ++ T)]
  | .callable a bs L S, .callable c ds M T => [.callable a (bs ++ c :: ds) (L ++ M) (S ++ T)]
  | .callable a bs L S, .arrs M T => [.callable a bs (L ++ M) (S ++ T)]
  | .arrs L S, .callable a bs M T => [.callable a bs (M ++ L) (T ++ S)]
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
  | .nul => 0 | .bool | .boolLit _ => 1 | .refs .. | .dict .. => 2 | .arrs .. | .callable .. => 3
  | .undef => 4 | .num | .numLit _ => 5 | .str | .strLit _ => 6
  | .top => 7 | .list .. => 8

def valueShape : Val → Nat
  | .nul => 0 | .tru | .fls => 1 | .objAt _ .absent => 2 | .undef => 4
  | .objAt _ (.closure _ _) | .objAt _ (.variadic _ _) | .objAt _ (.bound _ _ _) => 3
  | .num _ => 5
  | .str _ => 6
  | .arr _ => 8
  | _ => 7

/-- Every member of a clause is a closed value; top says nothing more. -/
theorem sem_value {X : α → Fam} {c : Clause α} {n W v}
    (h : sem X c n W v) : isVal v = true ∧ Scoped 0 v := by
  cases c with
  | top => exact h
  | list a bs => obtain ⟨ls, rfl, _⟩ := h.1; exact ⟨rfl, trivial⟩
  | nul => subst v; exact ⟨rfl, trivial⟩
  | bool => rcases h with rfl | rfl <;> exact ⟨rfl, trivial⟩
  | boolLit b => cases b <;> cases h <;> exact ⟨rfl, trivial⟩
  | num => obtain ⟨b, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | numLit b => subst v; exact ⟨rfl, trivial⟩
  | refs a rest => obtain ⟨flds, rfl, _⟩ := h.1.1; exact ⟨rfl, trivial⟩
  | dict a rest vs ds => obtain ⟨flds, rfl, _⟩ := h.1.1; exact ⟨rfl, trivial⟩
  | arrs L S => exact ⟨h.1.1.val, h.1.1.scoped⟩
  | callable a bs L S => exact ⟨h.1.2.1.val, h.1.2.1.scoped⟩
  | undef => subst v; exact ⟨rfl, trivial⟩
  | str => obtain ⟨s, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | strLit s => subst v; exact ⟨rfl, trivial⟩

/-- A member's shape is its clause's, except under top, which has none. -/
theorem sem_shape {X : α → Fam} {c : Clause α} {n W v} (hc : c ≠ .top)
    (h : sem X c n W v) : valueShape v = shape c := by
  cases c with
  | top => exact absurd rfl hc
  | list a bs => obtain ⟨ls, rfl, _⟩ := h.1; rfl
  | nul => cases h; rfl
  | bool => rcases h with h | h <;> cases h <;> rfl
  | boolLit b => cases b <;> cases h <;> rfl
  | num => obtain ⟨b, rfl⟩ := h; rfl
  | numLit b => cases h; rfl
  | refs a bs => obtain ⟨flds, rfl, _⟩ := h.1.1; rfl
  | dict a bs vs ds => obtain ⟨flds, rfl, _⟩ := h.1.1; rfl
  | arrs L S =>
    obtain ⟨fs, code, rfl, hc, -⟩ := h.1.1
    cases code <;> simp_all [valueShape, shape]
  | undef => cases h; rfl
  | callable a bs L S =>
    obtain ⟨fs, code, rfl, hc, -⟩ := h.1.2.1
    cases code <;> simp_all [valueShape, shape]
  | str => obtain ⟨s, rfl⟩ := h; rfl
  | strLit s => cases h; rfl

theorem meet_sound (X : α → Fam) (a b : Clause α) (n : Nat) (W : WorldT n) (v : Val) :
    semList X (meet a b) n W v ↔ interT (sem X a) (sem X b) n W v := by
  by_cases ha : a = .top
  · subst ha
    simp only [meet, singleton_sem, sem, interT]
    exact ⟨fun h => ⟨sem_value h, h⟩, fun h => h.2⟩
  by_cases hb : b = .top
  · subst hb
    have hm : meet a .top = [a] := by
      cases a <;> first | exact absurd rfl ha | rfl
    rw [hm, singleton_sem]
    exact ⟨fun h => ⟨h, sem_value h⟩, fun h => h.1⟩
  by_cases hs : shape a = shape b
  · cases a <;> cases b <;> simp only [shape] at hs
    all_goals try contradiction
    · simp [meet, singleton_sem, sem, interT]
    · simp [meet, singleton_sem, sem, interT]
    · rename_i b
      cases b <;> simp [meet, singleton_sem, sem, interT, boolT]
      all_goals intro hv; subst v; simp
    · simp only [meet, singleton_sem, sem, List.map_append, List.map_cons]
      rw [merge _ _ _ _ n W v, famsOf_append, viewT_append]
      simp only [interT]
      exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩, fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩⟩
    · -- refs ∩ dictionary
      simp only [meet, singleton_sem, sem, List.map_append, List.map_cons]
      rw [merge _ _ _ _ n W v, famsOf_append, viewT_append]
      simp only [interT]
      simp only [and_assoc, and_left_comm, and_comm]
    · -- dictionary ∩ refs
      simp only [meet, singleton_sem, sem, List.map_append, List.map_cons]
      rw [merge _ _ _ _ n W v, famsOf_append, viewT_append]
      simp only [interT]
      simp only [and_assoc, and_left_comm, and_comm]
    · -- dictionary ∩ dictionary
      simp only [meet, singleton_sem, sem, List.map_append, List.map_cons,
        List.mem_append, or_imp, forall_and]
      rw [merge _ _ _ _ n W v, famsOf_append, viewT_append]
      simp only [interT]
      simp only [and_assoc, and_left_comm, and_comm]
    · -- arrs ∩ arrs
      simp only [meet, singleton_sem, sem, List.map_append]
      rw [interT, TypeAlgebra.calls_append, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    · -- arrs ∩ callable
      simp only [meet, singleton_sem, sem, List.map_append]
      rw [interT, CallableConjunctions.calls_merge, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, c⟩, t, r⟩ => ⟨⟨c, r⟩, o, t⟩, fun ⟨⟨c, r⟩, o, t⟩ => ⟨⟨o, c⟩, t, r⟩⟩
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
    · -- callable ∩ arrs
      simp only [meet, singleton_sem, sem, List.map_append]
      rw [interT, CallableConjunctions.calls_merge, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, c⟩, r, t⟩ => ⟨⟨o, r⟩, c, t⟩, fun ⟨⟨o, r⟩, c, t⟩ => ⟨⟨o, c⟩, r, t⟩⟩
    · -- callable ∩ callable
      simp only [meet, singleton_sem, sem, List.map_append, List.map_cons]
      rw [interT, CallableConjunctions.merge, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, p⟩, r, t⟩ => ⟨⟨o, r⟩, p, t⟩, fun ⟨⟨o, r⟩, p, t⟩ => ⟨⟨o, p⟩, r, t⟩⟩
    · -- str ∩ str
      simp [meet, singleton_sem, sem, interT, strT]
    · -- str ∩ strLit
      rename_i s
      simp [meet, singleton_sem, sem, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ str
      rename_i s
      simp [meet, singleton_sem, sem, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ strLit
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [meet, singleton_sem, sem, interT]
      · simp [meet, semList, setSem, sem, interT, hab]
        intro hv; subst hv; simp [hab]
    · -- list ∩ list: every contract of both, on the one store
      simp only [meet, singleton_sem, sem, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq, interT]
      exact ⟨fun ⟨ha, hb, hc, hd⟩ => ⟨⟨ha, hb⟩, hc, hd⟩, fun ⟨⟨ha, hb⟩, hc, hd⟩ => ⟨ha, hb, hc, hd⟩⟩
  · have hm : meet a b = [] := by
      cases a <;> cases b <;> simp_all [shape, meet]
    rw [hm]
    constructor
    · intro h; exact False.elim (nil_sem X n W v h)
    · rintro ⟨hva, hvb⟩
      exact False.elim (hs ((sem_shape ha hva).symm.trans (sem_shape hb hvb)))

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
  | refs a bs vs => exact ⟨fun n W v h => ⟨(adm _ _).down n W v h.1, (viewT_adm _).down n W v h.2⟩,
      fun n W U hx v h => ⟨(adm _ _).mono n W U hx v h.1, (viewT_adm _).mono n W U hx v h.2⟩⟩
  | dict a bs vs ds =>
    refine ⟨?_, ?_⟩
    · intro n W v h
      exact ⟨(adm _ _).down n W v h.1, (viewT_adm _).down n W v h.2.1,
        fun d hd => (dictViewT_adm _).down n W v (h.2.2 d hd)⟩
    · intro n W U hx v h
      exact ⟨(adm _ _).mono n W U hx v h.1, (viewT_adm _).mono n W U hx v h.2.1,
        fun d hd => (dictViewT_adm _).mono n W U hx v (h.2.2 d hd)⟩
  | arrs L S => exact interT_adm _ _ (callsT_adm _) (restsT_adm _)
  | callable a bs L S => exact interT_adm _ _ (CallableConjunctions.adm _ _ _) (restsT_adm _)
  | undef => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | top => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | list a bs => exact ⟨fun n W v h => ⟨(listT_adm _).down n W v h.1,
        fun b hb => (listT_adm _).down n W v (h.2 b hb)⟩,
      fun n W U hx v h => ⟨(listT_adm _).mono n W U hx v h.1,
        fun b hb => (listT_adm _).mono n W U hx v (h.2 b hb)⟩⟩
  | str => exact strT_adm
  | strLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Position by position, a tuple contract's meaning depends on its labels'
meanings only below the budget, as a record's does. -/
theorem list_congr_below (X Y : α → Fam) (t : Tuple α) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    listT (tupleFams X t) n W v ↔ listT (tupleFams Y t) n W v := by
  constructor <;> rintro ⟨ls, rfl, hlen, hbound, hreq, hopt, hrest⟩ <;>
    simp only [listT, tupleFams, List.length_map, List.getElem?_map, Option.map_eq_none_iff,
      Option.map_eq_some_iff] at hlen hbound hreq hopt hrest ⊢ <;>
    refine ⟨ls, rfl, hlen, hbound, ?_, ?_, ?_⟩
  · rintro i A ⟨a, ha, rfl⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (X a) ⟨a, ha, rfl⟩
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u)⟩
  · rintro i A l ⟨a, ha, rfl⟩ hl
    obtain ⟨c, hw, hag⟩ := hopt i (X a) l ⟨a, ha, rfl⟩ hl
    exact ⟨c, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u)⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l hi hl
    exact ⟨Y e, c, ⟨e, he, rfl⟩, hw, fun j hj W' u => (hag j hj W' u).congr (h e j hj W' u)⟩
  · rintro i A ⟨a, ha, rfl⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (Y a) ⟨a, ha, rfl⟩
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u).symm⟩
  · rintro i A l ⟨a, ha, rfl⟩ hl
    obtain ⟨c, hw, hag⟩ := hopt i (Y a) l ⟨a, ha, rfl⟩ hl
    exact ⟨c, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u).symm⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l hi hl
    exact ⟨X e, c, ⟨e, he, rfl⟩, hw, fun j hj W' u => (hag j hj W' u).congr (h e j hj W' u).symm⟩

theorem sem_congr (X Y : α → Fam) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n)
    (c : Clause α) (W : WorldT n) (v : Val) : sem X c n W v ↔ sem Y c n W v := by
  cases c with
  | nul => rfl
  | bool => rfl
  | boolLit _ => rfl
  | num => rfl
  | numLit _ => rfl
  | str => rfl
  | strLit _ => rfl
  | undef => rfl
  | top => rfl
  | list a bs =>
    exact and_congr (list_congr_below X Y a n h W v) (forall_congr' fun b => forall_congr' fun _ => list_congr_below X Y b n h W v)
  | refs a bs vs => exact and_congr (congr_below X Y a bs n h W v) (view_congr_below X Y vs n h W v)
  | dict a bs vs ds =>
    exact and_congr (congr_below X Y a bs n h W v)
      (and_congr (view_congr_below X Y vs n h W v)
        (forall_congr' fun d => forall_congr' fun _ => dictViewT_congr (h d) W v))
  | arrs L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (callsT_congr L _ _ (fun p _ => ⟨h p.1, hd p.2.1, h p.2.2⟩) W v)
      (restsT_congr S _ _ (fun s _ => ⟨h s.1, hd s.2.1, h s.2.2.1, h s.2.2.2⟩) W v)
  | callable a bs L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (CallableConjunctions.congr_below X Y a bs L n h W v)
      (restsT_congr S _ _ (fun s _ => ⟨h s.1, hd s.2.1, h s.2.2.1, h s.2.2.2⟩) W v)

#print axioms normalize_sound
end Verification.Model.PositiveNormalization
