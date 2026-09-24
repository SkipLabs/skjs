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

/-- The operand a tuple contract states for an index, as `positionFam` states
its family. -/
def Tuple.position (t : Tuple α) (i : Nat) : Option α :=
  match t.required[i]? with
  | some a => some a
  | none => match t.optional[i - t.required.length]? with
    | some a => some a
    | none => if t.required.length + t.optional.length ≤ i then t.rest else none

/-- The families a tuple contract denotes, position by position. -/
def tupleFams {α : Type} (X : α → Fam) (t : Tuple α) : TupleF :=
  ⟨t.required.map X, t.optional.map X, t.rest.map X, t.readonly⟩

inductive Clause (α : Type) where
  | nul | bool
  /-- A location under one or more record contracts. An operand is a finite map
  from field names to labels and names only the fields it constrains, so
  operands naming different fields describe different locations of the same
  object rather than one location twice. Optional fields constrain a key
  only where the object has it (`optT`). -/
  | refs (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (views : List (PropKey × α)) (optional : List (PropKey × α) := [])
  /-- A plain object with invariant named fields, readonly named views, and
  readonly string-index views. The index operands apply to every present own
  field, including named ones. A first record operand fixes the object shape;
  it may be empty for a pure dictionary. -/
  | dict (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (views : List (PropKey × α)) (indexes : List α) (optional : List (PropKey × α) := [])
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
  | callable (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
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
  /-- Bigints and symbols; appended last so every earlier case order holds. -/
  | bigint
  | symbol
  /-- A class value meeting every construct signature `(parameters, result)`:
  `new` with actuals at the parameters is safe at the result; and every
  variadic one `(parameters, rest, result)`, whose actuals past the parameters
  are, as one pack, at the rest. Its code has `[[Construct]]` only, so no
  callable clause meets it. -/
  | ctors (signatures : List (List α × α)) (variadic : List (List α × α × α) := [])
  /-- An argument list under one or more tuple contracts: what a rest
  parameter's type says of the actuals after the fixed ones. Only a signature's
  rest meets one; no program value is one. -/
  | pack (first : Tuple α) (rest : List (Tuple α))
  deriving Repr, DecidableEq

/-- Every value. A closed value, as every member of every family is. -/
def topT : Fam := fun _ _ v => isVal v = true ∧ Scoped 0 v

def semWithArgs (X : α → Fam) (P : α → ArgFam) : Clause α → Fam
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
  | .bigint => bigintT
  | .symbol => symbolT
  | .refs a bs vs os => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧ viewT (famsOf X vs) n W v ∧
        optT (famsOf X os) n W v
  | .dict a bs vs ds os => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧
      viewT (famsOf X vs) n W v ∧ (∀ d ∈ ds, dictViewT (X d) n W v) ∧
        optT (famsOf X os) n W v
  | .arrs L S => interT (callsT (L.map fun p => (X p.1, p.2.1.map X, X p.2.2)))
      (restsT (S.map fun s => (X s.1, s.2.1.map X, P s.2.2.1, X s.2.2.2)))
  | .callable a bs L S =>
      interT (CallableConjunctions.objectsT (famsOf X a) (bs.map (famsOf X))
        (L.map fun p => (X p.1, p.2.1.map X, X p.2.2)))
        (restsT (S.map fun s => (X s.1, s.2.1.map X, P s.2.2.1, X s.2.2.2)))
  | .ctors L S => interT (ctorsT (L.map fun p => (p.1.map X, X p.2)))
      (ctorRestsT (S.map fun s => (s.1.map X, P s.2.1, X s.2.2)))
  | .pack a bs => packT (tupleFams X a :: bs.map (tupleFams X))

/-- The argument-list component of a clause. Grouping arguments spends no
approximation step; only a surrounding runtime operation supplies a guard. -/
def clauseArguments (X : α → Fam) : Clause α → ArgFam
  | .pack a bs => fun n W vs => ∀ t ∈ a :: bs,
      ArgumentContracts.Fits (tupleFams X t) n W vs
  | _ => fun _ _ _ => False

/-- The legacy graph interpretation; argument slots cross an explicit boundary. -/
def sem (X : α → Fam) : Clause α → Fam := semWithArgs X (fun a => packArgs (X a))

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
  | .bigint, .bigint => [.bigint]
  | .symbol, .symbol => [.symbol]
  | .refs a bs vs os, .refs c ds ws ps => [.refs a (bs ++ c :: ds) (vs ++ ws) (os ++ ps)]
  | .refs a bs vs os, .dict c ds ws ix ps => [.dict a (bs ++ c :: ds) (vs ++ ws) ix (os ++ ps)]
  | .dict a bs vs ix os, .refs c ds ws ps => [.dict a (bs ++ c :: ds) (vs ++ ws) ix (os ++ ps)]
  | .dict a bs vs ix os, .dict c ds ws iy ps => [.dict a (bs ++ c :: ds) (vs ++ ws) (ix ++ iy) (os ++ ps)]
  | .arrs L S, .arrs M T => [.arrs (L ++ M) (S ++ T)]
  | .ctors L S, .ctors M T => [.ctors (L ++ M) (S ++ T)]
  | .pack a bs, .pack c ds => [.pack a (bs ++ c :: ds)]
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
  | .top => 7 | .list .. => 8 | .bigint => 9 | .symbol => 10 | .ctors .. => 11
  | .pack .. => 12

def valueShape : Val → Nat
  | .nul => 0 | .tru | .fls => 1 | .objAt _ .absent => 2 | .undef => 4
  | .objAt _ (.closure _ _ .call) | .objAt _ (.variadic _ _) | .objAt _ (.bound _ _ _) => 3
  | .objAt _ (.closure _ _ .construct) => 11
  | .num _ => 5
  | .str _ => 6
  | .arr _ => 8
  | .bigint _ => 9
  | .sym _ => 10
  | .args _ => 12
  | _ => 7

/-- Every member of a clause is a closed value; top says nothing more. -/
theorem semWithArgs_value {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (h : semWithArgs X P c n W v) : isVal v = true ∧ Scoped 0 v := by
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
  | bigint => obtain ⟨i, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | symbol => obtain ⟨i, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | ctors L S => obtain ⟨fs, a, b, rfl, hs⟩ := h.1.1; exact ⟨rfl, hs⟩
  | pack a bs => obtain ⟨vs, rfl, hs, -⟩ := h; exact ⟨rfl, hs⟩

theorem sem_value {X : α → Fam} {c : Clause α} {n W v}
    (h : sem X c n W v) : isVal v = true ∧ Scoped 0 v := semWithArgs_value h

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
    cases code <;> try (rename_i kind; cases kind)
    all_goals simp_all [valueShape, shape, CallCode.callable]
  | undef => cases h; rfl
  | callable a bs L S =>
    obtain ⟨fs, code, rfl, hc, -⟩ := h.1.2.1
    cases code <;> try (rename_i kind; cases kind)
    all_goals simp_all [valueShape, shape, CallCode.callable]
  | str => obtain ⟨s, rfl⟩ := h; rfl
  | strLit s => cases h; rfl
  | bigint => obtain ⟨i, rfl⟩ := h; rfl
  | symbol => obtain ⟨i, rfl⟩ := h; rfl
  | ctors L S => obtain ⟨fs, a, b, rfl, -⟩ := h.1.1; rfl
  | pack a bs => obtain ⟨vs, rfl, -⟩ := h; rfl

theorem meet_sound (X : α → Fam) (a b : Clause α) (n : Nat) (W : WorldT n) (v : Val) :
    semList X (meet a b) n W v ↔ interT (sem X a) (sem X b) n W v := by
  by_cases ha : a = .top
  · subst ha
    simp only [meet, singleton_sem, sem, semWithArgs, interT]
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
    · simp [meet, singleton_sem, sem, semWithArgs, interT]
    · simp [meet, singleton_sem, sem, semWithArgs, interT]
    · rename_i b
      cases b <;> simp [meet, singleton_sem, sem, semWithArgs, interT, boolT]
      all_goals intro hv; subst v; simp
    · simp only [meet, singleton_sem, sem, semWithArgs, List.map_append, List.map_cons]
      rw [merge _ _ _ _ n W v]
      simp only [famsOf_append, viewT_append, optT_append, interT]
      simp only [and_assoc, and_left_comm, and_comm]
    · -- refs ∩ dictionary
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append, List.map_cons]
      rw [merge _ _ _ _ n W v]
      simp only [famsOf_append, viewT_append, optT_append, interT]
      simp only [and_assoc, and_left_comm, and_comm]
    · -- dictionary ∩ refs
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append, List.map_cons]
      rw [merge _ _ _ _ n W v]
      simp only [famsOf_append, viewT_append, optT_append, interT]
      simp only [and_assoc, and_left_comm, and_comm]
    · -- dictionary ∩ dictionary
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append, List.map_cons,
        List.mem_append, or_imp, forall_and]
      rw [merge _ _ _ _ n W v]
      simp only [famsOf_append, viewT_append, optT_append, interT]
      simp only [and_assoc, and_left_comm, and_comm]
    · -- arrs ∩ arrs
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append]
      rw [interT, TypeAlgebra.calls_append, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    · -- arrs ∩ callable
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append]
      rw [interT, CallableConjunctions.calls_merge, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, c⟩, t, r⟩ => ⟨⟨c, r⟩, o, t⟩, fun ⟨⟨c, r⟩, o, t⟩ => ⟨⟨o, c⟩, t, r⟩⟩
    · rename_i b
      cases b <;> simp [meet, singleton_sem, sem, semWithArgs, interT, boolT]
      all_goals intro hv; subst v; simp
    · rename_i b c
      cases b <;> cases c <;> simp [meet, sem, semWithArgs, interT, semList, setSem]
      all_goals intro hv; subst v; simp
    · -- num ∩ num
      simp [meet, singleton_sem, sem, semWithArgs, interT, numT]
    · -- num ∩ numLit: the singleton already implies the family
      rename_i b
      simp [meet, singleton_sem, sem, semWithArgs, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ num
      rename_i b
      simp [meet, singleton_sem, sem, semWithArgs, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ numLit: equal spellings are equal numbers
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [meet, singleton_sem, sem, semWithArgs, interT]
      · simp [meet, semList, setSem, sem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · simp [meet, singleton_sem, sem, semWithArgs, interT]
    · -- callable ∩ arrs
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append]
      rw [interT, CallableConjunctions.calls_merge, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, c⟩, r, t⟩ => ⟨⟨o, r⟩, c, t⟩, fun ⟨⟨o, r⟩, c, t⟩ => ⟨⟨o, c⟩, r, t⟩⟩
    · -- callable ∩ callable
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append, List.map_cons]
      rw [interT, CallableConjunctions.merge, TypeAlgebra.rests_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, p⟩, r, t⟩ => ⟨⟨o, r⟩, p, t⟩, fun ⟨⟨o, r⟩, p, t⟩ => ⟨⟨o, p⟩, r, t⟩⟩
    · -- str ∩ str
      simp [meet, singleton_sem, sem, semWithArgs, interT, strT]
    · -- str ∩ strLit
      rename_i s
      simp [meet, singleton_sem, sem, semWithArgs, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ str
      rename_i s
      simp [meet, singleton_sem, sem, semWithArgs, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ strLit
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [meet, singleton_sem, sem, semWithArgs, interT]
      · simp [meet, semList, setSem, sem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · -- list ∩ list: every contract of both, on the one store
      simp only [meet, singleton_sem, sem, semWithArgs, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq, interT]
      exact ⟨fun ⟨ha, hb, hc, hd⟩ => ⟨⟨ha, hb⟩, hc, hd⟩, fun ⟨⟨ha, hb⟩, hc, hd⟩ => ⟨ha, hb, hc, hd⟩⟩
    · -- bigint ∩ bigint
      simp [meet, singleton_sem, sem, semWithArgs, interT, bigintT]
    · -- symbol ∩ symbol
      simp [meet, singleton_sem, sem, semWithArgs, interT, symbolT]
    · -- ctors ∩ ctors: every construct signature of both
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append, interT]
      rw [ctorsT_append, ctorRestsT_append]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    · -- pack ∩ pack: every contract of both, on the one list
      rename_i a bs c ds
      simp only [meet, singleton_sem, sem, semWithArgs, List.map_append, List.map_cons, interT]
      exact packT_append (tupleFams X a :: bs.map (tupleFams X)) _ n W v
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
theorem semWithArgs_adm (X : α → Fam) (P : α → ArgFam) (c : Clause α) : Adm (semWithArgs X P c) := by
  cases c with
  | nul => exact nulT_adm
  | bool => exact boolT_adm
  | boolLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | num => exact numT_adm
  | numLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | refs a bs vs os => exact ⟨fun n W v h => ⟨(adm _ _).down n W v h.1, (viewT_adm _).down n W v h.2.1,
        (optT_adm _).down n W v h.2.2⟩,
      fun n W U hx v h => ⟨(adm _ _).mono n W U hx v h.1, (viewT_adm _).mono n W U hx v h.2.1,
        (optT_adm _).mono n W U hx v h.2.2⟩⟩
  | dict a bs vs ds os =>
    refine ⟨?_, ?_⟩
    · intro n W v h
      exact ⟨(adm _ _).down n W v h.1, (viewT_adm _).down n W v h.2.1,
        fun d hd => (dictViewT_adm _).down n W v (h.2.2.1 d hd), (optT_adm _).down n W v h.2.2.2⟩
    · intro n W U hx v h
      exact ⟨(adm _ _).mono n W U hx v h.1, (viewT_adm _).mono n W U hx v h.2.1,
        fun d hd => (dictViewT_adm _).mono n W U hx v (h.2.2.1 d hd), (optT_adm _).mono n W U hx v h.2.2.2⟩
  | arrs L S => exact interT_adm _ _ (callsT_adm _) (restsT_adm _)
  | callable a bs L S => exact interT_adm _ _ (CallableConjunctions.adm _ _ _) (restsT_adm _)
  | ctors L S => exact interT_adm _ _ (ctorsT_adm _) (ctorRestsT_adm _)
  | pack a bs => exact packT_adm _
  | undef => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | top => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | list a bs => exact ⟨fun n W v h => ⟨(listT_adm _).down n W v h.1,
        fun b hb => (listT_adm _).down n W v (h.2 b hb)⟩,
      fun n W U hx v h => ⟨(listT_adm _).mono n W U hx v h.1,
        fun b hb => (listT_adm _).mono n W U hx v (h.2 b hb)⟩⟩
  | str => exact strT_adm
  | strLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | bigint => exact bigintT_adm
  | symbol => exact symbolT_adm

theorem sem_adm (X : α → Fam) (c : Clause α) : Adm (sem X c) :=
  semWithArgs_adm X (fun a => packArgs (X a)) c

theorem positionFam_tupleFams (X : α → Fam) (t : Tuple α) (i : Nat) :
    positionFam (tupleFams X t) i = (t.position i).map X := by
  simp only [positionFam, Tuple.position, tupleFams, List.getElem?_map, List.length_map]
  cases t.required[i]? <;> simp
  cases t.optional[i - t.required.length]? <;> simp
  split <;> simp

/-- Past the required and optional positions, every index has the rest. -/
theorem Tuple.position_beyond {t : Tuple α} {i : Nat}
    (h : t.required.length + t.optional.length ≤ i) : t.position i = t.rest := by
  simp only [Tuple.position, List.getElem?_eq_none (show t.required.length ≤ i by omega),
    List.getElem?_eq_none (show t.optional.length ≤ i - t.required.length by omega), h, if_true]

/-- An index without a position is past the fixed positions of a contract
without a rest. -/
theorem Tuple.position_none {t : Tuple α} {i : Nat} (h : t.position i = none) :
    t.required.length + t.optional.length ≤ i ∧ t.rest = none := by
  simp only [Tuple.position] at h
  cases hr : t.required[i]? <;> simp only [hr, reduceCtorEq] at h
  cases ho : t.optional[i - t.required.length]? <;> simp only [ho, reduceCtorEq] at h
  rw [List.getElem?_eq_none_iff] at hr ho
  have hi : t.required.length + t.optional.length ≤ i := by omega
  simp only [hi, if_true] at h
  exact ⟨hi, h⟩

/-- Current-level tuple membership preserves current-level agreement. -/
theorem arguments_congr (X Y : α → Fam) (t : Tuple α) (n : Nat) {W : WorldT n}
    (h : ∀ a v, X a n W v ↔ Y a n W v) (vs : List Val) :
    ArgumentContracts.Fits (tupleFams X t) n W vs ↔
      ArgumentContracts.Fits (tupleFams Y t) n W vs := by
  apply TupleFits.congr (by simp [tupleFams]) (by simp [tupleFams]) (by simp [tupleFams])
  intro i
  simp only [positionFam_tupleFams]
  refine ⟨by simp, fun A B hA hB v => ?_⟩
  cases hp : t.position i <;> simp [hp] at hA hB
  subst hA; subst hB
  exact h _ v

theorem clauseArguments_congr (X Y : α → Fam) (c : Clause α) (n : Nat) (W : WorldT n)
    (h : ∀ a v, X a n W v ↔ Y a n W v) (vs : List Val) :
    clauseArguments X c n W vs ↔ clauseArguments Y c n W vs := by
  cases c <;> try exact Iff.rfl
  rename_i a bs
  exact forall_congr' fun t => forall_congr' fun _ => arguments_congr X Y t n h vs

/-- An argument list's fit to a tuple contract depends on the labels' meanings
only below the budget. -/
theorem pack_congr_below (X Y : α → Fam) (t : Tuple α) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (vs : List Tm) :
    PackFits (tupleFams X t) n W vs ↔ PackFits (tupleFams Y t) n W vs := by
  refine PackFits.congr (by simp [tupleFams]) (by simp [tupleFams]) (by simp [tupleFams])
    fun i => ?_
  simp only [positionFam_tupleFams]
  refine ⟨by simp, fun A B hA hB => ?_⟩
  cases hp : t.position i <;> simp [hp] at hA hB
  subst hA; subst hB; exact h _

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

theorem semWithArgs_congr (X Y : α → Fam) (P Q : α → ArgFam) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n)
    (hP : ∀ a, Agree (P a) (Q a) n) (c : Clause α) (W : WorldT n) (v : Val) : semWithArgs X P c n W v ↔ semWithArgs Y Q c n W v := by
  cases c with
  | nul => rfl
  | bool => rfl
  | boolLit _ => rfl
  | num => rfl
  | numLit _ => rfl
  | str => rfl
  | strLit _ => rfl
  | bigint => rfl
  | symbol => rfl
  | undef => rfl
  | top => rfl
  | list a bs =>
    exact and_congr (list_congr_below X Y a n h W v) (forall_congr' fun b => forall_congr' fun _ => list_congr_below X Y b n h W v)
  | refs a bs vs os =>
    exact and_congr (congr_below X Y a bs n h W v)
      (and_congr (view_congr_below X Y vs n h W v) (opt_congr_below X Y os n h W v))
  | dict a bs vs ds os =>
    exact and_congr (congr_below X Y a bs n h W v)
      (and_congr (view_congr_below X Y vs n h W v)
        (and_congr (forall_congr' fun d => forall_congr' fun _ => dictViewT_congr (h d) W v)
          (opt_congr_below X Y os n h W v)))
  | arrs L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (callsT_congr L _ _ (fun p _ => ⟨h p.1, hd p.2.1, h p.2.2⟩) W v)
      (restsT_congr S _ _ (fun s _ => ⟨h s.1, hd s.2.1, hP s.2.2.1, h s.2.2.2⟩) W v)
  | callable a bs L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (CallableConjunctions.congr_below X Y a bs L n h W v)
      (restsT_congr S _ _ (fun s _ => ⟨h s.1, hd s.2.1, hP s.2.2.1, h s.2.2.2⟩) W v)
  | ctors L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (ctorsT_congr L _ _ (fun p _ => ⟨hd p.1, h p.2⟩) W v)
      (ctorRestsT_congr S _ _ (fun s _ => ⟨hd s.1, hP s.2.1, h s.2.2⟩) W v)
  | pack a bs =>
    simp only [semWithArgs, packT]
    refine exists_congr fun vs => and_congr Iff.rfl (and_congr Iff.rfl ?_)
    simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact and_congr (pack_congr_below X Y a n h W vs)
      (forall_congr' fun b => forall_congr' fun _ => pack_congr_below X Y b n h W vs)

theorem sem_congr (X Y : α → Fam) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n)
    (c : Clause α) (W : WorldT n) (v : Val) : sem X c n W v ↔ sem Y c n W v :=
  semWithArgs_congr X Y _ _ n h (fun a => packArgs_congr (h a)) c W v

/-! ## Renaming operands

`Clause.map` renames every operand; the meaning of a renamed clause is the
clause read through the renaming (`sem_map`). A renaming fixing every operand
changes nothing (`map_of_operands`). -/

def Tuple.map (f : α → β) (t : Tuple α) : Tuple β :=
  ⟨t.required.map f, t.optional.map f, t.rest.map f, t.readonly⟩

def Tuple.operands (t : Tuple α) : List α := t.required ++ t.optional ++ t.rest.toList

def mapFields (f : α → β) (fs : List (PropKey × α)) : List (PropKey × β) :=
  fs.map fun q => (q.1, f q.2)

def Clause.map (f : α → β) : Clause α → Clause β
  | .top => .top
  | .nul => .nul
  | .undef => .undef
  | .bool => .bool
  | .boolLit b => .boolLit b
  | .num => .num
  | .numLit v => .numLit v
  | .str => .str
  | .strLit v => .strLit v
  | .bigint => .bigint
  | .symbol => .symbol
  | .list a bs => .list (a.map f) (bs.map (·.map f))
  | .refs a bs vs os => .refs (mapFields f a) (bs.map (mapFields f)) (mapFields f vs) (mapFields f os)
  | .dict a bs vs ds os => .dict (mapFields f a) (bs.map (mapFields f)) (mapFields f vs)
      (ds.map f) (mapFields f os)
  | .arrs L S => .arrs (L.map fun q => (f q.1, q.2.1.map f, f q.2.2))
      (S.map fun q => (f q.1, q.2.1.map f, f q.2.2.1, f q.2.2.2))
  | .callable a bs L S => .callable (mapFields f a) (bs.map (mapFields f))
      (L.map fun q => (f q.1, q.2.1.map f, f q.2.2))
      (S.map fun q => (f q.1, q.2.1.map f, f q.2.2.1, f q.2.2.2))
  | .ctors L S => .ctors (L.map fun q => (q.1.map f, f q.2))
      (S.map fun q => (q.1.map f, f q.2.1, f q.2.2))
  | .pack a bs => .pack (a.map f) (bs.map (·.map f))

/-- Every operand of a clause. -/
def Clause.operands : Clause α → List α
  | .list a bs => a.operands ++ bs.flatMap Tuple.operands
  | .refs a bs vs os => (a ++ bs.flatten ++ vs ++ os).map (·.2)
  | .dict a bs vs ds os => (a ++ bs.flatten ++ vs ++ os).map (·.2) ++ ds
  | .arrs L S => L.flatMap (fun q => q.1 :: q.2.1 ++ [q.2.2]) ++
      S.flatMap (fun q => q.1 :: q.2.1 ++ [q.2.2.1, q.2.2.2])
  | .callable a bs L S => (a ++ bs.flatten).map (·.2) ++
      L.flatMap (fun q => q.1 :: q.2.1 ++ [q.2.2]) ++
      S.flatMap (fun q => q.1 :: q.2.1 ++ [q.2.2.1, q.2.2.2])
  | .ctors L S => L.flatMap (fun q => q.1 ++ [q.2]) ++ S.flatMap fun q => q.1 ++ [q.2.1, q.2.2]
  | .pack a bs => a.operands ++ bs.flatMap Tuple.operands
  | _ => []

private theorem famsOf_fun (X : α → Fam) :
    famsOf X = fun fs => fs.map fun p => (p.1, X p.2) := rfl

theorem tupleFams_map (Y : β → Fam) (f : α → β) (t : Tuple α) :
    tupleFams Y (t.map f) = tupleFams (fun a => Y (f a)) t := by
  simp [tupleFams, Tuple.map, Function.comp_def]

/-- Operand substitution transports value and list operands independently.
The legacy adapter is only one instance of this equation. -/
theorem semWithArgs_map (Y : β → Fam) (P : β → ArgFam) (f : α → β) (c : Clause α) :
    semWithArgs Y P (c.map f) = semWithArgs (fun a => Y (f a)) (fun a => P (f a)) c := by
  cases c
  case pack a bs =>
    simp only [semWithArgs, Clause.map, List.map_map, tupleFams_map]
    congr 2
    exact List.map_congr_left fun t _ => tupleFams_map Y f t
  all_goals simp [semWithArgs, Clause.map, mapFields, famsOf_fun, tupleFams, Tuple.map, Function.comp_def]

theorem sem_map (Y : β → Fam) (f : α → β) (c : Clause α) :
    sem Y (c.map f) = sem (fun a => Y (f a)) c :=
  semWithArgs_map Y (fun a => packArgs (Y a)) f c

/-- The same syntactic operand substitution preserves the argument component,
using current-level element membership rather than delayed pack membership. -/
theorem clauseArguments_map (Y : β → Fam) (f : α → β) (c : Clause α) :
    clauseArguments Y (c.map f) = clauseArguments (fun a => Y (f a)) c := by
  cases c <;> try rfl
  rename_i a bs
  funext n W vs
  apply propext
  simp [clauseArguments, Clause.map, tupleFams_map]

private theorem map_self {l : List α} {f : α → α} (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [h.1, ih h.2]

private theorem mapFields_self {fs : List (PropKey × α)} {f : α → α}
    (h : ∀ a ∈ fs.map (·.2), f a = a) : mapFields f fs = fs :=
  map_self fun q hq => by
    have := h q.2 (List.mem_map_of_mem hq)
    simp [this]

private theorem tuple_self {t : Tuple α} {f : α → α} (h : ∀ a ∈ t.operands, f a = a) :
    t.map f = t := by
  obtain ⟨r, o, e, b⟩ := t
  simp only [Tuple.operands, List.mem_append] at h
  have h1 := map_self (l := r) fun a ha => h a (.inl (.inl ha))
  have h2 := map_self (l := o) fun a ha => h a (.inl (.inr ha))
  have h3 : e.map f = e := by cases e <;> simp_all
  simp [Tuple.map, h1, h2, h3]

/-- A renaming fixing every operand fixes the clause. -/
theorem map_of_operands {c : Clause α} {f : α → α} (h : ∀ a ∈ c.operands, f a = a) :
    c.map f = c := by
  cases c with
  | list a bs =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.list.injEq]
    exact ⟨tuple_self fun x hx => h x (.inl hx),
      map_self fun t ht => tuple_self fun x hx => h x (.inr ⟨t, ht, hx⟩)⟩
  | refs a bs vs os =>
    simp only [Clause.operands, List.map_append, List.mem_append] at h
    simp only [Clause.map, Clause.refs.injEq]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl hx))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inr ?_))),
      mapFields_self fun x hx => h x (.inl (.inr hx)),
      mapFields_self fun x hx => h x (.inr hx)⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | dict a bs vs ds os =>
    simp only [Clause.operands, List.map_append, List.mem_append] at h
    simp only [Clause.map, Clause.dict.injEq]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl hx)))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inl (.inr ?_)))),
      mapFields_self fun x hx => h x (.inl (.inl (.inr hx))),
      map_self fun x hx => h x (.inr hx),
      mapFields_self fun x hx => h x (.inl (.inr hx))⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | arrs L S =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.arrs.injEq]
    refine ⟨map_self fun q hq => ?_, map_self fun q hq => ?_⟩
    · have h1 := h q.1 (.inl ⟨q, hq, by simp⟩)
      have h3 := h q.2.2 (.inl ⟨q, hq, by simp⟩)
      have h2 := map_self (l := q.2.1) fun x hx => h x (.inl ⟨q, hq, by simp [hx]⟩)
      simp [h1, h2, h3]
    · have h1 := h q.1 (.inr ⟨q, hq, by simp⟩)
      have h3 := h q.2.2.1 (.inr ⟨q, hq, by simp⟩)
      have h4 := h q.2.2.2 (.inr ⟨q, hq, by simp⟩)
      have h2 := map_self (l := q.2.1) fun x hx => h x (.inr ⟨q, hq, by simp [hx]⟩)
      simp [h1, h2, h3, h4]
  | callable a bs L S =>
    simp only [Clause.operands, List.map_append, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.callable.injEq]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl hx))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inr ?_))),
      map_self fun q hq => ?_, map_self fun q hq => ?_⟩
    · simp only [List.mem_map, List.mem_flatten] at hx ⊢
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
    · have h1 := h q.1 (.inl (.inr ⟨q, hq, by simp⟩))
      have h3 := h q.2.2 (.inl (.inr ⟨q, hq, by simp⟩))
      have h2 := map_self (l := q.2.1) fun x hx => h x (.inl (.inr ⟨q, hq, by simp [hx]⟩))
      simp [h1, h2, h3]
    · have h1 := h q.1 (.inr ⟨q, hq, by simp⟩)
      have h3 := h q.2.2.1 (.inr ⟨q, hq, by simp⟩)
      have h4 := h q.2.2.2 (.inr ⟨q, hq, by simp⟩)
      have h2 := map_self (l := q.2.1) fun x hx => h x (.inr ⟨q, hq, by simp [hx]⟩)
      simp [h1, h2, h3, h4]
  | ctors L S =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.ctors.injEq]
    refine ⟨map_self fun q hq => ?_, map_self fun q hq => ?_⟩
    · have h2 := h q.2 (.inl ⟨q, hq, by simp⟩)
      have h1 := map_self (l := q.1) fun x hx => h x (.inl ⟨q, hq, by simp [hx]⟩)
      simp [h1, h2]
    · have h2 := h q.2.1 (.inr ⟨q, hq, by simp⟩)
      have h3 := h q.2.2 (.inr ⟨q, hq, by simp⟩)
      have h1 := map_self (l := q.1) fun x hx => h x (.inr ⟨q, hq, by simp [hx]⟩)
      simp [h1, h2, h3]
  | pack a bs =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.pack.injEq]
    exact ⟨tuple_self fun x hx => h x (.inl hx),
      map_self fun t ht => tuple_self fun x hx => h x (.inr ⟨t, ht, hx⟩)⟩
  | _ => rfl

#print axioms normalize_sound
end Verification.Model.PositiveNormalization
