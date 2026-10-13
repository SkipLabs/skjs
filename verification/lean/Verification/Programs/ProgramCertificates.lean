import Verification.Programs.ProgramTyping
-- ../Types/QualifiedGraphs.lean checks lexical instances of schemes whose binders carry resolution descriptors; without it lexical body checking has no instance comparison.
import Verification.Types.QualifiedGraphs

/-! Finite program evidence checked against the declarative rules. Each node
states its sequent explicitly. The external entry point also checks that the
root is the requested closed program and type; evidence cannot change the task.
The evidence fixes its rule and premise tree. Coercion choices are validated
through the common engine, whose execution outcome is retained by `CheckResult`. -/
namespace Verification.ProgramCertificates
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules
open CallEffects (Arrow RestArrow MethodArrow Contract Effect)

structure Sequent (ι : Type) where
  context : List (Ty ι)
  term : Tm
  type : Ty ι
  deriving DecidableEq

/-- Validation scopes enclosing an unfinished comparison, outermost first. -/
inductive CheckFrame where
  | node (label : Nat)
  | code (index : Nat)
  | obligation (index : Nat)
  | request (index : Nat)
  deriving Repr, DecidableEq

/-- An incomplete subtype comparison, including its requested judgment. -/
structure Exhaustion (ι : Type) where
  source : Ty ι
  target : Ty ι
  limit : Nat
  rounds : Nat
  visited : Nat
  frames : List CheckFrame := []
  deriving Repr, DecidableEq

/-- The first graph node named by an unfinished comparison's validation scopes. -/
@[nospecialize] def Exhaustion.nodeLabel (stop : Exhaustion ι) : Option Nat :=
  (stop.frames.filterMap fun frame => match frame with
    | .node label => some label
    | .code _ | .obligation _ | .request _ => none).head?

/-- Compositional search and validation retain unfinished subtype work.
Successful proposal values require independent certificate validation. -/
structure CheckResult (ι α : Type) where
  value : Option α
  exhaustion : Option (Exhaustion ι) := none

/-- Attach diagnostic provenance without changing a validation value. -/
@[nospecialize] def CheckResult.at (s : CheckResult ι α) (frame : CheckFrame) : CheckResult ι α :=
  { s with exhaustion := s.exhaustion.map fun stop => { stop with frames := frame :: stop.frames } }

theorem CheckResult.value_at (s : CheckResult ι α) (frame : CheckFrame) : (s.at frame).value = s.value := rfl

@[nospecialize] def CheckResult.fromOption (o : Option α) : CheckResult ι α := ⟨o, none⟩

instance : Coe (Option α) (CheckResult ι α) := ⟨CheckResult.fromOption⟩

@[nospecialize] def CheckResult.bind (s : CheckResult ι α) (f : α → CheckResult ι β) : CheckResult ι β :=
  match s.value with
  | none => ⟨none, s.exhaustion⟩
  | some a =>
    let t := f a
    if t.value.isSome then t else { t with exhaustion := s.exhaustion <|> t.exhaustion }

instance : Monad (CheckResult ι) where
  pure a := ⟨some a, none⟩
  bind := CheckResult.bind

instance : MonadLift Option (CheckResult ι) where
  monadLift := CheckResult.fromOption

@[nospecialize] def CheckResult.orElse (s : CheckResult ι α) (next : Unit → CheckResult ι α) : CheckResult ι α :=
  match s.value with
  | some a => ⟨some a, none⟩
  | none =>
    let t := next ()
    if t.value.isSome then { t with exhaustion := none }
    else { t with exhaustion := s.exhaustion <|> t.exhaustion }

instance : Alternative (CheckResult ι) where
  failure := ⟨none, none⟩
  orElse := CheckResult.orElse

@[nospecialize] def CheckResult.map (f : α → β) (s : CheckResult ι α) : CheckResult ι β :=
  ⟨s.value.map f, if s.value.isSome then none else s.exhaustion⟩

/-- Try candidates in order, retaining exhaustion only when every candidate fails. -/
@[nospecialize] def _root_.List.findCheck? (xs : List β) (f : β → CheckResult ι α) : CheckResult ι α :=
  match xs with
  | [] => failure
  | x :: xs => (f x).orElse fun _ => xs.findCheck? f

@[nospecialize] def CheckResult.accepted (s : CheckResult ι α) : Bool := s.value.isSome

theorem CheckResult.accepted_at (s : CheckResult ι α) (frame : CheckFrame) :
    (s.at frame).accepted = s.accepted := rfl

@[nospecialize] def CheckResult.ofBool (b : Bool) : CheckResult ι Unit :=
  ⟨if b then some () else none, none⟩

theorem CheckResult.accepted_ofBool (b : Bool) : (CheckResult.ofBool (ι := ι) b).accepted = b := by
  cases b <;> rfl

theorem CheckResult.value_bind (s : CheckResult ι α) (f : α → CheckResult ι β) :
    (s.bind f).value = s.value.bind (fun a => (f a).value) := by
  cases s with
  | mk v e =>
    cases v with
    | none => rfl
    | some a =>
      simp only [CheckResult.bind, Option.bind_some]
      split <;> rfl

theorem CheckResult.accepted_bind_value (s : CheckResult ι α) (f : α → CheckResult ι β) :
    (s.bind f).accepted = s.value.any (fun a => (f a).accepted) := by
  rw [CheckResult.accepted, CheckResult.value_bind]
  cases s.value <;> rfl

theorem CheckResult.accepted_map (s : CheckResult ι α) (f : α → β) :
    (s.map f).accepted = s.accepted := by
  cases s with
  | mk v e => cases v <;> rfl

/-- Require a particular validated result, retaining unfinished work. -/
@[nospecialize] def CheckResult.expect [DecidableEq α] (s : CheckResult ι α) (expected : α) : CheckResult ι Unit :=
  s.bind fun actual => CheckResult.ofBool (decide (actual = expected))

theorem CheckResult.accepted_expect [DecidableEq α] (s : CheckResult ι α) (expected : α) :
    (s.expect expected).accepted = decide (s.value = some expected) := by
  cases s with
  | mk v e =>
    cases v with
    | none => rfl
    | some actual =>
      by_cases h : actual = expected <;>
        simp [CheckResult.expect, CheckResult.bind, CheckResult.ofBool, CheckResult.accepted, h]

theorem CheckResult.accepted_bind (s : CheckResult ι α) (t : CheckResult ι β) :
    (s.bind fun _ => t).accepted = (s.accepted && t.accepted) := by
  cases s with
  | mk v e =>
    cases v with
    | none => rfl
    | some a =>
      simp only [CheckResult.bind, CheckResult.accepted, Option.isSome_some, Bool.true_and]
      split <;> rfl

@[nospecialize] def CheckResult.all (xs : List β) (f : β → CheckResult ι Unit) : CheckResult ι Unit :=
  match xs with
  | [] => pure ()
  | x :: xs => (f x).bind fun _ => CheckResult.all xs f

theorem CheckResult.accepted_all (xs : List β) (f : β → CheckResult ι Unit) :
    (CheckResult.all xs f).accepted = xs.all (fun x => (f x).accepted) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [CheckResult.all, CheckResult.accepted_bind, ih, List.all_cons]

/-- Enumerate checks with their enclosing diagnostic scopes. -/
@[nospecialize] def CheckResult.allLocated (xs : List β) (frame : Nat → CheckFrame)
    (f : β → CheckResult ι Unit) : CheckResult ι Unit :=
  CheckResult.all xs.zipIdx fun (x, i) => (f x).at (frame i)

theorem CheckResult.accepted_allLocated (xs : List β) (frame : Nat → CheckFrame)
    (f : β → CheckResult ι Unit) :
    (CheckResult.allLocated xs frame f).accepted = xs.all (fun x => (f x).accepted) := by
  simp only [CheckResult.allLocated, CheckResult.accepted_all, CheckResult.accepted_at]
  have h := congrArg (fun ys => ys.all (fun x => (f x).accepted)) (List.zipIdx_map_fst 0 xs)
  simpa only [List.all_map, Function.comp_def] using h

/-- Disjunctive validation retains unfinished work if no alternative succeeds. -/
@[nospecialize] def CheckResult.any (xs : List β) (f : β → CheckResult ι Unit) : CheckResult ι Unit :=
  xs.findCheck? f

theorem CheckResult.accepted_orElse (s : CheckResult ι α) (t : Unit → CheckResult ι α) :
    (s.orElse t).accepted = (s.accepted || (t ()).accepted) := by
  cases s with
  | mk v e =>
    cases v with
    | none =>
      simp only [CheckResult.orElse, CheckResult.accepted, Option.isSome_none, Bool.false_or]
      split <;> rfl
    | some a => rfl

theorem CheckResult.accepted_any (xs : List β) (f : β → CheckResult ι Unit) :
    (CheckResult.any xs f).accepted = xs.any (fun x => (f x).accepted) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [CheckResult.any, List.findCheck?, CheckResult.accepted_orElse, List.any_cons]
    exact congrArg ((f x).accepted || ·) ih

theorem CheckResult.value_failure : (failure : CheckResult ι α).value = none := rfl

theorem CheckResult.value_map_const (s : CheckResult ι α) (b : β) :
    (s.map fun _ => b).value = if s.accepted then some b else none := by
  cases s with
  | mk v e => cases v <;> rfl

theorem CheckResult.value_bind_const (s : CheckResult ι α) (t : CheckResult ι β) :
    (s.bind fun _ => t).value = if s.accepted then t.value else none := by
  cases s with
  | mk v e =>
    cases v with
    | none => rfl
    | some a =>
      simp only [CheckResult.bind, CheckResult.accepted, Option.isSome_some, ite_true]
      split <;> rfl

theorem CheckResult.value_orElse (s : CheckResult ι α) (t : Unit → CheckResult ι α) :
    (s.orElse t).value = s.value.orElse fun _ => (t ()).value := by
  cases s with
  | mk v e =>
    cases v with
    | none =>
      simp only [CheckResult.orElse, Option.orElse]
      split <;> rfl
    | some a => rfl

/-- Convert the common subtype outcome while retaining the requested pair. -/
@[nospecialize] def CheckResult.fromComparison (limit : Nat) (A B : Ty ι)
    (r : PositiveCertificates.ComparisonResult α) : CheckResult ι α :=
  match r with
  | .established x => ⟨some x, none⟩
  | .notEstablished => ⟨none, none⟩
  | .exhausted rounds visited => ⟨none, some ⟨A, B, limit, rounds, visited, []⟩⟩

theorem CheckResult.accepted_fromComparison (limit : Nat) (A B : Ty ι)
    (r : PositiveCertificates.ComparisonResult α) :
    (CheckResult.fromComparison limit A B r).accepted = r.accepted := by
  cases r <;> rfl

/-- Validate supplied subtype choices through the common operation. -/
@[nospecialize] def checkSubtypeUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (A B : Ty ι)
    (choices : PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  CheckResult.fromComparison images.budget.rounds A B
    ((PositiveCertificates.compareUsing G images A B (choices.proposal G A B)
      (fun _ => choices.members)).map fun _ => ())

theorem checkSubtypeUsing_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (A B : Ty ι)
    (choices : PositiveCertificates.SubtypeChoices ι) :
    (checkSubtypeUsing G images A B choices).accepted = PositiveCertificates.checkUsing G images A B choices := by
  unfold checkSubtypeUsing PositiveCertificates.checkUsing
  rw [CheckResult.accepted_fromComparison, PositiveCertificates.ComparisonResult.accepted_map]

/-- What a literal index names in a tuple contract, as the checker reads it: a
required position's type; an optional or rest position's type with `undefined`;
any named position's type. -/
@[nospecialize] def requiredAt (T : Tuple (Ty ι)) (b : UInt64) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => T.required[k]?

@[nospecialize] def optionalAt (T : Tuple (Ty ι)) (b : UInt64) (U : Ty ι) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => match T.required[k]? with
    | some _ => none
    | none => (positionTy T k).map (· ++ U)

@[nospecialize] def namedAt (T : Tuple (Ty ι)) (b : UInt64) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => positionTy T k

inductive Rule (ι : Type) where
  | var | nul | undef | tru | fls | truLit | flsLit | numLit | num | strLit | str
  | bigintLit | bigint
  /-- Graph code: its captures, each a slot of the context at the type the
  code was checked with, are the premises; the code itself is an entry of the
  unit's checked code table. With a rest, `arrays` are the rest-store types of
  the variadic signatures, in their order. -/
  | funGraph (arrays : List (Ty ι))
  /-- A class value: construct-only graph code, checked at each construct
  signature with `undef`, the `undefined` type, for its receiver. -/
  | ctorGraph (undef : Ty ι)
  /-- A callable object: the bag's fields, then the captures of its graph
  code; `arrays` as for `funGraph`. -/
  | callableGraph (arrays : List (Ty ι))
  | app (effect : Effect)
  | letE | alloc | read | readView | write | arith | test
  /-- A read through an index over `keys`. -/
  | readDict (keys : IndexKeys) (element undef : Ty ι)
  /-- A computed read through an index over `keys`, of a key of `keyKeys`'s
  key clause. -/
  | indexDict (keys keyKeys : IndexKeys) (element undef : Ty ι)
  | readOptional (element undef : Ty ι)
  /-- A read through the prototype: the prototype's type. -/
  | readProto (proto : Ty ι)
  | arrLit | elem | setElem | len
  /-- A string's `length`. -/
  | lenStr
  /-- A string's code unit at a numeric index: the string and `undefined`
  types of the result. -/
  | elemStr (str undef : Ty ι)
  | elemOpt (undef : Ty ι)
  | elemAny (undef : Ty ι)
  | ifBool | ifTrue | ifFalse
  | ifKnown (answer : Bool)
  | ifBoolVar (trueType falseType : Ty ι)
  | unionVar (slot : Nat)
  | callCallable (effect : Effect)
  | readCallable | writeCallable
  /-- A copy of a spread, at the element type its store holds. -/
  | arrCopy (elem : Ty ι)
  /-- How many actuals are fixed, which later ones are spreads, and the rest
  type the further ones fit. -/
  | callRest (effect : Effect) (fixed omitted : Nat) (spreads : List Bool) (rest : Ty ι)
  /-- A bound function: its saved slots are read from the context. -/
  | bindE
  /-- A bound variadic function, likewise. -/
  | bindRestE
  /-- A member read from a slot's object and bound to that same object: for
  each fixed signature of the result, proofs that a member signature covers it,
  one per parameter, then the result; for each variadic signature, likewise,
  one per fixed parameter, then the rest, then the result; and one proof per
  type the member's host must meet, that the object's type is within it; or,
  with no proofs, the result one of the member's quantified signatures, a
  scheme. -/
  | bindMember (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
      (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι × PositiveCertificates.SubtypeChoices ι))
      (receivers : List (PositiveCertificates.SubtypeChoices ι))
  /-- `new`: the constructor, then the actuals in order. -/
  | construct
  | sub (proof : PositiveCertificates.SubtypeChoices ι)
  /-- `throw`: its operand at a type of its own. -/
  | throw
  /-- An allocation from parts: the accumulator, then the source. -/
  | merge

inductive Evidence (ι : Type) where
  | node (claim : Sequent ι) (rule : Rule ι) (premises : List (Evidence ι))

@[nospecialize] def claim : Evidence ι → Sequent ι
  | .node j _ _ => j

/-- The slots a prefix of saved variables names, when every entry is one. -/
def varSlots : List Tm → Option (List Nat)
  | [] => some []
  | .var i :: ts => (varSlots ts).map (i :: ·)
  | _ :: _ => none

theorem varSlots_map (saved : List Nat) : varSlots (saved.map .var) = some saved := by
  induction saved <;> simp_all [varSlots]

theorem varSlots_eq : ∀ {ts : List Tm} {saved : List Nat}, varSlots ts = some saved →
    ts = saved.map .var
  | [], _, h => by simp [varSlots] at h; subst h; rfl
  | .var i :: ts, saved, h => by
    simp only [varSlots, Option.map_eq_some_iff] at h
    obtain ⟨rest, hr, rfl⟩ := h
    simp [varSlots_eq hr]
  | .invoke .. :: _, _, h | .letE .. :: _, _, h | .nul :: _, _, h | .undef :: _, _, h
  | .tru :: _, _, h | .fls :: _, _, h | .num _ :: _, _, h | .str _ :: _, _, h
  | .objAt .. :: _, _, h | .makeAt .. :: _, _, h | .readAt .. :: _, _, h
  | .writeAt .. :: _, _, h | .test .. :: _, _, h | .ite .. :: _, _, h | .arith .. :: _, _, h
  | .arr _ :: _, _, h | .arrLit _ :: _, _, h | .elemAt .. :: _, _, h | .setElem .. :: _, _, h
  | .lenOf _ :: _, _, h | .spread _ :: _, _, h => by simp [varSlots] at h

theorem filterMap_of_map {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.map f = ys.map some → xs.filterMap f = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [h.1, filterMap_of_map h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The captures of graph code are slots below `n`. -/
def capSlotsBelow (caps : List Tm) (n : Nat) : Bool :=
  match varSlots caps with
  | some slots => slots.all (· < n)
  | none => false

/-- The scheme row a type is, if it is one. -/
@[nospecialize] def schemeOf (G : NormalGraph ι) : Ty ι → Option (ι × SchemeRow ι)
  | [i] => if G.params i then none else (G.schemes i).map (i, ·)
  | _ => none

theorem schemeOf_plain {G : NormalGraph ι} {A : Ty ι} (h : G.plainTy A = true) :
    schemeOf G A = none := by
  unfold schemeOf
  split
  · rename_i i
    have hi := NormalGraph.plain_iff.mp (List.all_eq_true.mp h i (by simp))
    simp [hi.1, hi.2.1]
  · rfl

/-- Every signature `(L, S)` offers is a checked entry of graph code with
captures at `Cs` (`CodeOffers`): without a rest, each offered row; with one,
no fixed signature and each variadic signature with its store type from `As`. -/
@[nospecialize] def offersChecked [DecidableEq ι] (G : NormalGraph ι) (codes : CodeEntry ι → Bool) (arity : Nat)
    (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (rest : Bool) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) (As : List (Ty ι)) : Bool :=
  match rest with
  | false => (offerRows L S).all fun p => codes ⟨arity, E, K, start, Cs, p, none⟩
  | true => L.isEmpty && S.length == As.length && (S.zip As).all fun q =>
      q.1.arguments.1.length == arity && decide (RestStore G q.2 q.1.arguments.2) &&
        codes ⟨arity, E, K, start, Cs, q.1.fixed, some q.2⟩

/-- Every signature the type `A` offers is a checked entry of graph code with
captures at `Cs`: an arrow type's signatures, or, for a generic closure, a
scheme row's, whose captures' types then read none of its binders. A table
entry is checked at every assignment of the parameter rows
(`CodesSound`), so at every instantiation of the scheme's binders. -/
@[nospecialize] def graphCodesChecked [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (codes : CodeEntry ι → Bool)
    (arity : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (start : Nat) (Cs : List (Ty ι)) (rest : Bool) (As : List (Ty ι)) : Bool :=
  match schemeOf G A with
  | some (_, s) => capturesFree G s Cs &&
      offersChecked G codes arity E K start Cs rest s.signatures s.variadic As
  | none =>
    match expand G A with
    | [.arrs L S] => offersChecked G codes arity E K start Cs rest L S As
    | _ => false

/-- A class value's construct signatures, each a checked entry of its graph
code at the row whose receiver is `U`, the `undefined` type `new` passes. -/
@[nospecialize] def ctorCodesChecked [DecidableEq ι] (G : NormalGraph ι) (A U : Ty ι) (codes : CodeEntry ι → Bool)
    (arity : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (start : Nat) (Cs : List (Ty ι)) : Bool :=
  match expand G A with
  | [.ctors L] => L.all fun p => codes ⟨arity, E, K, start, Cs, ⟨U, p.1, p.2, .unrestricted⟩, none⟩
  | _ => false

/-- The prototype type `P` has a field or view `f` at `A`. -/
@[nospecialize] def ProtoMember (G : NormalGraph ι) (P : Ty ι) (f : PropKey) (A : Ty ι) : Prop :=
  match expand G P with
  | [.refs gs [] ws _ _ _] => (f, A) ∈ gs ++ ws
  | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (P : Ty ι) (f : PropKey) (A : Ty ι) :
    Decidable (ProtoMember G P f A) := by
  unfold ProtoMember; split <;> infer_instance

/-- Proofs that the member signature `c` covers the claimed `q`: each claimed
parameter within the member's, then the member's result within the claimed. -/
@[nospecialize] def CallProofsUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι))
    (c : MethodArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) : Prop :=
  q.arguments.length = c.arguments.length ∧ ps.1.length = c.arguments.length ∧
    (∀ x ∈ (q.arguments.zip c.arguments).zip ps.1, PositiveCertificates.checkUsing G images x.1.1 x.1.2 x.2 = true) ∧
    PositiveCertificates.checkUsing G images c.result q.result ps.2 = true ∧ c.effect.covers q.effect = true

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (q c ps) : Decidable (CallProofsUsing G images q c ps) := by
  unfold CallProofsUsing; infer_instance

theorem CallProofsUsing.covered [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {q c ps}
    (h : CallProofsUsing G images q c ps) : CoveredCallUsing G images q c := by
  obtain ⟨hl, hp, hall, hr, he⟩ := h
  refine ⟨hl, fun x hx => ?_, ⟨_, hr⟩, he⟩
  obtain ⟨p, hxp⟩ := PositiveCertificates.exists_mem_zip (xs := q.arguments.zip c.arguments) (ys := ps.1)
    (by rw [List.length_zip, hl, Nat.min_self, hp]) x hx
  exact ⟨p, hall _ hxp⟩

/-- A choice for each member of a list, as a list alongside it. -/
theorem choose_list {α β : Type} {P : α → β → Prop} :
    ∀ xs : List α, (∀ x ∈ xs, ∃ y, P x y) →
      ∃ ys : List β, ys.length = xs.length ∧ ∀ xy ∈ xs.zip ys, P xy.1 xy.2
  | [], _ => ⟨[], rfl, by simp⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hl, hall⟩ := choose_list xs fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨y :: ys, by simp [hl], fun xy hxy => ?_⟩
    rcases List.mem_cons.mp hxy with rfl | hxy
    · exact hy
    · exact hall xy hxy

theorem CoveredCallUsing.proofs [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {q c}
    (h : CoveredCallUsing G images q c) : ∃ ps, CallProofsUsing G images q c ps := by
  obtain ⟨hl, hall, ⟨pr, hr⟩, he⟩ := h
  obtain ⟨ps, hpl, hps⟩ := choose_list (P := fun (x : Ty ι × Ty ι) p =>
    PositiveCertificates.checkUsing G images x.1 x.2 p = true) _ hall
  exact ⟨(ps, pr), hl, by simpa [List.length_zip, hl] using hpl, hps, hr, he⟩

/-- Proofs that the member's variadic signature `c` covers the claimed `q`:
each claimed fixed parameter within the member's, the claimed rest within the
member's, then the member's result within the claimed. -/
@[nospecialize] def RestProofsUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (q : RestArrow (Ty ι)) (c : CallEffects.MethodRestArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι × PositiveCertificates.SubtypeChoices ι) : Prop :=
  q.arguments.1.length = c.arguments.1.length ∧ ps.1.length = c.arguments.1.length ∧
    (∀ x ∈ (q.arguments.1.zip c.arguments.1).zip ps.1, PositiveCertificates.checkUsing G images x.1.1 x.1.2 x.2 = true) ∧
    PositiveCertificates.checkUsing G images q.arguments.2 c.arguments.2 ps.2.1 = true ∧
    PositiveCertificates.checkUsing G images c.result q.result ps.2.2 = true ∧ c.effect.covers q.effect = true

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (q c ps) : Decidable (RestProofsUsing G images q c ps) := by
  unfold RestProofsUsing; infer_instance

theorem RestProofsUsing.covered [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {q c ps}
    (h : RestProofsUsing G images q c ps) : CoveredRestUsing G images q c := by
  obtain ⟨hl, hp, hall, he, hr, heff⟩ := h
  refine ⟨hl, fun x hx => ?_, ⟨_, he⟩, ⟨_, hr⟩, heff⟩
  obtain ⟨p, hxp⟩ := PositiveCertificates.exists_mem_zip (xs := q.arguments.1.zip c.arguments.1) (ys := ps.1)
    (by rw [List.length_zip, hl, Nat.min_self, hp]) x hx
  exact ⟨p, hall _ hxp⟩

theorem CoveredRestUsing.proofs [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {q c}
    (h : CoveredRestUsing G images q c) : ∃ ps, RestProofsUsing G images q c ps := by
  obtain ⟨hl, hall, ⟨pe, he⟩, ⟨pr, hr⟩, heff⟩ := h
  obtain ⟨ps, hpl, hps⟩ := choose_list (P := fun (x : Ty ι × Ty ι) p =>
    PositiveCertificates.checkUsing G images x.1 x.2 p = true) _ hall
  exact ⟨(ps, pe, pr), hl, by simpa [List.length_zip, hl] using hpl, hps, he, hr, heff⟩

/-- Validate a fixed member signature, preserving each parameter/result comparison. -/
@[nospecialize] def checkCallProofs [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι)) (c : MethodArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide (q.arguments.length = c.arguments.length ∧
    ps.1.length = c.arguments.length) && c.effect.covers q.effect)).bind fun _ =>
    (CheckResult.all ((q.arguments.zip c.arguments).zip ps.1) fun x =>
      checkSubtypeUsing G images x.1.1 x.1.2 x.2).bind fun _ =>
      checkSubtypeUsing G images c.result q.result ps.2

theorem checkCallProofs_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι)) (c : MethodArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) :
    (checkCallProofs G images q c ps).accepted = decide (CallProofsUsing G images q c ps) := by
  simp only [checkCallProofs, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
    CheckResult.accepted_all, checkSubtypeUsing_accepted]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  unfold CallProofsUsing
  simp only [and_assoc, and_left_comm, and_comm]

/-- Validate a variadic member signature, including its rest and result. -/
@[nospecialize] def checkRestProofs [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : RestArrow (Ty ι))
    (c : CallEffects.MethodRestArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide (q.arguments.1.length = c.arguments.1.length ∧
    ps.1.length = c.arguments.1.length) && c.effect.covers q.effect)).bind fun _ =>
    (CheckResult.all ((q.arguments.1.zip c.arguments.1).zip ps.1) fun x =>
      checkSubtypeUsing G images x.1.1 x.1.2 x.2).bind fun _ =>
    (checkSubtypeUsing G images q.arguments.2 c.arguments.2 ps.2.1).bind fun _ =>
      checkSubtypeUsing G images c.result q.result ps.2.2

theorem checkRestProofs_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : RestArrow (Ty ι))
    (c : CallEffects.MethodRestArrow (Ty ι))
    (ps : List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι) :
    (checkRestProofs G images q c ps).accepted = decide (RestProofsUsing G images q c ps) := by
  simp only [checkRestProofs, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
    CheckResult.accepted_all, checkSubtypeUsing_accepted]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  unfold RestProofsUsing
  simp only [and_assoc, and_left_comm, and_comm]

/-- The bound member covers each claimed signature and accepts the host receiver. -/
@[nospecialize] def MemberProofsUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (host : Option (Ty ι)) (F : Ty ι) (k : PropKey)
    (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
    (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι)) (receivers : List (PositiveCertificates.SubtypeChoices ι)) : Prop :=
  match host, expand G F with
  | some O, [.arrs L S] => ∃ m ∈ (memberOf G O k).toList,
      proofs.length = L.length ∧ (∀ qp ∈ L.zip proofs, ∃ c ∈ m.calls, CallProofsUsing G images qp.1 c qp.2) ∧
      rests.length = S.length ∧ (∀ sp ∈ S.zip rests, ∃ c ∈ m.rests, RestProofsUsing G images sp.1 c sp.2) ∧
      receivers.length = m.receivers.length ∧
      (∀ tp ∈ m.receivers.zip receivers, PositiveCertificates.checkUsing G images O tp.1 tp.2 = true)
  | some O, _ => proofs = [] ∧ rests = [] ∧ receivers = [] ∧ expand G F = [] ∧
      ∃ m ∈ (memberOf G O k).toList, F ∈ m.schemes
  | none, _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (host F k proofs rests receivers) : Decidable (MemberProofsUsing G images host F k proofs rests receivers) := by
  unfold MemberProofsUsing
  split <;> infer_instance

/-- Check every signature using alternatives only among actual member signatures. -/
@[nospecialize] def checkMemberProofs [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (host : Option (Ty ι)) (F : Ty ι) (k : PropKey)
    (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
    (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι)) (receivers : List (PositiveCertificates.SubtypeChoices ι)) : CheckResult ι Unit :=
  match host, expand G F with
  | some O, [.arrs L S] => CheckResult.any (memberOf G O k).toList fun m =>
      (CheckResult.ofBool (decide (proofs.length = L.length ∧ rests.length = S.length ∧
        receivers.length = m.receivers.length))).bind fun _ =>
      (CheckResult.all (L.zip proofs) fun qp =>
        CheckResult.any m.calls fun c => checkCallProofs G images qp.1 c qp.2).bind fun _ =>
      (CheckResult.all (S.zip rests) fun sp =>
        CheckResult.any m.rests fun c => checkRestProofs G images sp.1 c sp.2).bind fun _ =>
      CheckResult.all (m.receivers.zip receivers) fun tp => checkSubtypeUsing G images O tp.1 tp.2
  | some O, _ => CheckResult.ofBool (decide (proofs = [] ∧ rests = [] ∧ receivers = [] ∧ expand G F = [] ∧
      ∃ m ∈ (memberOf G O k).toList, F ∈ m.schemes))
  | none, _ => failure

theorem checkMemberProofs_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (host : Option (Ty ι)) (F : Ty ι) (k : PropKey)
    (proofs : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι))
    (rests : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
      PositiveCertificates.SubtypeChoices ι)) (receivers : List (PositiveCertificates.SubtypeChoices ι)) :
    (checkMemberProofs G images host F k proofs rests receivers).accepted =
      decide (MemberProofsUsing G images host F k proofs rests receivers) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  unfold checkMemberProofs MemberProofsUsing
  unfold CheckResult.accepted
  split
  · change (CheckResult.any _ _).accepted = true ↔ _
    simp only [CheckResult.accepted_any, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
      CheckResult.accepted_all, checkSubtypeUsing_accepted, checkCallProofs_accepted, checkRestProofs_accepted]
    simp only [List.any_eq_true, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨m, hm, ⟨hp, hs, hr⟩, hcalls, hrests, hreceivers⟩
      exact ⟨m, hm, hp, hcalls, hs, hrests, hr, hreceivers⟩
    · rintro ⟨m, hm, hp, hcalls, hs, hrests, hr, hreceivers⟩
      exact ⟨m, hm, ⟨hp, hs, hr⟩, hcalls, hrests, hreceivers⟩
  · rw [← CheckResult.accepted, CheckResult.accepted_ofBool, decide_eq_true_eq]
  · change (false = true) ↔ False
    simp

/-- Each top-level label of a type replaced by the label it is aliased to. -/
@[nospecialize] def renameTy [DecidableEq ι] (aliases : List (ι × ι)) (A : Ty ι) : Ty ι :=
  A.map fun l => match aliases.find? (·.1 == l) with
    | some p => p.2
    | none => l

/-- Aliased labels denote the same values at every assignment the enclosing
scheme admits within its declared bounds. -/
def AliasesSound (G : NormalGraph ι) (source : SchemeRow ι) (aliases : List (ι × ι)) : Prop :=
  ∀ η As, As.length = source.binders.length → G.domain.allowed source As →
    (∀ m, Bounded (mixedMeaning G) η source As m) →
    ∀ p ∈ aliases, ∀ n W v,
      mixedMeaning G (assign η source.binders As) [p.1] n W (.inl v) ↔
        mixedMeaning G (assign η source.binders As) [p.2] n W (.inl v)

theorem renameTy_meaning [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {aliases : List (ι × ι)}
    (same : ∀ p ∈ aliases, ∀ n W v,
      mixedMeaning G η [p.1] n W (.inl v) ↔ mixedMeaning G η [p.2] n W (.inl v))
    (A : Ty ι) (n W v) :
    mixedMeaning G η (renameTy aliases A) n W (.inl v) ↔ mixedMeaning G η A n W (.inl v) := by
  let X := fun i => qDenoteWithArgs G (mixedParameters G) (η, i)
  have single : ∀ l, mixedMeaning G η [l] n W (.inl v) ↔ X l n W v := by
    intro l
    change (∃ i ∈ [l], X i n W v) ↔ _
    simp
  have label : ∀ l, X (match aliases.find? (·.1 == l) with
      | some p => p.2
      | none => l) n W v ↔ X l n W v := by
    intro l
    split
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have he : p.1 = l := by simpa using List.find?_some hp
      rw [← single, ← single, ← (same p hm n W v), he]
    · exact Iff.rfl
  change (∃ i ∈ renameTy aliases A, X i n W v) ↔ (∃ i ∈ A, X i n W v)
  simp only [renameTy, List.mem_map]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hv⟩
    exact ⟨l, hl, (label l).mp hv⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨_, ⟨l, hl, rfl⟩, (label l).mpr hv⟩

/-- Body subsumption without aliases: an ordinary comparison, or a qualified
callable instantiated with the complete resolution group from its enclosing
scheme. Ordinary comparisons and all instance-image, kind, signature and bound
checks use the shared checker. -/
@[nospecialize] def lexicalComparison [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (A B : Ty ι) (proof : PositiveCertificates.SubtypeChoices ι) : Bool :=
  PositiveCertificates.checkUsing G images A B proof ||
    match expand G B, proof.instantiation with
    | [.arrs L M], some inst =>
      (QualifiedGraphs.compareLexicalInstance G images source
        (fun U V state => (PositiveCertificates.ComparisonResult.fromBool
          (PositiveCertificates.checkUsing G images U V proof), state))
        () A L M inst ()).1.accepted
    | _, _ => false

/-- Body subsumption compares the two types as they are or, failing that,
with each aliased label read as its alias. -/
@[nospecialize] def lexicalBodyCheck [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (aliases : List (ι × ι)) (A B : Ty ι) (proof : PositiveCertificates.SubtypeChoices ι) : Bool :=
  lexicalComparison G images source A B proof ||
    (!aliases.isEmpty &&
      lexicalComparison G images source (renameTy aliases A) (renameTy aliases B) proof)

theorem lexicalComparison_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {source : SchemeRow ι}
    {N : Fam} {C : ResolutionDescriptors.Capabilities N}
    (domain : G.domain = ResolutionDescriptors.descriptorDomain C)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (length : As.length = source.binders.length) (allowed : G.domain.allowed source As)
    {A B : Ty ι} {proof : PositiveCertificates.SubtypeChoices ι}
    (checked : lexicalComparison G images source A B proof = true) (n W v)
    (hv : mixedMeaning G (assign η source.binders As) A n W (.inl v)) :
    mixedMeaning G (assign η source.binders As) B n W (.inl v) := by
  simp only [lexicalComparison, Bool.or_eq_true] at checked
  rcases checked with ordinary | lexical
  · exact PositiveCertificates.checkUsing_sound ordinary
      (assign η source.binders As) n W (.inl v) hv
  · split at lexical
    · rename_i L M inst target instanced
      have bounds : ∀ U V (prior : Unit),
          (PositiveCertificates.ComparisonResult.fromBool
            (PositiveCertificates.checkUsing G images U V proof)).accepted = true →
          FamLe (mixedMeaning G (assign η source.binders As) U)
            (mixedMeaning G (assign η source.binders As) V) := by
        intro U V _ h
        exact PositiveCertificates.checkUsing_sound
          (by simpa only [PositiveCertificates.ComparisonResult.accepted_fromBool] using h) _
      have step := QualifiedGraphs.compareLexicalInstance_sound G images source domain
        η As length allowed bounds lexical
      exact mixed_of_expand target (step n W v hv)
    · cases lexical

/-- The lexical check supplies precisely the subsumption premise consumed by
program typing, at an assignment permitted by the enclosing scheme within its
declared bounds. -/
@[nospecialize] def lexicalBodySubtyping [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    {N : Fam} {C : ResolutionDescriptors.Capabilities N}
    (domain : G.domain = ResolutionDescriptors.descriptorDomain C)
    (aliases : List (ι × ι)) (aliasesSound : AliasesSound G source aliases)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (length : As.length = source.binders.length) (allowed : G.domain.allowed source As)
    (bounded : ∀ m, Bounded (mixedMeaning G) η source As m) :
    BodySubtyping (reassign G (assign η source.binders As)) where
  check := lexicalBodyCheck G images source aliases
  sound := by
    intro A B proof checked
    simp only [lexicalBodyCheck, Bool.or_eq_true, Bool.and_eq_true] at checked
    rcases checked with direct | ⟨_, renamed⟩
    · exact fun n W v hv => lexicalComparison_sound domain η As length allowed direct n W v hv
    · have same := aliasesSound η As length allowed bounded
      intro n W v hv
      exact (renameTy_meaning same B n W v).mp
        (lexicalComparison_sound domain η As length allowed renamed n W v
          ((renameTy_meaning same A n W v).mpr hv))

#print axioms renameTy_meaning
#print axioms lexicalBodySubtyping

/-- Only finite, syntactic premises of one rule. -/
@[nospecialize] def LocalUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool := fun _ => false)
    (subtype : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool :=
      PositiveCertificates.checkUsing G images) : Prop :=
  match r with
  | .var =>
    match j.term, ps with
    | .var i, [] => j.context[i]? = some j.type
    | _, _ => False
  | .nul =>
    match j.term, ps with
    | .nul, [] => Represents G j.type .nul
    | _, _ => False
  | .undef =>
    match j.term, ps with
    | .undef, [] => Represents G j.type .undef
    | _, _ => False
  | .tru =>
    match j.term, ps with
    | .tru, [] => Represents G j.type .bool
    | _, _ => False
  | .fls =>
    match j.term, ps with
    | .fls, [] => Represents G j.type .bool
    | _, _ => False
  | .truLit =>
    match j.term, ps with
    | .tru, [] => Represents G j.type (.boolLit true)
    | _, _ => False
  | .flsLit =>
    match j.term, ps with
    | .fls, [] => Represents G j.type (.boolLit false)
    | _, _ => False
  | .numLit =>
    match j.term, ps with
    | .num b, [] => Represents G j.type (.numLit b)
    | _, _ => False
  | .num =>
    match j.term, ps with
    | .num _, [] => Represents G j.type .num
    | _, _ => False
  | .strLit =>
    match j.term, ps with
    | .str s, [] => Represents G j.type (.strLit s)
    | _, _ => False
  | .str =>
    match j.term, ps with
    | .str _, [] => Represents G j.type .str
    | _, _ => False
  | .bigintLit =>
    match j.term, ps with
    | .bigint i, [] => Represents G j.type (.bigintLit i)
    | _, _ => False
  | .bigint =>
    match j.term, ps with
    | .bigint _, [] => Represents G j.type .bigint
    | _, _ => False
  -- Graph code: one premise per capture, a slot of this context, at the type
  -- the code's table entry states; every signature the type offers is an
  -- entry of the unit's checked table.
  | .funGraph As =>
    match j.term, ps with
    | .makeAt (.graph arity E K start caps kind rest) ns inits, ps =>
      kind = .call ∧ ns = [codeField] ∧ inits = [Tm.nul] ∧ ps.map Sequent.term = caps ∧
      (∀ q ∈ ps, q.context = j.context) ∧ capSlotsBelow caps j.context.length = true ∧
      graphCodesChecked G j.type codes arity E K start (ps.map Sequent.type) rest As = true
    | _, _ => False
  -- A class value: as a function's code, construct-only, at its construct
  -- signatures with `undefined` for the receiver.
  | .ctorGraph U =>
    match j.term, ps with
    | .makeAt (.graph arity E K start caps kind rest) ns inits, ps =>
      kind = .construct ∧ rest = false ∧ ns = [codeField] ∧ inits = [Tm.nul] ∧ ps.map Sequent.term = caps ∧
      (∀ q ∈ ps, q.context = j.context) ∧ capSlotsBelow caps j.context.length = true ∧
      Represents G U .undef ∧
      ctorCodesChecked G j.type U codes arity E K start (ps.map Sequent.type) = true
    | _, _ => False
  -- A callable object: one premise per named field, then one per capture.
  | .callableGraph As =>
    match j.term, ps with
    | .makeAt (.graph arity E K start caps kind rest) ns inits, ps =>
      match expand G j.type with
      | [.callable P [] L S] =>
        kind = .call ∧ ns.Nodup ∧ ns.length = inits.length ∧
        (ps.take ns.length).map Sequent.term = inits ∧
        (∀ p ∈ ps, p.context = j.context) ∧
        P = ns.zip ((ps.take ns.length).map Sequent.type) ∧
        (ps.drop ns.length).map Sequent.term = caps ∧ capSlotsBelow caps j.context.length = true ∧
        offersChecked G codes arity E K start ((ps.drop ns.length).map Sequent.type) rest L S As = true
      | _ => False
    | _, _ => False
  -- The callee, then the receiver at the selected signature's receiver, then
  -- the actual premises in order, then one premise per position the signature
  -- declares and this call omits. Each of those proves `undefined` at its
  -- declared type: the value the machine binds there.
  | .app effect =>
    match j.term, ps with
    | .invoke f r args, jf :: jr :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
      (jas.take args.length).map Sequent.term = args ∧
      (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      match expand G jf.type with
      | [.arrs L _] => ⟨jr.type, jas.map Sequent.type, j.type, effect⟩ ∈ L
      | _ => False
    | _, _ => False
  | .letE =>
    match j.term, ps with
    | .letE a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb = ⟨ja.type :: j.context, b, j.type⟩
    | _, _ => False
  | .alloc =>
    match j.term, ps with
    | .makeAt .absent ns inits, ps =>
      match expand G j.type with
      | [.refs fs [] [] [] [] ks] =>
        ns.Nodup ∧ ns.length = ps.length ∧ ps.map Sequent.term = inits ∧
        (∀ p ∈ ps, p.context = j.context) ∧ fs = ns.zip (ps.map Sequent.type) ∧
        (∀ K ∈ ks, ∀ n ∈ ns, K.admits n = true) ∧ allocRealm G fs = true
      -- A literal allocated directly at a dictionary: each field an index's
      -- class may admit at exactly that index's type, each optional field
      -- absent (`HasTyUsing.allocDict`).
      | [.dict fs [] [] ix os [] [] cs] =>
        ns.Nodup ∧ CallArguments.protoField ∉ ns ∧ CallArguments.arrayStoreField ∉ ns ∧
        ns.length = ps.length ∧ ps.map Sequent.term = inits ∧
        (∀ p ∈ ps, p.context = j.context) ∧ fs = ns.zip (ps.map Sequent.type) ∧
        (∀ f ∈ fs, ∀ y ∈ ix ++ cs, y.1.may f.1 = true → f.2 = y.2) ∧
        (∀ o ∈ os, o.key ∉ ns) ∧
        (∀ o ∈ os, ∀ y ∈ cs, y.1.may o.key = true → o.type = y.2 ∨ PositiveRules.Uninhabited G y.2)
      | _ => False
    | _, _ => False
  | .read =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      (match expand G ja.type with
       | [c] => (f, j.type) ∈ ((namedMembers c).map Prod.fst).getD []
       | _ => False)
    | _, _ => False
  | .readView =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      (match expand G ja.type with
       | [c] => (f, j.type) ∈ ((namedMembers c).map Prod.snd).getD []
       | _ => False)
    | _, _ => False
  -- A key a bound of the object does not admit is read from its prototype `P`, which
  -- the object holds under the reserved key; `P`'s field or view gives the type.
  | .readProto P =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      (match expand G ja.type with
       | [.refs fs [] vs _ _ ks] =>
         (∃ K ∈ ks, K.admits f = false) ∧ (CallArguments.protoField, P) ∈ fs ++ vs ∧
         ProtoMember G P f j.type
       | _ => False)
    | _, _ => False
  | .readOptional A U =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G U .undef ∧ j.type = A ++ U ∧
      (match expand G ja.type with
       | [.refs _ [] _ os _ _] => ∃ o ∈ os, o.key = f ∧ o.type = A
       | _ => False)
    | _, _ => False
  | .readDict K A U =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G U .undef ∧ j.type = A ++ U ∧
      K.surely f = true ∧
      (match expand G ja.type with
       | [.dict _ [] _ ix _ _ _ _] => (K, A) ∈ ix
       | _ => False)
    | _, _ => False
  | .indexDict K KK A U =>
    match j.term, ps with
    | .indexAt a key, [ja, jk] =>
      ja.context = j.context ∧ ja.term = a ∧
      jk.context = j.context ∧ jk.term = key ∧
      Represents G jk.type (keyClause KK) ∧ KK.within K = true ∧
      Represents G U .undef ∧ j.type = A ++ U ∧
      (match expand G ja.type with
       | [.dict _ [] _ ix _ _ _ _] => (K, A) ∈ ix
       | _ => False)
    | _, _ => False
  | .write =>
    match j.term, ps with
    | .writeAt f a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      Represents G j.type .nul ∧
      (match expand G ja.type with
       | [.refs fs [] _ _ _ _] => (f, jb.type) ∈ fs
       | _ => False)
    | _, _ => False
  | .arith =>
    match j.term, ps with
    | .arith op a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      OperatorTypes G op ja.type jb.type j.type
    | _, _ => False
  | .test =>
    match j.term, ps with
    | .test _ a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      (.boolLit true) ∈ expand G j.type ∧ (.boolLit false) ∈ expand G j.type
    | _, _ => False
  | .arrLit =>
    match j.term, ps with
    | .arrLit inits, ps =>
      match expand G j.type with
      | [.list T []] =>
        ps.map Sequent.term = inits ∧ (∀ p ∈ ps, p.context = j.context) ∧
        T.required.length ≤ ps.length ∧
        (T.rest = none → ps.length ≤ T.required.length + T.optional.length) ∧
        ∀ q ∈ ps.zipIdx, positionTy T q.2 = some q.1.type
      | _ => False
    | _, _ => False
  | .elem =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      (match expand G ja.type, expand G ji.type with
       | [.list T []], [.numLit b] => requiredAt T b = some j.type
       | _, _ => False)
    | _, _ => False
  | .elemOpt U =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      Represents G U .undef ∧
      (match expand G ja.type, expand G ji.type with
       | [.list T []], [.numLit b] => optionalAt T b U = some j.type
       | _, _ => False)
    | _, _ => False
  | .elemAny U =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      Represents G U .undef ∧ Answers G ji.type .isNum true ∧
      (match expand G ja.type with
       | [.list ⟨[], [], some E, _, _⟩ []] => j.type = E ++ U
       | _ => False)
    | _, _ => False
  | .setElem =>
    match j.term, ps with
    | .setElem a i v, [ja, ji, jv] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      jv.context = j.context ∧ jv.term = v ∧ j.type = ja.type ∧
      (match expand G ja.type, expand G ji.type with
       | [.list T []], [.numLit b] =>
         -- At most the required length: in bounds or appending, never a hole.
         namedAt T b = some jv.type ∧ (indexOfBits b).getD 0 ≤ T.required.length ∧
           T.readonly = false
       | _, _ => False)
    | _, _ => False
  | .len =>
    match j.term, ps with
    | .lenOf a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G j.type .num ∧
      (match expand G ja.type with
       | [.list _ []] => True
       | _ => False)
    | _, _ => False
  | .lenStr =>
    match j.term, ps with
    | .lenOf a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧ Represents G j.type .num ∧
      Answers G ja.type .isStr true
    | _, _ => False
  | .elemStr T U =>
    match j.term, ps with
    | .elemAt a i, [ja, ji] =>
      ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
      Answers G ja.type .isStr true ∧ Answers G ji.type .isNum true ∧
      Represents G T .str ∧ Represents G U .undef ∧ j.type = T ++ U
    | _, _ => False
  | .ifBool =>
    match j.term, ps with
    | .ite c t e, [jc,jt,je] =>
      jc.context = j.context ∧ jc.term = c ∧ Answers G jc.type .isBool true ∧
      jt = ⟨j.context,t,j.type⟩ ∧ je = ⟨j.context,e,j.type⟩
    | _, _ => False
  | .ifKnown q =>
    match j.term, ps with
    | .ite c t e, [jc,jb] =>
      jc.context = j.context ∧ jc.term = c ∧ Represents G jc.type (.boolLit q) ∧
      jb = ⟨j.context, (if q then t else e), j.type⟩
    | _, _ => False
  | .ifBoolVar T F =>
    match j.term, ps with
    | .ite (.var i) t e, [jt,je] =>
      (match j.context[i]? with | some C => Answers G C .isBool true | none => False) ∧
      Represents G T (.boolLit true) ∧ Represents G F (.boolLit false) ∧
      jt = ⟨j.context.set i T,t,j.type⟩ ∧ je = ⟨j.context.set i F,e,j.type⟩
    | _, _ => False
  | .ifTrue =>
    match j.term, ps with
    | .ite (.test tag (.var i)) u _, [ju] =>
      ju = ⟨j.context, u, j.type⟩ ∧
      match j.context[i]? with
      | some A => Answers G A tag true
      | none => False
    | _, _ => False
  | .ifFalse =>
    match j.term, ps with
    | .ite (.test tag (.var i)) _ e, [je] =>
      je = ⟨j.context, e, j.type⟩ ∧
      match j.context[i]? with
      | some A => Answers G A tag false
      | none => False
    | _, _ => False
  | .unionVar i =>
    match j.term, ps with
    | _, ps =>
      match j.context[i]? with
      | some C => ps = C.map (fun a => ⟨j.context.set i [a], j.term, j.type⟩)
      | none => False
  | .callCallable effect =>
    match j.term, ps with
    | .invoke f r args, jf :: jr :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
      (jas.take args.length).map Sequent.term = args ∧
      (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      match expand G jf.type with
      | [.callable _ _ L _] => ⟨jr.type, jas.map Sequent.type,j.type, effect⟩ ∈ L
      | _ => False
    | _, _ => False
  | .readCallable =>
    match j.term, ps with
    | .readAt f a, [ja] =>
      ja.context = j.context ∧ ja.term = a ∧
      match expand G ja.type with
      | [.callable P _ _ _] => (f, j.type) ∈ P
      | _ => False
    | _, _ => False
  | .writeCallable =>
    match j.term, ps with
    | .writeAt f a b, [ja,jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      Represents G j.type .nul ∧
      match expand G ja.type with
      | [.callable P _ _ _] => (f, jb.type) ∈ P
      | _ => False
    | _, _ => False
  -- The one premise is the store the spread reads.
  | .arrCopy E =>
    match j.term, ps with
    | .arrLit [.spread s], [js] =>
      js.context = j.context ∧ js.term = s ∧ SpreadsInto G js.type E ∧
      match expand G j.type with
      | [.list ⟨[], [], some E', false, _⟩ []] => E = E'
      | _ => False
    | _, _ => False
  -- The callee, the receiver, the fixed actuals, one `undefined` premise per
  -- fixed position the call omits, then one premise per further part: the
  -- actual itself, or the store a spread reads. A call that omits a position
  -- writes no part.
  | .callRest effect k u flags P =>
    match j.term, ps with
    | .invoke f r args, jf :: jr :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      jas.length = k + u + flags.length ∧ (u = 0 ∨ flags = []) ∧
      args = (jas.take k).map Sequent.term ++
        (flags.zip (jas.drop (k + u))).map (fun q => spreadTerm (q.1, q.2.term)) ∧
      (∀ ja ∈ (jas.drop k).take u, ja.term = .undef) ∧
      RestParts G P ((flags.zip (jas.drop (k + u))).map fun q => (q.1, q.2.type)) ∧
      ⟨jr.type, ((jas.take (k + u)).map Sequent.type, P), j.type, effect⟩ ∈ restSigs G jf.type
    | _, _ => False
  -- `.bind`'s saved slots, with no premises: the target's selected signature
  -- starts with the prefix slots' contracts, and the result takes the rest at
  -- the one receiver it states, whatever that is.
  | .bindE =>
    match j.term, ps with
    | .makeAt (.bound (.var t) (.var r) pre) ns inits, [] =>
      ns = [] ∧ inits = [] ∧
      match varSlots pre, j.context[t]?, j.context[r]?, expand G j.type with
      | some saved, some T, some Rt, [.arrs [⟨_, Ds, R, effect⟩] []] =>
        saved.map (j.context[·]?) = (saved.filterMap (j.context[·]?)).map some ∧
        ⟨Rt, saved.filterMap (j.context[·]?) ++ Ds, R, effect⟩ ∈ callSigs G T
      | _, _, _, _ => False
    | _, _ => False
  -- As `bindE`, for a variadic signature of the target with an element rest:
  -- the prefix takes its first fixed positions, and past them the element.
  | .bindRestE =>
    match j.term, ps with
    | .makeAt (.bound (.var t) (.var r) pre) ns inits, [] =>
      ns = [] ∧ inits = [] ∧
      match varSlots pre, j.context[t]?, j.context[r]?, expand G j.type with
      | some saved, some T, some Rt, [.arrs [] [⟨_, (Ds, E'), R, effect⟩]] =>
        saved.map (j.context[·]?) = (saved.filterMap (j.context[·]?)).map some ∧
        ∃ s ∈ restSigs G T, s.receiver = Rt ∧ s.arguments.2 = E' ∧ s.result = R ∧ s.effect = effect ∧
          Ds = s.arguments.1.drop saved.length ∧ ∃ El ∈ (restElem G E').toList,
          saved.filterMap (j.context[·]?) =
            s.arguments.1.take saved.length ++ List.replicate (saved.length - s.arguments.1.length) El
      | _, _, _, _ => False
    | _, _ => False
  -- A member read from a slot's object and bound to that same object, with no
  -- premises: the result's signatures are the member's, at any receiver.
  | .bindMember proofs rests receivers =>
    match j.term, ps with
    | .letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var r) pre) ns inits),
      [] =>
      r = i + 1 ∧ pre = [] ∧ ns = [] ∧ inits = [] ∧
      MemberProofsUsing G images j.context[i]? j.type k proofs rests receivers
    | _, _ => False
  -- The constructor, the actual premises in order, then one premise per
  -- position the signature declares and `new` omits, proving `undefined`
  -- there, as for `.app`.
  | .construct =>
    match j.term, ps with
    | .construct f args, jf :: jas =>
      jf.context = j.context ∧ jf.term = f ∧ (jas.take args.length).map Sequent.term = args ∧
      (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
      (∀ ja ∈ jas, ja.context = j.context) ∧
      match expand G jf.type with
      | [.ctors L] => (jas.map Sequent.type, j.type) ∈ L
      | _ => False
    | _, _ => False
  | .sub proof =>
    match j.term, ps with
    | _, [jt] =>
      jt.context = j.context ∧ jt.term = j.term ∧
      subtype jt.type j.type proof = true
    | _, _ => False
  | .throw =>
    match j.term, ps with
    | .throw a, [ja] => ja.context = j.context ∧ ja.term = a ∧ SourceValues G ja.type
    | _, _ => False
  | .merge =>
    match j.term, ps with
    | .merge d a b, [ja, jb] =>
      ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
      ObjectMerge.MergeOk G d ja.type jb.type j.type = true
    | _, _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (j : Sequent ι) (r : Rule ι) (ps)
    (codes : CodeEntry ι → Bool)
    (subtype : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool) :
    Decidable (LocalUsing G images j r ps codes subtype) := by
  unfold LocalUsing
  split <;> (try split) <;> try infer_instance
  all_goals try dsimp [Represents, Answers]
  all_goals first | infer_instance | (split <;> infer_instance)

/-- Each evidence rule chooses its validator explicitly. Coercion checks
retain the subtype outcome; other rule predicates are their declarative checks. -/
@[nospecialize] def localCheckUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι)
    (ps : List (Sequent ι)) (codes : CodeEntry ι → Bool := fun _ => false) : CheckResult ι Unit :=
  match r with
  | .sub choices => match ps with
    | [jt] => if jt.context = j.context ∧ jt.term = j.term then
        checkSubtypeUsing G images jt.type j.type choices else failure
    | _ => failure
  | .bindMember proofs rests receivers => match j.term, ps with
    | .letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var r) pre) ns inits), [] =>
        (CheckResult.ofBool (decide (r = i + 1 ∧ pre = [] ∧ ns = [] ∧ inits = []))).bind fun _ =>
          checkMemberProofs G images j.context[i]? j.type k proofs rests receivers
    | _, _ => failure
  | .var | .nul | .undef | .tru | .fls | .truLit | .flsLit | .numLit | .num | .strLit | .str
    | .bigintLit | .bigint | .funGraph .. | .ctorGraph .. | .callableGraph .. | .app ..
    | .letE | .alloc | .read | .readView | .write | .arith | .test | .readDict .. | .indexDict ..
    | .readOptional .. | .readProto .. | .arrLit | .elem | .setElem | .len | .lenStr | .elemStr ..
    | .elemOpt .. | .elemAny .. | .ifBool | .ifTrue | .ifFalse | .ifKnown .. | .ifBoolVar ..
    | .unionVar .. | .callCallable .. | .readCallable | .writeCallable | .arrCopy ..
    | .callRest .. | .bindE | .bindRestE | .construct | .throw | .merge =>
      CheckResult.ofBool (decide (LocalUsing G images j r ps codes))

theorem localCheckUsing_accepted [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι)
    (ps : List (Sequent ι)) (codes : CodeEntry ι → Bool) :
    (localCheckUsing G images j r ps codes).accepted = decide (LocalUsing G images j r ps codes) := by
  cases r <;> try exact CheckResult.accepted_ofBool _
  case bindMember proofs rests receivers =>
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    simp only [localCheckUsing, CheckResult.accepted]
    split
    · change ((CheckResult.ofBool _).bind _).accepted = true ↔ _
      simp only [CheckResult.accepted_bind, CheckResult.accepted_ofBool,
        checkMemberProofs_accepted, Bool.and_eq_true, decide_eq_true_eq]
      rename_i heq
      unfold LocalUsing
      simp only [heq, and_assoc]
    · change (false = true) ↔ LocalUsing G images j (.bindMember proofs rests receivers) _ codes
      simp only [Bool.false_eq_true, false_iff]
      intro h
      unfold LocalUsing at h
      split at h <;> simp_all
  case sub choices =>
    cases ps with
    | nil => rfl
    | cons jt ps =>
      cases ps with
      | cons x xs => rfl
      | nil =>
        by_cases h : jt.context = j.context ∧ jt.term = j.term
        · have hL : LocalUsing G images j (.sub choices) [jt] codes ↔
              jt.context = j.context ∧ jt.term = j.term ∧
                PositiveCertificates.checkUsing G images jt.type j.type choices = true := Iff.rfl
          simp [localCheckUsing, h, checkSubtypeUsing_accepted, hL]
        · have hf : ¬ LocalUsing G images j (.sub choices) [jt] codes := by
            intro hp
            exact h ⟨hp.1, hp.2.1⟩
          simp only [localCheckUsing, if_neg h, decide_eq_false hf]
          rfl

/-- Check the evidence tree once, retaining unfinished subtype work. -/
@[nospecialize] def checkTreeResult [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) : CheckResult ι Unit :=
  match e with
  | .node j r ps => (localCheckUsing G images j r (ps.map claim) codes).bind fun _ =>
      CheckResult.all ps.attach (fun e => checkTreeResult G images e.val codes)
termination_by sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem e.property
  simp only [Evidence.node.sizeOf_spec]
  omega

@[nospecialize] def checkTreeUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  (checkTreeResult G images e codes).accepted

/-- The acceptance projection has exactly the declarative rule premises. -/
theorem checkTreeUsing_eq [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) (r : Rule ι)
    (ps : List (Evidence ι)) (codes : CodeEntry ι → Bool) :
    checkTreeUsing G images (.node j r ps) codes =
      (decide (LocalUsing G images j r (ps.map claim) codes) &&
        ps.attach.all (fun e => checkTreeUsing G images e.val codes)) := by
  rw [checkTreeUsing, checkTreeResult, CheckResult.accepted_bind, CheckResult.accepted_all,
    localCheckUsing_accepted]
  rfl

mutual
def checkScope (d : Nat) : Tm → Bool
  | .var i => decide (i < d)
  | .objAt _ .absent _ => true
  | .objAt _ (.bound t r pre) _ => checkScope d t && checkScope d r && checkScopes d pre
  | .makeAt (.bound t r pre) _ args =>
      checkScope d t && checkScope d r && checkScopes d pre && checkScopes d args
  | .makeAt .absent _ args => checkScopes d args
  | .letE a b => checkScope d a && checkScope (d+1) b
  | .invoke f r args => checkScope d f && checkScope d r && checkScopes d args
  | .construct f args => checkScope d f && checkScopes d args
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b | .merge _ a b =>
      checkScope d a && checkScope d b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => checkScope d a
  | .setElem a b c => checkScope d a && checkScope d b && checkScope d c
  | .arrLit args => checkScopes d args
  | .ite c a b => checkScope d c && checkScope d a && checkScope d b
  | .objAt _ (.graph _ _ _ _ caps _ _) _ => checkScopes d caps
  | .makeAt (.graph _ _ _ _ caps _ _) _ args => checkScopes d caps && checkScopes d args
  | .goto _ _ _ L x => checkScopes d L && checkScope d x
  | .frame _ _ t L x _ _ => checkScope d t && checkScopes d L && checkScope d x
  | _ => true

def checkScopes (d : Nat) : List Tm → Bool
  | [] => true
  | a :: args => checkScope d a && checkScopes d args
end

@[simp] theorem checkScopes_iff (d : Nat) (args : List Tm) :
    checkScopes d args = true ↔ ∀ a ∈ args, checkScope d a = true := by
  induction args <;> simp_all [checkScopes]

theorem checkScope_iff (d : Nat) (t : Tm) : checkScope d t = true ↔ Scoped d t := by
  induction t using Tm.induct generalizing d <;> simp_all [checkScope, Scoped, and_assoc]

/-- Bind evidence to the actual requested program, type and empty context.
Scope includes unselected branches and bodies of empty overloads. -/
@[nospecialize] def checkUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) (t : Tm) (A : Ty ι) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  decide (claim e = ⟨[], t, A⟩) && checkScope 0 t && checkTreeUsing G images e codes

/-- A code table is sound when each entry's code meets its signature in the
graph reassigned at every assignment of its parameter rows: a code check reads
no assignment (`Parametricity`), so a checked table is sound at all of them,
which is what a generic closure's creation needs (`HasTyUsing.funScheme`). -/
@[nospecialize] def CodesSound (G : NormalGraph ι) (codes : CodeEntry ι → Bool) : Prop :=
  ∀ c, codes c = true → ∀ η, c.Spec (reassign G η)

theorem codesSound_none (G : NormalGraph ι) : CodesSound G (fun _ => false) := by
  intro c h; cases h

/-- A generic body's code entries hold at the assignments admitted by its
own scheme. All three resolution projections are retained by that assignment. -/
@[nospecialize] def SchemeCodesSound (G : NormalGraph ι) (s : SchemeRow ι)
    (codes : CodeEntry ι → Bool) : Prop :=
  ∀ c, codes c = true → ∀ η As, As.length = s.binders.length →
    G.domain.allowed s As → c.Spec (reassign G (assign η s.binders As))

/-- Unconditionally checked code also meets a scheme's permitted assignments. -/
theorem CodesSound.scheme {G : NormalGraph ι} {codes : CodeEntry ι → Bool}
    (h : CodesSound G codes) (s : SchemeRow ι) : SchemeCodesSound G s codes :=
  fun c hc η As _ _ => h c hc (assign η s.binders As)

/-- Checked signatures use the body's actual permitted binder assignment. -/
theorem schemeOffersChecked_sound [DecidableEq ι] {G : NormalGraph ι}
    {s : SchemeRow ι} {codes : CodeEntry ι → Bool}
    (hcodes : SchemeCodesSound G s codes) {arity : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {start : Nat}
    {Cs : List (Ty ι)} {rest : Bool} {stores : List (Ty ι)}
    (h : offersChecked G codes arity E K start Cs rest s.signatures s.variadic stores = true)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (hlen : As.length = s.binders.length) (ha : G.domain.allowed s As) :
    CodeOffers (reassign G (assign η s.binders As)) arity E K start Cs rest
      s.signatures s.variadic stores := by
  cases rest with
  | false =>
    simp only [offersChecked, List.all_eq_true] at h
    exact fun p hp => hcodes _ (h p hp) η As hlen ha
  | true =>
    simp only [offersChecked, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨hL, hslen⟩, hall⟩ := h
    exact ⟨hL, hslen, fun q hq => ⟨(hall q hq).1.1, (hall q hq).1.2,
      hcodes _ (hall q hq).2 η As hlen ha⟩⟩

/-- The checker establishes code formation independently of whether a scheme
has an admitted instance. -/
theorem offersChecked_shape [DecidableEq ι] {G : NormalGraph ι}
    {codes : CodeEntry ι → Bool} {arity E K start Cs rest L S stores}
    (h : offersChecked G codes arity E K start Cs rest L S stores = true) :
    CodeOffersShape G arity rest L S stores := by
  cases rest with
  | false => trivial
  | true =>
    simp only [offersChecked, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.isEmpty_iff] at h
    exact ⟨h.1.1, h.1.2, fun q hq => (h.2 q hq).1⟩

/-- A generic closure is certified by its code table at the scheme's permitted
assignments and by the ordinary capture and code-formation checks. -/
theorem funScheme_of_checked [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G}
    {Γ : List (Ty ι)} {j : ι} {s : SchemeRow ι}
    {codes : CodeEntry ι → Bool} (hcodes : SchemeCodesSound G s codes)
    {arity start : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {caps : List (Ty ι × Nat)} {rest : Bool} {stores : List (Ty ι)}
    (hp : G.params j = false) (hs : G.schemes j = some s)
    (hc : offersChecked G codes arity E K start (caps.map Prod.fst) rest
      s.signatures s.variadic stores = true)
    (hfree : capturesFree G s (caps.map Prod.fst) = true)
    (hlt : ∀ c ∈ caps, c.2 < Γ.length)
    (hcap : ∀ c ∈ caps, HasTyUsing G images (subtyping := subtyping) Γ (.var c.2) c.1) :
    HasTyUsing G images (subtyping := subtyping) Γ
      (.makeFn (.graph arity E K start (caps.map fun c => .var c.2) .call rest) .nul) [j] :=
  .funScheme hp hs (schemeOffersChecked_sound hcodes hc) (offersChecked_shape hc) hfree hlt hcap

#print axioms schemeOffersChecked_sound
#print axioms funScheme_of_checked

/-- A checked offer holds at every assignment: each entry does (`CodesSound`),
and a store type is read through the graph's rows only. -/
theorem offersChecked_sound [DecidableEq ι] {G : NormalGraph ι} {codes : CodeEntry ι → Bool}
    (hcodes : CodesSound G codes) {arity : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {start : Nat}
    {Cs : List (Ty ι)} {rest : Bool} {L : List (Arrow (Ty ι))}
    {S : List (RestArrow (Ty ι))} {As : List (Ty ι)}
    (h : offersChecked G codes arity E K start Cs rest L S As = true) :
    ∀ η, CodeOffers (reassign G η) arity E K start Cs rest L S As := by
  intro η
  cases rest with
  | false =>
    simp only [offersChecked, List.all_eq_true] at h
    exact fun p hp => hcodes _ (h p hp) η
  | true =>
    simp only [offersChecked, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨hL, hlen⟩, hall⟩ := h
    exact ⟨hL, hlen, fun q hq => ⟨(hall q hq).1.1, (hall q hq).1.2, hcodes _ (hall q hq).2 η⟩⟩

/-- Premises naming slots of the context are the captures of graph code: each
a slot below the context's length, typed there. -/
theorem caps_of_local [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G} {Γ : List (Ty ι)}
    {ps : List (Sequent ι)} (hctx : ∀ q ∈ ps, q.context = Γ)
    (hslots : capSlotsBelow (ps.map Sequent.term) Γ.length = true)
    (hp : ∀ p ∈ ps, HasTyUsing G images (subtyping := subtyping) p.context p.term p.type) :
    ∃ caps : List (Ty ι × Nat), caps.map (fun c => Tm.var c.2) = ps.map Sequent.term ∧
      caps.map Prod.fst = ps.map Sequent.type ∧ (∀ c ∈ caps, c.2 < Γ.length) ∧
      ∀ c ∈ caps, HasTyUsing G images (subtyping := subtyping) Γ (.var c.2) c.1 := by
  unfold capSlotsBelow at hslots
  split at hslots
  · rename_i slots hvs
    have hterms := varSlots_eq hvs
    have hlen : (ps.map Sequent.type).length = slots.length := by
      have := congrArg List.length hterms
      simpa using this
    let caps := (ps.map Sequent.type).zip slots
    have hvar : caps.map (fun c => Tm.var c.2) = ps.map Sequent.term := by
      rw [hterms]
      have : caps.map Prod.snd = slots := List.map_snd_zip (by omega)
      rw [← this, List.map_map]; rfl
    have hfst : caps.map Prod.fst = ps.map Sequent.type := List.map_fst_zip (by omega)
    have hlt : ∀ c ∈ caps, c.2 < Γ.length := fun c hc => by
      have := List.of_mem_zip hc
      exact of_decide_eq_true (List.all_eq_true.mp hslots c.2 this.2)
    have hcap : ∀ c ∈ caps, HasTyUsing G images (subtyping := subtyping) Γ (.var c.2) c.1 := fun c hc => by
      obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hc
      have hi' : i < ps.length := by simp [caps] at hi; omega
      have hsl : i < slots.length := by simp [caps] at hi; omega
      rw [List.getElem_zip] at hci
      subst hci
      have hq := hp ps[i] (List.getElem_mem hi')
      have ht : ps[i].term = .var slots[i] := by
        have := congrArg (·[i]?) hterms
        simp [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hsl] at this
        exact this
      rw [hctx _ (List.getElem_mem hi'), ht] at hq
      simpa using hq
    exact ⟨caps, hvar, hfst, hlt, hcap⟩
  · contradiction

/-- A graph code creation whose captures are slots and whose signatures the
table has checked is derivable. -/
theorem funGraph_of_local [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G} {Γ : List (Ty ι)} {A : Ty ι}
    {codes : CodeEntry ι → Bool} (hcodes : CodesSound G codes) {arity start : Nat}
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {rest : Bool} {As : List (Ty ι)}
    {ps : List (Sequent ι)} (hctx : ∀ q ∈ ps, q.context = Γ)
    (hslots : capSlotsBelow (ps.map Sequent.term) Γ.length = true)
    (hok : graphCodesChecked G A codes arity E K start (ps.map Sequent.type) rest As = true)
    (hp : ∀ p ∈ ps, HasTyUsing G images (subtyping := subtyping) p.context p.term p.type) :
    HasTyUsing G images (subtyping := subtyping) Γ (.makeFn (.graph arity E K start (ps.map Sequent.term) .call rest) .nul) A := by
  obtain ⟨caps, hvar, hfst, hlt, hcap⟩ := caps_of_local hctx hslots hp
  rw [← hvar]
  unfold graphCodesChecked at hok
  split at hok
  · -- A generic closure: its type is a scheme row.
    rename_i i s hs
    simp only [Bool.and_eq_true] at hok
    unfold schemeOf at hs
    split at hs
    · rename_i i'
      split at hs
      · cases hs
      · rename_i hpar
        obtain ⟨s', hq, he⟩ := Option.map_eq_some_iff.mp hs
        cases he
        exact funScheme_of_checked (caps := caps) (E := E) (K := K) (start := start) (arity := arity)
          (hcodes.scheme s) (by simpa using hpar) hq
          (by rw [hfst]; exact hok.2) (by rw [hfst]; exact hok.1) hlt hcap
    · cases hs
  · split at hok
    · rename_i L S hL
      exact HasTyUsing.funGraph (caps := caps) (E := E) (K := K) (start := start) (arity := arity) hL
        (by rw [hfst]; exact offersChecked_sound hcodes hok G.env) hlt hcap
    · contradiction

theorem local_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {subtyping : BodySubtyping G} {j r ps} {codes : CodeEntry ι → Bool}
    (hl : LocalUsing G images j r ps codes subtyping.check) (hcodes : CodesSound G codes)
    (hp : ∀ p ∈ ps, HasTyUsing G images (subtyping := subtyping) p.context p.term p.type) : HasTyUsing G images (subtyping := subtyping) j.context j.term j.type := by
  rcases j with ⟨Γ, t, A⟩
  unfold LocalUsing at hl
  split at hl <;> (try split at hl) <;> (try contradiction) <;> (try dsimp only at *) <;> (try subst t)
  · exact .var hl
  · exact .nul hl
  · exact .undef hl
  · exact .tru hl
  · exact .fls hl
  · exact .truLit hl
  · exact .flsLit hl
  · exact .numLit hl
  · exact .num hl
  · exact .strLit hl
  · exact .str hl
  · exact .bigintLit hl
  · exact .bigint hl
  · rename_i As ps _ _ arity E K start caps kind rest ns inits
    obtain ⟨rfl, rfl, rfl, hterms, hctx, hslots, hok⟩ := hl
    subst caps
    exact funGraph_of_local hcodes hctx hslots hok hp
  · rename_i U ps _ _ arity E K start caps kind rest ns inits
    obtain ⟨rfl, rfl, rfl, rfl, hterms, hctx, hslots, hu, hok⟩ := hl
    subst caps
    obtain ⟨caps, hvar, hfst, hlt, hcap⟩ := caps_of_local hctx hslots hp
    rw [← hvar]
    unfold ctorCodesChecked at hok
    split at hok
    · rename_i L hL
      simp only [List.all_eq_true] at hok
      exact HasTyUsing.ctorGraph hL hu (fun p hp' => by rw [hfst]; exact hcodes _ (hok p hp') G.env)
        hlt hcap
    · contradiction
  · split at hl
    · rename_i _ As ps _ _ arity E K start caps kind rest ns inits _ P L S hF
      obtain ⟨rfl, hnd, hlen, hterms, hctx, rfl, hcaps, hslots, hok⟩ := hl
      have hctxd : ∀ q ∈ ps.drop ns.length, q.context = Γ :=
        fun q hq => hctx q (List.mem_of_mem_drop hq)
      have hpd : ∀ q ∈ ps.drop ns.length, HasTyUsing G images (subtyping := subtyping) q.context q.term q.type :=
        fun q hq => hp q (List.mem_of_mem_drop hq)
      obtain ⟨caps', hvar, hfst, hlt, hcap⟩ :=
        caps_of_local hctxd (by rw [hcaps]; exact hslots) hpd
      subst caps
      rw [← hvar]
      have htl : (ps.take ns.length).length = ns.length := by
        have := congrArg List.length hterms
        simp only [List.length_map] at this
        omega
      let parts := (ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)
      have hfst' : parts.map Prod.fst = ns := by
        simp only [parts, List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : parts.map (fun p => p.2.2) = inits := by
        rw [← hterms]
        simp only [parts, List.map_map, Function.comp_def]
        calc (ns.zip (ps.take ns.length)).map (fun r => r.2.term)
            = ((ns.zip (ps.take ns.length)).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = (ps.take ns.length).map Sequent.term := by
              rw [List.map_snd_zip (by omega)]
      have hP : parts.map (fun p => (p.1, p.2.1)) =
          ns.zip ((ps.take ns.length).map Sequent.type) := by
        simp only [parts, List.map_map, Function.comp_def]
        rw [List.zip_map_right]
        simp []
      have hpart : ∀ p ∈ parts, HasTyUsing G images (subtyping := subtyping) Γ p.2.2 p.2.1 := by
        intro p hm
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
        have hmem := List.of_mem_zip hr
        have h := hp r.2 (List.mem_of_mem_take hmem.2)
        rw [hctx r.2 (List.mem_of_mem_take hmem.2)] at h
        exact h
      have := HasTyUsing.callableGraph (G := G) (images := images) (Γ := Γ) (F := A) (parts := parts) (caps := caps')
        (E := E) (K := K) (start := start) (arity := arity) (rest := rest) (As := As)
        (by rw [hP]; exact hF) (by rw [hfst']; exact hnd) hpart
        (by rw [hfst]; exact offersChecked_sound hcodes hok G.env) hlt hcap
      rw [hfst', hsnd] at this
      exact this
    · contradiction
  · rename_i f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    split at hL
    · rename_i L he
      -- The actual premises and the omitted-position premises are the same list,
      -- split at the number of actuals the call writes.
      have ha : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type,ja.term)),
          HasTyUsing G images (subtyping := subtyping) Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hcontexts ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTyUsing G images (subtyping := subtyping) Γ .undef A := by
        intro A hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja)))
        rw [hcontexts ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type,ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      have h := HasTyUsing.app hf he (xs := (jas.take args.length).map (fun ja => (ja.type,ja.term)))
        (Us := (jas.drop args.length).map Sequent.type)
        (by rw [hsplit]; exact hL) hrt ha hu
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓ, ht, rfl⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    exact .letE ha (hp ⟨ja.type :: Γ, b, A⟩ (by simp))
  · rename_i _ ps _ _ ns inits
    split at hl
    · rename_i fs ks he
      obtain ⟨hnd, hlen, hterms, hctx, rfl, hk, hreal⟩ := hl
      have hzl : (ns.zip ps).length = ns.length := by simp [hlen]
      have hfst : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map (fun p => p.2.2)
          = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip ps).map (fun r => r.2.term)
            = ((ns.zip ps).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = ps.map Sequent.term := by rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip (ps.map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTyUsing.alloc (G := G) (images := images) (Γ := Γ) (Ref := A)
        (parts := (ns.zip ps).map fun r => (r.1, r.2.type, r.2.term))
        (by rw [hfst]; exact hnd)
        (by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := (List.of_mem_zip (by simpa using hr)).2
          have h := hp r.2 hmem
          rw [hctx r.2 hmem] at h
          exact h)
        (by rw [htyp]; exact he)
        (by
          intro K hK q hq
          have : q.1 ∈ ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst :=
            List.mem_map_of_mem hq
          rw [hfst] at this
          exact hk K hK q.1 this)
        (by rw [htyp]; exact hreal)
      rw [hfst, hsnd] at this
      exact this
    · rename_i fs ix os cs he
      obtain ⟨hnd, hnp, hns, hlen, hterms, hctx, rfl, hix, habs, hos⟩ := hl
      have hfst : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map (fun p => p.2.2)
          = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip ps).map (fun r => r.2.term)
            = ((ns.zip ps).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = ps.map Sequent.term := by rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip (ps.map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTyUsing.allocDict (G := G) (images := images) (Γ := Γ) (Ref := A)
        (parts := (ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)) (ix := ix) (cs := cs) (os := os)
        (by rw [hfst]; exact hnd) (by rw [hfst]; exact hnp) (by rw [hfst]; exact hns)
        (by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := (List.of_mem_zip (by simpa using hr)).2
          have h := hp r.2 hmem
          rw [hctx r.2 hmem] at h
          exact h)
        (by rw [htyp]; exact he)
        (by
          intro q hq y hy hm
          have : (q.1, q.2.1) ∈ ns.zip (ps.map Sequent.type) := by
            rw [← htyp]; exact List.mem_map_of_mem hq
          exact hix _ this y hy hm)
        (by rw [hfst]; exact habs) hos
      rw [hfst, hsnd] at this
      exact this
    · contradiction
  · rename_i f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i c he
      cases hc : namedMembers c with
      | none => simp [hc] at hr
      | some m => simp only [hc, Option.map_some, Option.getD_some] at hr; exact .read ha he hc hr
    · contradiction
  · rename_i f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i c he
      cases hc : namedMembers c with
      | none => simp [hc] at hr
      | some m => simp only [hc, Option.map_some, Option.getD_some] at hr; exact .readView ha he hc hr
    · contradiction
  · rename_i P _ _ f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs ks he
      obtain ⟨⟨K, hK, hf⟩, hpr, hP⟩ := hr
      unfold ProtoMember at hP
      split at hP
      · rename_i gs ws ks' hPe
        exact .readProto ha he hK hf hpr hPe hP
      · contradiction
    · contradiction
  · rename_i A U _ _ f a ja
    rcases hl with ⟨hΓ, ht, hUnd, eq, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs os he
      subst eq
      obtain ⟨⟨f', r, A'⟩, ho, hf, hA⟩ := hr
      simp only at hf hA
      subst hf hA
      exact .readOptional ha he ho hUnd
    · contradiction
  · rename_i K A U _ _ f a ja
    rcases hl with ⟨hΓ, ht, hUnd, eq, hsure, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs ix os he
      subst eq
      exact .readDict ha he hr hsure hUnd
    · contradiction
  · rename_i K KK E U _ _ a key ja jk
    rcases hl with ⟨hΓa, hta, hΓk, htk, hStr, hwithin, hUnd, eq, hr⟩
    have ha := hp ja (by simp)
    have hk := hp jk (by simp)
    rw [hΓa, hta] at ha
    rw [hΓk, htk] at hk
    split at hr
    · rename_i fs vs ix os he
      subst eq
      exact .indexDict ha he hk hStr hwithin hr hUnd
    · contradiction
  · rename_i f a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hn, hr⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    split at hr
    · rename_i fs vs os he
      exact .write ha he hr hb hn
    · contradiction
  · rename_i op a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hops⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    exact .arith ha hb hops
  · rename_i k a ja
    rcases hl with ⟨hΓ, hta, ht, hf⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .test ha ht hf
  · rename_i _ psl x ps' inits
    split at hl
    · rename_i T hT
      obtain ⟨hterms, hctx, hreq, hbound, hpos⟩ := hl
      subst hterms
      have hmap : psl.map Sequent.term = (psl.map fun p => (p.type, p.term)).map Prod.snd := by
        simp [List.map_map, Function.comp_def]
      rw [hmap]
      refine HasTyUsing.arrLit (xs := psl.map fun p => (p.type, p.term)) hT
        (by simpa using hreq) (by simpa using hbound) ?_ ?_
      · intro q hq
        rw [List.zipIdx_map] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact hpos p hp
      · intro p hmem
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        have := hp q hq
        rw [hctx q hq] at this
        exact this
    · contradiction
  · rename_i a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i T b hT hI
      simp only [requiredAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hA⟩ := hr
      exact .elem ha hT hi hI hk hA
    · contradiction
  · rename_i U _ _ a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hU, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i T b hT hI
      simp only [optionalAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hr⟩ := hr
      split at hr
      · cases hr
      · rename_i hnone
        simp only [Option.map_eq_some_iff] at hr
        obtain ⟨A, hA, rfl⟩ := hr
        exact .elemOpt ha hT hi hI hk hnone hA hU
    · contradiction
  · rename_i U _ _ a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hU, hq, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i E ro presence hT
      rw [hr]
      exact .elemAny ha hT hi hq hU
    · contradiction
  · rename_i a i v ja ji jv
    rcases hl with ⟨hΓa, hta, hΓi, hti, hΓv, htv, hty, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    have hv := hp jv (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    rw [hΓv, htv] at hv
    rw [hty]
    split at hr
    · rename_i T b hT hI
      obtain ⟨hr, hkle, hro⟩ := hr
      simp only [namedAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hA⟩ := hr
      rw [hk] at hkle
      exact .setElem ha hT hi hI hk hA hkle hro hv
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ, hta, hn, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    split at hr
    · rename_i T hT
      exact .len ha hT hn
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ, hta, hn, hs⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .lenStr ha hs hn
  · rename_i T U _ _ a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hs, hq, hT, hU, hty⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    rw [hty]
    exact .elemStr ha hs hi hq hT hU
  · rename_i c t e jc jt je
    rcases hl with ⟨hΓ, hc, hb, rfl, rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ, hc] at hcond
    exact .ifBool hcond hb (hp ⟨Γ,t,A⟩ (by simp)) (hp ⟨Γ,e,A⟩ (by simp))
  · rename_i q _ _ c t e jc jb
    rcases hl with ⟨hΓ,hc,hq,rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ,hc] at hcond
    exact .ifKnown hcond hq (hp ⟨Γ,(if q then t else e),A⟩ (by simp))
  · rename_i T F _ _ i t e jt je
    rcases hl with ⟨hb,hT,hF,rfl,rfl⟩
    split at hb
    · rename_i C hc
      exact .ifBoolVar hc hb hT hF (hp ⟨Γ.set i T,t,A⟩ (by simp)) (hp ⟨Γ.set i F,e,A⟩ (by simp))
    · contradiction
  · rename_i tag i u e ju
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (fun _ => hp ⟨Γ, u, A⟩ (by simp)) (by intro h; cases h)
    · contradiction
  · rename_i tag i u e je
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (by intro h; cases h) (fun _ => hp ⟨Γ, e, A⟩ (by simp))
    · contradiction
  · rename_i i ps _ _
    split at hl
    · rename_i C hi
      apply HasTyUsing.unionVar hi
      intro a ha
      apply hp ⟨Γ.set i [a], _, A⟩
      rw [hl]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩
    · contradiction
  · rename_i f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    split at hL
    · rename_i P Ps L he
      -- The actual premises and the omitted-position premises are the same list,
      -- split at the number of actuals the call writes.
      have ha : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type,ja.term)),
          HasTyUsing G images (subtyping := subtyping) Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hcontexts ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTyUsing G images (subtyping := subtyping) Γ .undef A := by
        intro A hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja)))
        rw [hcontexts ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type,ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      have h := HasTyUsing.callCallable hf he (xs := (jas.take args.length).map (fun ja => (ja.type,ja.term)))
        (Us := (jas.drop args.length).map Sequent.type)
        (by rw [hsplit]; exact hL) hrt ha hu
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ,ht,hL⟩
    have ha := hp ja (by simp)
    rw [hΓ,ht] at ha
    split at hL
    · rename_i P Ps L he
      exact .readCallable ha he hL
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓa,hta,hΓb,htb,hn,hL⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa,hta] at ha
    rw [hΓb,htb] at hb
    split at hL
    · rename_i P Ps L he
      exact .writeCallable ha he hL hb hn
    · contradiction
  · rename_i E _ _ s js
    rcases hl with ⟨hΓ, ht, hsp, hr⟩
    have h := hp js (by simp)
    rw [hΓ, ht] at h
    split at hr
    · rename_i E' presence hT
      cases hr
      exact .arrCopy h hsp hT
    · contradiction
  · rename_i k u flags P _ _ f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hctx, hlen, hshort, rfl, hundef, hparts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    have htake : jas.take (k + u) = jas.take k ++ (jas.drop k).take u := List.take_add ..
    have := HasTyUsing.callRest (xs := (jas.take k).map fun ja => (ja.type, ja.term))
      (Us := ((jas.drop k).take u).map Sequent.type) (P := P)
      (parts := (flags.zip (jas.drop (k + u))).map fun q => (q.1, q.2.type, q.2.term)) hf
      (by rw [htake] at hL; simpa [List.map_append, List.map_map, Function.comp_def] using hL) hrt
      (by
        intro p hm
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hctx ja (List.mem_of_mem_take hja)] at h
        exact h)
      (by
        intro A hA
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hA
        have hmem : ja ∈ jas := List.mem_of_mem_drop (List.mem_of_mem_take hja)
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem))
        rw [hctx ja hmem, hundef ja hja] at h
        exact h)
      (by rcases hshort with h | h <;> simp [h])
      (by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        have hja := List.mem_of_mem_drop (List.of_mem_zip hq).2
        have h := hp q.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hja))
        rw [hctx q.2 hja] at h
        exact h)
      (by simpa [List.map_map, Function.comp_def] using hparts)
    simpa [List.map_map, Function.comp_def] using this
  · obtain ⟨rfl, rfl, hl⟩ := hl
    split at hl
    · rename_i hsaved hT hRt hF
      obtain ⟨hmap, hsig⟩ := hl
      rw [varSlots_eq hsaved]
      exact HasTyUsing.bindE hT hsig hRt hmap hF
    · contradiction
  · obtain ⟨rfl, rfl, hl⟩ := hl
    split at hl
    · rename_i hsaved hT hRt hF
      obtain ⟨hmap, ⟨Rt', ⟨Ps, E'⟩, R', ef⟩, hmem, h1, h2, h3, hef, h4, El, hEl, h5⟩ := hl
      simp only at h1 h2 h3 hef h4 h5
      subst h1 h2 h3 hef h4
      rw [varSlots_eq hsaved]
      exact HasTyUsing.bindRestE hT hmem (by simpa using hEl) hRt hmap h5 hF
    · contradiction
  · obtain ⟨rfl, rfl, rfl, rfl, hl⟩ := hl
    unfold MemberProofsUsing at hl
    split at hl
    · rename_i O L S hO hF
      obtain ⟨m, hm, hlen, hL, hrlen, hS, hvlen, hV⟩ := hl
      exact HasTyUsing.bindMember hO (by simpa using hm) hF (fun q hq => by
        obtain ⟨pp, hpp⟩ := PositiveCertificates.exists_mem_zip hlen q hq
        obtain ⟨c, hc, hcp⟩ := hL _ hpp
        exact ⟨c, hc, hcp.covered⟩) (fun s hs => by
        obtain ⟨pp, hpp⟩ := PositiveCertificates.exists_mem_zip hrlen s hs
        obtain ⟨c, hc, hcp⟩ := hS _ hpp
        exact ⟨c, hc, hcp.covered⟩) (fun T hT => by
        obtain ⟨pp, hpp⟩ := PositiveCertificates.exists_mem_zip hvlen T hT
        exact ⟨pp, hV _ hpp⟩)
    · rename_i O hO _
      obtain ⟨-, -, -, hE, m, hm, hF⟩ := hl
      exact HasTyUsing.bindScheme hO (by simpa using hm) hF hE
    · contradiction
  · rename_i f args jf jas
    rcases hl with ⟨hΓf, htf, hterms, hundef, hctx, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    split at hL
    · rename_i L he
      have hxs : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type, ja.term)),
          HasTyUsing G images (subtyping := subtyping) Γ p.2 p.1 := by
        intro p hp'
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hp'
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_of_mem_take hja))
        rw [hctx ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTyUsing G images (subtyping := subtyping) Γ .undef A := by
        intro A hm
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja))
        rw [hctx ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type, ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      have hc := HasTyUsing.construct (xs := (jas.take args.length).map fun ja => (ja.type, ja.term))
        (Us := (jas.drop args.length).map Sequent.type) hf he
        (by rw [hsplit]; exact hL) hxs hu
      simpa only [List.map_map, Function.comp_def, hterms] using hc
    · contradiction
  · rename_i proof _ t jt
    rcases hl with ⟨hΓ, ht, hc⟩
    have hj := hp jt (by simp)
    rw [hΓ, ht] at hj
    exact .sub hj hc
  · rename_i a ja
    rcases hl with ⟨hΓ, hta, hA⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .throw hA ha
  · rename_i d a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hm⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    exact .merge ha hb hm

theorem checkTreeUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (e : Evidence ι)
    {codes : CodeEntry ι → Bool} (he : checkTreeUsing G images e codes = true)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    HasTyUsing G images (claim e).context (claim e).term (claim e).type := by
  cases e with
  | node j r ps =>
    simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
    apply local_sound he.1 hcodes
    intro p hp
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hp
    exact checkTreeUsing_sound e (he.2 ⟨e, he'⟩ (by simp)) hcodes
termination_by sizeOf e

/-- Expression evidence under a body's subsumption rule. The rule and every
premise are checked, including closure captures and the checked code table. -/
@[nospecialize] def checkTreeWith [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G)
    (subtype : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool)
    (e : Evidence ι) (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  match e with
  | .node j r ps => decide (LocalUsing G images j r (ps.map claim) codes subtype) &&
      ps.attach.all (fun p => checkTreeWith G images subtype p.val codes)
termination_by sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem p.property
  simp only [Evidence.node.sizeOf_spec]
  omega

theorem checkTreeWith_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (subtyping : BodySubtyping G)
    (e : Evidence ι) {codes : CodeEntry ι → Bool}
    (he : checkTreeWith G images subtyping.check e codes = true)
    (hcodes : CodesSound G codes) :
    HasTyUsing G images (subtyping := subtyping)
      (claim e).context (claim e).term (claim e).type := by
  cases e with
  | node j r ps =>
    simp only [checkTreeWith, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
    apply local_sound he.1 hcodes
    intro p hp
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hp
    exact checkTreeWith_sound subtyping e (he.2 ⟨e, he'⟩ (by simp)) hcodes
termination_by sizeOf e

#print axioms checkTreeWith_sound

theorem checkUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {t A e} {codes : CodeEntry ι → Bool}
    (he : checkUsing G images t A e codes = true) (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    Scoped 0 t ∧ HasTyUsing G images [] t A := by
  simp only [checkUsing, Bool.and_eq_true, decide_eq_true_eq] at he
  refine ⟨(checkScope_iff 0 t).mp he.1.2, ?_⟩
  have ht := checkTreeUsing_sound e he.2 hcodes
  simpa only [he.1.1] using ht

theorem acceptedUsing_safe [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {t A e} {codes : CodeEntry ι → Bool}
    (he : checkUsing G images t A e codes = true) (n W h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    Safe (meaning G A) n W h t :=
  (checkUsing_sound he hcodes).2.closed_safe (checkUsing_sound he hcodes).1 n W h hw hh

/-- Every offer graph code meets is checked when every entry is admitted. -/
theorem offersChecked_complete [DecidableEq ι] {G : NormalGraph ι} {arity : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {start : Nat}
    {Cs : List (Ty ι)} {rest : Bool} {L : List (Arrow (Ty ι))}
    {S : List (RestArrow (Ty ι))} {As : List (Ty ι)}
    (h : CodeOffers G arity E K start Cs rest L S As) :
    offersChecked G (fun _ => true) arity E K start Cs rest L S As = true := by
  cases rest with
  | false => simp [offersChecked]
  | true =>
    obtain ⟨rfl, hlen, hs⟩ := h
    simp only [offersChecked, List.isEmpty_nil, hlen, beq_self_eq_true, Bool.and_true,
      Bool.true_and, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact fun q hq => ⟨(hs q hq).1, (hs q hq).2.1⟩

/-- Captures that are slots of the context name slots below its length. -/
theorem capSlots_complete {Γ : List (Ty ι)} {caps : List (Ty ι × Nat)}
    (hlt : ∀ c ∈ caps, c.2 < Γ.length) :
    capSlotsBelow (caps.map fun c => Tm.var c.2) Γ.length = true := by
  have hv : varSlots (caps.map fun c => Tm.var c.2) = some (caps.map Prod.snd) := by
    have := varSlots_map (caps.map Prod.snd)
    simpa [List.map_map, Function.comp_def] using this
  simp only [capSlotsBelow, hv, List.all_eq_true, List.mem_map]
  rintro _ ⟨c, hc, rfl⟩
  exact decide_eq_true (hlt c hc)

/-- Evidence for a sequent, with every graph code admitted: coverage of the
rules, where which code a unit has checked is not the question. -/
@[nospecialize] def RepresentableUsing [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) (j : Sequent ι) : Prop :=
  ∃ e, claim e = j ∧ checkTreeUsing G images e (fun _ => true) = true

private theorem gather [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} (js : List (Sequent ι))
    (h : ∀ j ∈ js, RepresentableUsing G images j) :
    ∃ es : List (Evidence ι), es.map claim = js ∧ ∀ e ∈ es, checkTreeUsing G images e (fun _ => true) = true := by
  induction js with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons j js ih =>
    obtain ⟨e, he, hc⟩ := h j (by simp)
    obtain ⟨es, hes, hcs⟩ := ih (fun k hk => h k (by simp [hk]))
    refine ⟨e :: es, by simp [he, hes], ?_⟩
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | hm
    · exact hc
    · exact hcs e' hm

private theorem node_complete [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {j r js}
    (hl : LocalUsing G images j r js (fun _ => true)) (h : ∀ p ∈ js, RepresentableUsing G images p) :
    RepresentableUsing G images j := by
  obtain ⟨es, hes, hcs⟩ := gather js h
  refine ⟨.node j r es, rfl, ?_⟩
  simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨by simpa only [hes] using hl, fun e _ => hcs e.val e.property⟩

/-- Every declarative derivation has finite accepted evidence. This is coverage
of the rules, not semantic completeness and not a proof-search algorithm. -/
theorem checkTreeUsing_complete [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {Γ t A}
    (ht : HasTyUsing G images Γ t A) : RepresentableUsing G images ⟨Γ, t, A⟩ := by
  induction ht with
  | var hi => exact node_complete (r := .var) (js := []) hi (by simp)
  | nul hr => exact node_complete (r := .nul) (js := []) hr (by simp)
  | undef hr => exact node_complete (r := .undef) (js := []) hr (by simp)
  | tru hr => exact node_complete (r := .tru) (js := []) hr (by simp)
  | fls hr => exact node_complete (r := .fls) (js := []) hr (by simp)
  | truLit hr => exact node_complete (r := .truLit) (js := []) hr (by simp)
  | flsLit hr => exact node_complete (r := .flsLit) (js := []) hr (by simp)
  | numLit hr => exact node_complete (r := .numLit) (js := []) hr (by simp)
  | num hr => exact node_complete (r := .num) (js := []) hr (by simp)
  | strLit hr => exact node_complete (r := .strLit) (js := []) hr (by simp)
  | str hr => exact node_complete (r := .str) (js := []) hr (by simp)
  | bigintLit hr => exact node_complete (r := .bigintLit) (js := []) hr (by simp)
  | bigint hr => exact node_complete (r := .bigint) (js := []) hr (by simp)
  | @funGraph Γ F L S arity start E K caps rest As hr hspec hlt hcap ih =>
    apply node_complete (r := .funGraph As)
      (j := ⟨Γ, .makeFn (.graph arity E K start (caps.map fun c => .var c.2) .call rest) .nul, F⟩)
      (js := caps.map fun c => ⟨Γ, .var c.2, c.1⟩)
    · refine ⟨rfl, rfl, rfl, by simp, ?_, capSlots_complete hlt, ?_⟩
      · intro q hq
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
        rfl
      · have hmap : (caps.map fun c => (⟨Γ, .var c.2, c.1⟩ : Sequent ι)).map Sequent.type =
            caps.map Prod.fst := by simp
        simp only [graphCodesChecked, schemeOf_plain (Represents.plain hr),
          show expand G F = [.arrs L S] from hr, hmap]
        exact offersChecked_complete hspec
    · intro j hj
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hj
      exact ih c hc
  | @funScheme Γ i s arity start E K caps rest As hp hq _hspec hshape hcf hlt hcap ih =>
    apply node_complete (r := .funGraph As)
      (j := ⟨Γ, .makeFn (.graph arity E K start (caps.map fun c => .var c.2) .call rest) .nul, [i]⟩)
      (js := caps.map fun c => ⟨Γ, .var c.2, c.1⟩)
    · refine ⟨rfl, rfl, rfl, by simp, ?_, capSlots_complete hlt, ?_⟩
      · intro q hq
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
        rfl
      · have hmap : (caps.map fun c => (⟨Γ, .var c.2, c.1⟩ : Sequent ι)).map Sequent.type =
            caps.map Prod.fst := by simp
        simp only [graphCodesChecked, schemeOf, hp, hq, hmap, hcf, Bool.false_eq_true,
          if_false, Option.map_some, Bool.true_and]
        cases rest with
        | false => simp [offersChecked]
        | true =>
          obtain ⟨hL, hlen, hs⟩ := hshape
          simpa only [offersChecked, hL, List.isEmpty_nil, hlen, beq_self_eq_true,
            Bool.and_true, Bool.true_and, List.all_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] using hs
    · intro j hj
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hj
      exact ih c hc
  | @ctorGraph Γ F U L arity start E K caps hr hu hspec hlt hcap ih =>
    apply node_complete (r := .ctorGraph U)
      (j := ⟨Γ, .makeFn (.graph arity E K start (caps.map fun c => .var c.2) .construct) .nul, F⟩)
      (js := caps.map fun c => ⟨Γ, .var c.2, c.1⟩)
    · refine ⟨rfl, rfl, rfl, rfl, by simp, ?_, capSlots_complete hlt, hu, ?_⟩
      · intro q hq
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
        rfl
      · simp [ctorCodesChecked, show expand G F = [.ctors L] from hr]
    · intro j hj
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hj
      exact ih c hc
  | @callableGraph Γ F L S arity start E K caps rest As parts hr hnd hpart hspec hlt hcap ih ihc =>
    apply node_complete (r := .callableGraph As)
      (j := ⟨Γ, .makeAt (.graph arity E K start (caps.map fun c => .var c.2) .call rest)
        (parts.map Prod.fst) (parts.map fun p => p.2.2), F⟩)
      (js := (parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩) ++ caps.map fun c => ⟨Γ, .var c.2, c.1⟩)
    · unfold LocalUsing; simp only [
        show expand G F = [.callable (parts.map fun p => (p.1, p.2.1)) [] L S] from hr]
      have hlenp : (parts.map fun p => (⟨Γ, p.2.2, p.2.1⟩ : Sequent ι)).length
          = (parts.map Prod.fst).length := by simp
      refine ⟨trivial, hnd, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.take_left' hlenp]
        simp [List.map_map, Function.comp_def]
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
          rfl
        · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
          rfl
      · rw [List.take_left' hlenp]
        simp [List.map_map, Function.comp_def, List.zip_map']
      · rw [List.drop_left' hlenp]
        simp [List.map_map, Function.comp_def]
      · exact capSlots_complete hlt
      · rw [List.drop_left' hlenp]
        have hmap : (caps.map fun c => (⟨Γ, .var c.2, c.1⟩ : Sequent ι)).map Sequent.type =
            caps.map Prod.fst := by simp
        rw [hmap]
        exact offersChecked_complete hspec
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
        exact ih p hp
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hj
        exact ihc c hc
  | @callCallable effect Γ f r F Rt B P Ps L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    apply node_complete (r := .callCallable effect)
      (js := ⟨Γ,f,F⟩ :: ⟨Γ,r,Rt⟩ :: (xs.map (fun p => ⟨Γ,p.2,p.1⟩) ++ Us.map (fun A => ⟨Γ,.undef,A⟩)))
    · have hlenx : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))).length
          = (xs.map Prod.snd).length := by simp
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
      · rw [List.take_left' hlenx]
        simp only [List.map_map,Function.comp_def]
      · rw [List.drop_left' hlenx]
        intro ja hj
        obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
        rfl
      · intro ja hj
        rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          rfl
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          rfl
      · have heq : ((xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))
            ++ Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).map Sequent.type)
            = xs.map Prod.fst ++ Us := by
          rw [List.map_append, List.map_map, List.map_map]
          simp [Function.comp_def]
        rw [show expand G F = [.callable P Ps L S] from hr, heq]
        exact hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihrt
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          exact iha p hp
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          exact ihu A hA
  | @readCallable Γ a F P Ps L S f A ha hr hm ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ,.readAt f a,A⟩) (r := .readCallable) (js := [⟨Γ,a,F⟩])
    · unfold LocalUsing; simpa [show expand G F = [.callable P Ps L S] from hr] using hm
    · simpa using ih
  | @writeCallable Γ a F P Ps L S f A b N ha hr hm hb hn iha ihb =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ,.writeAt f a b,N⟩) (r := .writeCallable)
      (js := [⟨Γ,a,F⟩,⟨Γ,b,A⟩])
    · exact ⟨rfl,rfl,rfl,rfl,hn,by
        simp only [show expand G F = [.callable P Ps L S] from hr]
        exact hm⟩
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl
      · exact iha
      · exact ihb
  | @construct Γ f F B L xs Us hf hr hp hx hu ihf ihx ihu =>
    apply node_complete (r := .construct)
      (js := ⟨Γ,f,F⟩ :: (xs.map (fun p => ⟨Γ,p.2,p.1⟩) ++ Us.map (fun A => ⟨Γ,.undef,A⟩)))
    · have hlenx : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))).length
          = (xs.map Prod.snd).length := by simp
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [List.take_left' hlenx]
        simp only [List.map_map, Function.comp_def]
      · rw [List.drop_left' hlenx]
        intro ja hj
        obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hj
        rfl
      · intro ja hj
        rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
          rfl
        · obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hj
          rfl
      · have heq : ((xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))
            ++ Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).map Sequent.type)
            = xs.map Prod.fst ++ Us := by
          rw [List.map_append, List.map_map, List.map_map]
          simp [Function.comp_def]
        rw [show expand G F = [.ctors L] from hr, heq]
        exact hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
          exact ihx p hp
        · obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hj
          exact ihu A hA
  | @app effect Γ f r F Rt B L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    apply node_complete (r := .app effect)
      (js := ⟨Γ,f,F⟩ :: ⟨Γ,r,Rt⟩ :: (xs.map (fun p => ⟨Γ,p.2,p.1⟩) ++ Us.map (fun A => ⟨Γ,.undef,A⟩)))
    · have hlenx : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))).length
          = (xs.map Prod.snd).length := by simp
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
      · rw [List.take_left' hlenx]
        simp only [List.map_map,Function.comp_def]
      · rw [List.drop_left' hlenx]
        intro ja hj
        obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
        rfl
      · intro ja hj
        rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          rfl
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          rfl
      · have heq : ((xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))
            ++ Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).map Sequent.type)
            = xs.map Prod.fst ++ Us := by
          rw [List.map_append, List.map_map, List.map_map]
          simp [Function.comp_def]
        rw [show expand G F = [.arrs L S] from hr, heq]
        exact hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihrt
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          exact iha p hp
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          exact ihu A hA
  | @letE Γ a A b B ha hb iha ihb =>
    apply node_complete (r := .letE) (js := [⟨Γ,a,A⟩, ⟨A::Γ,b,B⟩])
    · exact ⟨rfl, rfl, rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact iha
      · exact ihb
  | @alloc Γ Ref parts ks hnd hpart hr hk hreal ih =>
    apply node_complete (G := G) (images := images)
      (j := ⟨Γ, .makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2), Ref⟩)
      (r := .alloc) (js := parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩)
    · unfold LocalUsing; simp only [show expand G Ref = [.refs (parts.map fun p => (p.1, p.2.1)) [] [] [] [] ks] from hr]
      refine ⟨hnd, by simp, by simp [List.map_map, Function.comp_def], by
        intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; rfl, ?_, ?_, hreal⟩
      · simp only [List.map_map, Function.comp_def]
        rw [List.zip_map']
      · intro K hK n hn
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
        exact hk K hK p hp
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @allocDict Γ Ref parts ix cs os hnd hnp hns hpart hr hix habs hos ih =>
    apply node_complete (G := G) (images := images)
      (j := ⟨Γ, .makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2), Ref⟩)
      (r := .alloc) (js := parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩)
    · unfold LocalUsing; simp only [show expand G Ref =
        [.dict (parts.map fun p => (p.1, p.2.1)) [] [] ix os [] [] cs] from hr]
      refine ⟨hnd, hnp, hns, by simp, by simp [List.map_map, Function.comp_def], by
        intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; rfl, ?_, ?_, habs, hos⟩
      · simp only [List.map_map, Function.comp_def]
        rw [List.zip_map']
      · intro f hf y hy hm
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
        exact hix p hp y hy hm
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @read Γ a Ref c fs vs f A ha hr hc hm ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .readAt f a, A⟩) (r := .read) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,by simp only [show expand G Ref = [c] from hr, hc]; exact hm⟩
    simpa using ih
  | @readView Γ a Ref c fs vs f A ha hr hc hm ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .readAt f a, A⟩) (r := .readView) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,by simp only [show expand G Ref = [c] from hr, hc]; exact hm⟩
    simpa using ih
  | @readProto Γ a Ref P fs vs os ms ks K gs ws os' ms' ks' f A ha hr hK hf hpr hP hm ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .readAt f a, A⟩) (r := .readProto P) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,by
        simp only [ProtoMember, show expand G Ref = [.refs fs [] vs os ms ks] from hr,
          show expand G P = [.refs gs [] ws os' ms' ks'] from hP]
        exact ⟨⟨K, hK, hf⟩, hpr, hm⟩⟩
    simpa using ih
  | @readOptional Γ a Ref fs vs os ms ks f r A U ha hr hm hUnd ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .readAt f a, A ++ U⟩)
      (r := .readOptional A U) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,hUnd,rfl,by
        simp only [show expand G Ref = [.refs fs [] vs os ms ks] from hr]; exact ⟨_, hm, rfl, rfl⟩⟩

    simpa using ih
  | @readDict Γ a Ref fs vs ix os ms ks cs A U f K ha hr hm hsure hUnd ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .readAt f a, A ++ U⟩)
      (r := .readDict K A U) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,hUnd,rfl,hsure,
        by simp only [show expand G Ref = [.dict fs [] vs ix os ms ks cs] from hr]; exact hm⟩
    simpa using ih
  | @indexDict Γ a Ref fs vs ix os ms ks cs key Kt A U K KK ha hr hk hStr hwithin hm hUnd iha ihk =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .indexAt a key, A ++ U⟩)
      (r := .indexDict K KK A U) (js := [⟨Γ,a,Ref⟩, ⟨Γ,key,Kt⟩])
      ⟨rfl,rfl,rfl,rfl,hStr,hwithin,hUnd,rfl,
        by simp only [show expand G Ref = [.dict fs [] vs ix os ms ks cs] from hr]; exact hm⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact iha
    · exact ihk
  | @arrLit Γ L T xs hr hreq hbound hpos hx ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .arrLit (xs.map Prod.snd), L⟩) (r := .arrLit)
      (js := xs.map fun p => ⟨Γ, p.2, p.1⟩)
    · unfold LocalUsing; simp only [show expand G L = [.list T []] from hr]
      refine ⟨by simp [List.map_map, Function.comp_def],
        by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; rfl,
        by simpa using hreq, by simpa using hbound, ?_⟩
      intro q hq
      rw [List.zipIdx_map] at hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact hpos p hp
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @elem Γ a i L I A T b k ha hr hi hI hk hA iha ihi =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .elemAt a i, A⟩) (r := .elem) (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩])
      ⟨rfl,rfl,rfl,rfl,by simp only [show expand G L = [.list T []] from hr,
        show expand G I = [.numLit b] from hI]; simp [requiredAt, hk, hA]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihi
  | @elemOpt Γ a i L I A U T b k ha hr hi hI hk hnone hA hU iha ihi =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .elemAt a i, A ++ U⟩) (r := .elemOpt U)
      (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩])
      ⟨rfl,rfl,rfl,rfl,hU,by simp only [show expand G L = [.list T []] from hr,
        show expand G I = [.numLit b] from hI]; simp [optionalAt, hk, hnone, hA]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihi
  | @elemAny Γ a i L I E U ro presence ha hr hi hq hU iha ihi =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .elemAt a i, E ++ U⟩) (r := .elemAny U)
      (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩])
      ⟨rfl,rfl,rfl,rfl,hU,hq,by simp only [show expand G L = [.list ⟨[], [], some E, ro, presence⟩ []] from hr]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihi
  | @setElem Γ a i v L I A T b k ha hr hi hI hk hA hkle hro hv iha ihi ihv =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .setElem a i v, L⟩) (r := .setElem)
      (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩, ⟨Γ,v,A⟩])
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,by simp only [show expand G L = [.list T []] from hr,
        show expand G I = [.numLit b] from hI]; simp [namedAt, hk, hA, hro, hkle]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact iha
    · exact ihi
    · exact ihv
  | @len Γ a L N T ha hr hn ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .lenOf a, N⟩) (r := .len) (js := [⟨Γ,a,L⟩])
      ⟨rfl,rfl,hn,by simp only [show expand G L = [.list T []] from hr]⟩
    simpa using ih
  | @lenStr Γ a S N ha hs hn ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .lenOf a, N⟩) (r := .lenStr) (js := [⟨Γ,a,S⟩])
      ⟨rfl,rfl,hn,hs⟩
    simpa using ih
  | @elemStr Γ a i S I T U ha hs hi hq hT hU iha ihi =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .elemAt a i, T ++ U⟩) (r := .elemStr T U)
      (js := [⟨Γ,a,S⟩, ⟨Γ,i,I⟩]) ⟨rfl,rfl,rfl,rfl,hs,hq,hT,hU,rfl⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihi
  | @test Γ a A B k ha ht hf ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .test k a, B⟩) (r := .test) (js := [⟨Γ,a,A⟩])
      ⟨rfl,rfl,ht,hf⟩
    simpa using ih
  | @arith Γ a A b B op N ha hb hops iha ihb =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .arith op a b, N⟩) (r := .arith)
      (js := [⟨Γ,a,A⟩, ⟨Γ,b,B⟩]) ⟨rfl,rfl,rfl,rfl,hops⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb
  | @write Γ a Ref fs vs os ms ks f A b N ha hr hm hb hn iha ihb =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .writeAt f a b, N⟩) (r := .write)
      (js := [⟨Γ,a,Ref⟩, ⟨Γ,b,A⟩])
      ⟨rfl,rfl,rfl,rfl,hn,by simp only [show expand G Ref = [.refs fs [] vs os ms ks] from hr]; exact hm⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb
  | @ifBool Γ c C t A e hc hb ht he ihc iht ihe =>
    apply node_complete (r := .ifBool) (js := [⟨Γ,c,C⟩,⟨Γ,t,A⟩,⟨Γ,e,A⟩])
    · exact ⟨rfl,rfl,hb,rfl,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact ihc
      · exact iht
      · exact ihe
  | @ifKnown Γ c C q t e A hc hq ht ihc iht =>
    apply node_complete (r := .ifKnown q) (js := [⟨Γ,c,C⟩,⟨Γ,(if q then t else e),A⟩])
    · exact ⟨rfl,rfl,hq,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact ihc
      · exact iht
  | @ifBoolVar Γ i C T F t A e hi hb hT hF ht he iht ihe =>
    apply node_complete (r := .ifBoolVar T F) (js := [⟨Γ.set i T,t,A⟩,⟨Γ.set i F,e,A⟩])
    · exact ⟨by simpa only [hi] using hb,hT,hF,rfl,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact iht
      · exact ihe
  | @ifTag Γ i A tag q u B e hi hq ht he iht ihe =>
    cases q with
    | true =>
      apply node_complete (r := .ifTrue) (js := [⟨Γ,u,B⟩])
      · unfold LocalUsing; simpa only [hi, true_and] using hq
      · simpa using iht rfl
    | false =>
      apply node_complete (r := .ifFalse) (js := [⟨Γ,e,B⟩])
      · unfold LocalUsing; simpa only [hi, true_and] using hq
      · simpa using ihe rfl
  | @unionVar Γ i C t A hi ht ih =>
    apply node_complete (r := .unionVar i)
      (js := C.map (fun a => ⟨Γ.set i [a], t, A⟩))
    · unfold LocalUsing; simp [hi]
    · intro j hj
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hj
      exact ih a ha
  | @arrCopy Γ s S T E presence hs hsp hr ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .arrLit [.spread s], T⟩) (r := .arrCopy E)
      (js := [⟨Γ, s, S⟩]) ⟨rfl, rfl, hsp, by
        simp only [show expand G T = [.list ⟨[], [], some E, false, presence⟩ []] from hr]⟩
    simpa using ih
  | @callRest effect Γ f r F Rt xs Us P B parts hf hmem hrt hx hu hshort hp hparts
      ihf ihrt ihx ihu ihp =>
    apply node_complete (r := .callRest effect xs.length Us.length (parts.map Prod.fst) P)
      (js := ⟨Γ,f,F⟩ :: ⟨Γ,r,Rt⟩ :: (xs.map (fun p => ⟨Γ,p.2,p.1⟩) ++ Us.map (fun A => ⟨Γ,.undef,A⟩) ++
        parts.map (fun p => ⟨Γ,p.2.2,p.2.1⟩)))
    · have hlenx : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))).length = xs.length := by simp
      have hlenu : (Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).length = Us.length := by simp
      have hlenxu : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).length = xs.length + Us.length := by simp
      have hzip : (parts.map Prod.fst).zip (parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι)))
          = parts.map (fun p => (p.1, (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))) := List.zip_map'
      have htk : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).take xs.length =
          xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) := by
        rw [List.append_assoc, List.take_left' hlenx]
      have hdk : ((xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).drop xs.length).take Us.length =
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) := by
        rw [List.append_assoc, List.drop_left' hlenx, List.take_left' hlenu]
      have hdku : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).drop (xs.length + Us.length) =
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι)) := List.drop_left' hlenxu
      have htku : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).take (xs.length + Us.length) =
          xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
            Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) := List.take_left' hlenxu
      refine ⟨rfl, rfl, rfl, rfl, ?_, by simp; omega, by rcases hshort with h | h <;> simp [h],
        ?_, ?_, ?_, ?_⟩
      · intro ja hj
        simp only [List.mem_append, List.mem_map] at hj
        rcases hj with (⟨p,_,rfl⟩ | ⟨A,_,rfl⟩) | ⟨p,_,rfl⟩ <;> rfl
      · rw [htk, hdku, hzip]
        simp [List.map_map, Function.comp_def]
      · rw [hdk]
        intro ja hj
        obtain ⟨A,_,rfl⟩ := List.mem_map.mp hj; rfl
      · rw [hdku, hzip]
        simpa [List.map_map, Function.comp_def] using hparts
      · rw [htku]
        simpa [List.map_map, List.map_append, Function.comp_def] using hmem
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihrt
      · simp only [List.mem_append, List.mem_map] at hj
        rcases hj with (⟨p,hp',rfl⟩ | ⟨A,hA,rfl⟩) | ⟨p,hp',rfl⟩
        · exact ihx p hp'
        · exact ihu A hA
        · exact ihp p hp'
  | @bindE effect Γ F T Rt R Rc t r saved Ps Ds ht hsig hr hmap hF =>
    apply node_complete (r := .bindE) (js := [])
    · refine ⟨rfl, rfl, ?_⟩
      show (match varSlots (saved.map Tm.var), Γ[t]?, Γ[r]?, expand G F with
        | some saved, some T, some Rt, [.arrs [⟨_, Ds, R, effect⟩] []] =>
          saved.map (Γ[·]?) = (saved.filterMap (Γ[·]?)).map some ∧
          ⟨Rt, saved.filterMap (Γ[·]?) ++ Ds, R, effect⟩ ∈ callSigs G T
        | _, _, _, _ => False)
      rw [varSlots_map, ht, hr, show expand G F = [.arrs [⟨Rc, Ds, R, effect⟩] []] from hF]
      simp only
      rw [filterMap_of_map hmap]
      exact ⟨hmap, hsig⟩
    · simp
  | @bindMember Γ F O i k m L S hi hmo hF hL hS hR =>
    obtain ⟨proofs, hlen, hps⟩ := choose_list
      (P := fun q ps => ∃ c ∈ m.calls, CallProofsUsing G images q c ps) L (fun q hq => by
        obtain ⟨c, hc, hcov⟩ := hL q hq
        obtain ⟨ps, hps⟩ := CoveredCallUsing.proofs hcov
        exact ⟨ps, c, hc, hps⟩)
    obtain ⟨rests, hrlen, hrs⟩ := choose_list
      (P := fun s ps => ∃ c ∈ m.rests, RestProofsUsing G images s c ps) S (fun s hs => by
        obtain ⟨c, hc, hcov⟩ := hS s hs
        obtain ⟨ps, hps⟩ := CoveredRestUsing.proofs hcov
        exact ⟨ps, c, hc, hps⟩)
    obtain ⟨receivers, hvlen, hvs⟩ := choose_list
      (P := fun T p => PositiveCertificates.checkUsing G images O T p = true) m.receivers hR
    apply node_complete (r := .bindMember proofs rests receivers) (js := [])
    · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show (match Γ[i]?, expand G F with
        | some O, [.arrs L S] => ∃ m ∈ (memberOf G O k).toList,
            proofs.length = L.length ∧ (∀ qp ∈ L.zip proofs, ∃ c ∈ m.calls, CallProofsUsing G images qp.1 c qp.2) ∧
            rests.length = S.length ∧ (∀ sp ∈ S.zip rests, ∃ c ∈ m.rests, RestProofsUsing G images sp.1 c sp.2) ∧
            receivers.length = m.receivers.length ∧
            (∀ tp ∈ m.receivers.zip receivers, PositiveCertificates.checkUsing G images O tp.1 tp.2 = true)
        | some O, _ => proofs = [] ∧ rests = [] ∧ receivers = [] ∧ expand G F = [] ∧
            ∃ m ∈ (memberOf G O k).toList, F ∈ m.schemes
        | none, _ => False)
      rw [hi, show expand G F = [.arrs L S] from hF]
      exact ⟨m, by simp [hmo], hlen, hps, hrlen, hrs, hvlen, hvs⟩
    · simp
  | @bindScheme Γ F O i k m hi hmo hF hE =>
    apply node_complete (r := .bindMember [] [] []) (js := [])
    · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show (match Γ[i]?, expand G F with
        | some O, [.arrs L S] => ∃ m ∈ (memberOf G O k).toList,
            ([] : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι)).length =
              L.length ∧
            (∀ qp ∈ L.zip ([] : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι)),
              ∃ c ∈ m.calls, CallProofsUsing G images qp.1 c qp.2) ∧
            ([] : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
              PositiveCertificates.SubtypeChoices ι)).length = S.length ∧
            (∀ sp ∈ S.zip ([] : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
              PositiveCertificates.SubtypeChoices ι)), ∃ c ∈ m.rests, RestProofsUsing G images sp.1 c sp.2) ∧
            ([] : List (PositiveCertificates.SubtypeChoices ι)).length = m.receivers.length ∧
            (∀ tp ∈ m.receivers.zip ([] : List (PositiveCertificates.SubtypeChoices ι)),
              PositiveCertificates.checkUsing G images O tp.1 tp.2 = true)
        | some O, _ => ([] : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι)) = [] ∧
            ([] : List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι ×
              PositiveCertificates.SubtypeChoices ι)) = [] ∧
            ([] : List (PositiveCertificates.SubtypeChoices ι)) = [] ∧
            expand G F = [] ∧ ∃ m ∈ (memberOf G O k).toList, F ∈ m.schemes
        | none, _ => False)
      rw [hi, hE]
      exact ⟨rfl, rfl, rfl, rfl, m, by simp [hmo], hF⟩
    · simp
  | @bindRestE effect Γ F T Rt E El R Rc t r saved Ps Qs ht hsig hel hr hmap hQs hF =>
    apply node_complete (r := .bindRestE) (js := [])
    · refine ⟨rfl, rfl, ?_⟩
      show (match varSlots (saved.map Tm.var), Γ[t]?, Γ[r]?, expand G F with
        | some saved, some T, some Rt, [.arrs [] [⟨_, (Ds, E'), R, effect⟩]] =>
          saved.map (Γ[·]?) = (saved.filterMap (Γ[·]?)).map some ∧
          ∃ s ∈ restSigs G T, s.receiver = Rt ∧ s.arguments.2 = E' ∧ s.result = R ∧ s.effect = effect ∧
            Ds = s.arguments.1.drop saved.length ∧ ∃ El ∈ (restElem G E').toList,
            saved.filterMap (Γ[·]?) =
              s.arguments.1.take saved.length ++ List.replicate (saved.length - s.arguments.1.length) El
        | _, _, _, _ => False)
      rw [varSlots_map, ht, hr, show expand G F = [.arrs [] [⟨Rc, (Ps.drop saved.length, E), R, effect⟩]] from hF]
      simp only
      rw [filterMap_of_map hmap]
      exact ⟨hmap, ⟨Rt, (Ps, E), R, effect⟩, hsig, rfl, rfl, rfl, rfl, rfl, El, by simp [hel], hQs⟩
    · simp
  | @sub Γ t A B cert ht hc ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, t, B⟩) (r := .sub cert) (js := [⟨Γ,t,A⟩]) ⟨rfl,rfl,hc⟩
    simpa using ih
  | @throw A Γ a B hA ha ih =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .throw a, B⟩) (r := .throw) (js := [⟨Γ,a,A⟩]) ⟨rfl,rfl,hA⟩
    simpa using ih
  | @merge Γ d a b A B R ha hb hm iha ihb =>
    apply node_complete (G := G) (images := images) (j := ⟨Γ, .merge d a b, R⟩) (r := .merge)
      (js := [⟨Γ,a,A⟩, ⟨Γ,b,B⟩]) ⟨rfl,rfl,rfl,rfl,hm⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb

/-- A closed derivation has evidence, with every graph code admitted, and
evidence under a sound code table is a derivation: the checker decides the
rules, the table answering which graph code a unit checked. -/
theorem derivableUsing_iff_checked [DecidableEq ι] (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G) (t : Tm) (A : Ty ι) :
    ((Scoped 0 t ∧ HasTyUsing G images [] t A) → ∃ e, checkUsing G images t A e (fun _ => true) = true) ∧
    ∀ codes, CodesSound G codes → (∃ e, checkUsing G images t A e codes = true) → Scoped 0 t ∧ HasTyUsing G images [] t A := by
  constructor
  · rintro ⟨hs, ht⟩
    obtain ⟨e, he, hc⟩ := checkTreeUsing_complete ht
    exact ⟨e, by simp [checkUsing, he, (checkScope_iff 0 t).mpr hs, hc]⟩
  · rintro codes hcodes ⟨e, he⟩; exact checkUsing_sound he hcodes

/-- Finite specializations retain the existing source-facing entry points.
There is one implementation of each rule and one evidence grammar. -/
abbrev CallProofs [DecidableEq ι] (G : NormalGraph ι) :=
  CallProofsUsing G (PositiveCertificates.finiteInstanceImages G)
abbrev Local [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool := fun _ => false) : Prop :=
  LocalUsing G (PositiveCertificates.finiteInstanceImages G) j r ps codes

@[nospecialize] def checkTree [DecidableEq ι] (G : NormalGraph ι) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  checkTreeUsing G (PositiveCertificates.finiteInstanceImages G) e codes

@[nospecialize] def check [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  checkUsing G (PositiveCertificates.finiteInstanceImages G) t A e codes

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {t A e} {codes : CodeEntry ι → Bool}
    (he : check G t A e codes = true)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    Scoped 0 t ∧ HasTy G [] t A := checkUsing_sound he hcodes

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {t A e} {codes : CodeEntry ι → Bool}
    (he : check G t A e codes = true) (n W h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    Safe (meaning G A) n W h t := acceptedUsing_safe he n W h hw hh hcodes

theorem derivable_iff_checked [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) :
    ((Scoped 0 t ∧ HasTy G [] t A) → ∃ e, check G t A e (fun _ => true) = true) ∧
    ∀ codes, CodesSound G codes → (∃ e, check G t A e codes = true) → Scoped 0 t ∧ HasTy G [] t A :=
  derivableUsing_iff_checked G (PositiveCertificates.finiteInstanceImages G) t A

#print axioms derivable_iff_checked
#print axioms accepted_safe

#print axioms checkTreeUsing_sound
#print axioms derivableUsing_iff_checked
#print axioms acceptedUsing_safe
end Verification.ProgramCertificates
