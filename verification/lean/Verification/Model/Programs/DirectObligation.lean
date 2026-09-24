import Verification.Model.Source.SourceTypes

/-! Structured judgments checked before a ground graph request exists.

There is deliberately no prose field in this representation. A direct checker
either returns one of these closed judgment forms or refuses the source for a
separate reason. Readers derive every displayed sentence from these fields. -/
namespace Verification.Model.DirectObligation
open Lean

inductive Ty where
  | rigid (name : String)
  | ground (labels : List Nat)
  /-- A callable whose signature mentions a rigid parameter, such as the result
  `() => T` of a closure that retains its outer binder: the receiver a call
  may pass, the parameters, the result. -/
  | arrow (receiver : Ty) (params : List Ty) (result : Ty)
  /-- Mutable array storage keeps one invariant element contract. -/
  | array (element : Ty)
  | variadic (receiver : Ty) (params : List Ty) (element result : Ty)
  /-- Every value: the receiver of a signature indifferent to its receiver. -/
  | top
  deriving BEq, Repr, Inhabited

mutual
def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .rigid x, .rigid y =>
    if h : x = y then isTrue (by rw [h]) else isFalse (fun e => h (Ty.rigid.inj e))
  | .ground A, .ground B =>
    if h : A = B then isTrue (by rw [h]) else isFalse (fun e => h (Ty.ground.inj e))
  | .arrow a ps r, .arrow b qs t =>
    match Ty.decEq a b, Ty.decEqList ps qs, Ty.decEq r t with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (by rw [h0, h1, h2])
    | isFalse h0, _, _ => isFalse (fun e => h0 (Ty.arrow.inj e).1)
    | _, isFalse h1, _ => isFalse (fun e => h1 (Ty.arrow.inj e).2.1)
    | _, _, isFalse h2 => isFalse (fun e => h2 (Ty.arrow.inj e).2.2)
  | .variadic a ps e r, .variadic b qs f t =>
    match Ty.decEq a b, Ty.decEqList ps qs, Ty.decEq e f, Ty.decEq r t with
    | isTrue h0, isTrue hp, isTrue he, isTrue hr => isTrue (by rw [h0, hp, he, hr])
    | isFalse h0, _, _, _ => isFalse (fun h => h0 (Ty.variadic.inj h).1)
    | _, isFalse hp, _, _ => isFalse (fun h => hp (Ty.variadic.inj h).2.1)
    | _, _, isFalse he, _ => isFalse (fun h => he (Ty.variadic.inj h).2.2.1)
    | _, _, _, isFalse hr => isFalse (fun h => hr (Ty.variadic.inj h).2.2.2)
  | .variadic .., .rigid _ | .variadic .., .ground _ | .variadic .., .arrow .. | .variadic .., .array _ => isFalse nofun
  | .rigid _, .variadic .. | .ground _, .variadic .. | .arrow .., .variadic .. | .array _, .variadic .. => isFalse nofun
  | .array a, .array b =>
    match Ty.decEq a b with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => h (Ty.array.inj e))
  | .array _, .rigid _ | .array _, .ground _ | .array _, .arrow _ _ _ => isFalse nofun
  | .rigid _, .array _ | .ground _, .array _ | .arrow _ _ _, .array _ => isFalse nofun
  | .top, .top => isTrue rfl
  | .top, .rigid _ | .top, .ground _ | .top, .arrow .. | .top, .array _ | .top, .variadic .. =>
    isFalse nofun
  | .rigid _, .top | .ground _, .top | .arrow .., .top | .array _, .top | .variadic .., .top =>
    isFalse nofun
  | .rigid _, .ground _ => isFalse nofun
  | .rigid _, .arrow _ _ _ => isFalse nofun
  | .ground _, .rigid _ => isFalse nofun
  | .ground _, .arrow _ _ _ => isFalse nofun
  | .arrow _ _ _, .rigid _ => isFalse nofun
  | .arrow _ _ _, .ground _ => isFalse nofun
def Ty.decEqList : (as bs : List Ty) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Ty.decEq a b, Ty.decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (fun e => h1 (List.cons.inj e).1)
    | _, isFalse h2 => isFalse (fun e => h2 (List.cons.inj e).2)
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
end

instance : DecidableEq Ty := Ty.decEq

inductive ParameterScope where
  | ambient | quantified
  deriving BEq, Repr

structure Parameter where
  name : String
  scope : ParameterScope
  upper : Option Ty := none
  deriving BEq, Repr

structure Binding where
  name : String
  type : Ty
  deriving BEq, Repr

inductive Subject where
  | binding (name : String) (pos : Span)
  | expression (pos : Span)
  | returned (pos : Span)
  | closureBody (pos : Span)
  deriving BEq, Repr

inductive Judgment where
  | subtyping (parameters : List Parameter) (context : List Binding)
      (subject : Subject) (actual expected : Ty)
  | schemeIntroduction (parameters : List Parameter) (context : List Binding)
      (body : Subject) (actual expected : Ty)
  deriving BEq, Repr

inductive SourceRole where
  | entryClaim | expressionClaim | returnContract | bindingAnnotation
  | genericValidation | schemeIntroduction | schemeElimination
  /-- A write into captured storage: the value must meet the fixed contract. -/
  | storageWrite
  /-- An argument to a callable known over rigid types, such as a callback. -/
  | callArgument
  /-- A module initialization step that could read a constant before it holds a value. -/
  | initializationOrder
  deriving BEq, Repr

structure Located where
  pos : Span
  role : SourceRole
  judgment : Judgment
  deriving BEq, Repr

inductive Failure where
  | refusal (pos : Span) (role : SourceRole) (reason : String)
  | obligation (located : Located)
  deriving BEq, Repr

def SourceRole.wire : SourceRole → String
  | .entryClaim => "entry-claim"
  | .expressionClaim => "expression-claim"
  | .returnContract => "return-contract"
  | .bindingAnnotation => "binding-annotation"
  | .genericValidation => "generic-validation"
  | .schemeIntroduction => "scheme-introduction"
  | .schemeElimination => "scheme-elimination"
  | .storageWrite => "storage-write"
  | .callArgument => "call-argument"
  | .initializationOrder => "initialization-order"

partial def Ty.render (T : SourceTypes.Table) : Ty → String
  | .variadic rc ps e r =>
      s!"({String.intercalate ", " (receiverText T rc ++ ps.map (Ty.render T) ++ [s!"...Array<{e.render T}>"])}) => {r.render T}"
  | .rigid name => name
  | .top => "unknown"
  | .array element => s!"Array<{element.render T}>"
  | .ground labels => SourceTypes.render T labels
  | .arrow rc params result =>
      s!"({String.intercalate ", " (receiverText T rc ++ params.map (Ty.render T))}) => {result.render T}"
where
  /-- A signature indifferent to its receiver shows none; `this: R` otherwise. -/
  receiverText (T : SourceTypes.Table) (rc : Ty) : List String :=
    match rc with
    | .ground [l] => if T[l]? == some [.top] then [] else [s!"this: {rc.render T}"]
    | _ => [s!"this: {rc.render T}"]

open PositiveRules PositiveGraphs

mutual
  /-- Direct types denote ordinary semantic families once rigid names have an
  assignment. Callables use the calculus's ordered-argument semantics. -/
  def Ty.denote (G : NormalGraph Nat) (η : String → Fam) : Ty → Fam
    | .variadic rc ps e r =>
        restsT [(rc.denote G η, Ty.denoteList G η ps, e.denote G η, r.denote G η)]
    | .array element => recT [(CallArguments.arrayStoreField,
        listT ⟨[], [], some (Ty.denote G η element), false⟩)]
    | .rigid name => η name
    | .top => PositiveNormalization.topT
    | .ground labels => meaning G labels
    | .arrow rc params result =>
        callsT [(rc.denote G η, Ty.denoteList G η params, Ty.denote G η result)]
  def Ty.denoteList (G : NormalGraph Nat) (η : String → Fam) : List Ty → List Fam
    | [] => []
    | t :: ts => Ty.denote G η t :: Ty.denoteList G η ts
end

theorem Ty.denoteList_eq_map (G : NormalGraph Nat) (eta : String → Fam) (As : List Ty) :
    Ty.denoteList G eta As = As.map (Ty.denote G eta) := by
  induction As with
  | nil => rfl
  | cons A As ih => simp only [Ty.denoteList, List.map_cons, ih]

/-- Every declared upper bound is true of the rigid family assigned to its
parameter. Unbounded parameters impose no accidental top bound. -/
def Satisfies (G : NormalGraph Nat) (η : String → Fam)
    (parameters : List Parameter) : Prop :=
  ∀ p ∈ parameters, ∀ upper, p.upper = some upper → FamLe (η p.name) (upper.denote G η)

/-- Follow only declared rigid-to-rigid upper bounds. Names stay separate from
ground graph labels, so a binder cannot be confused with a graph row. -/
def follows (parameters : List Parameter) : Nat → String → String → Bool
  | fuel, x, y =>
    if x == y then true else match fuel with
      | 0 => false
      | n + 1 => parameters.any fun p =>
          p.name == x && match p.upper with
            | some (.rigid upper) => follows parameters n upper y
            | _ => false

theorem follows_sound {G : NormalGraph Nat} {η parameters fuel x y}
    (hs : Satisfies G η parameters) (h : follows parameters fuel x y = true) :
    FamLe (η x) (η y) := by
  induction fuel generalizing x with
  | zero =>
    simp only [follows] at h
    split at h
    · next heq =>
      have : x = y := beq_iff_eq.mp heq
      subst y
      exact fun _ _ _ hx => hx
    · contradiction
  | succ n ih =>
    simp only [follows] at h
    split at h
    · next heq =>
      have : x = y := beq_iff_eq.mp heq
      subst y
      exact fun _ _ _ hx => hx
    · obtain ⟨p, hp, hstep⟩ := List.any_eq_true.mp h
      have hname : p.name = x := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hstep).1
      have htail := (Bool.and_eq_true_iff.mp hstep).2
      split at htail <;> try contradiction
      next upper hu =>
        have hbound : FamLe (η x) (η upper) := by
          rw [← hname]
          change FamLe (η p.name) (Ty.denote G η (.rigid upper))
          exact hs p hp (.rigid upper) hu
        have hrest := ih htail
        exact fun k W v hv => hrest k W v (hbound k W v hv)

/-- A variadic promise includes each finite fixed-arity view. Optional omissions
in that view also remain admissible: omitted positions must admit undefined. -/
private theorem short_replicate {E : Fam} {n j W args}
    (h : ArgsShort (List.replicate n E) j W args) : ∀ a ∈ args, E j W a := by
  induction n generalizing args with
  | zero =>
    have hl := h.1
    simp only [List.length_replicate] at hl
    have : args = [] := by simpa using hl
    subst args
    simp
  | succ n ih =>
    cases args with
    | nil => simp
    | cons a args =>
      rw [List.replicate_succ, ArgsShort_cons] at h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact h.1
      · exact ih h.2 v hv

private theorem short_rest {Ps : List Fam} {E : Fam} {n j W args}
    (h : ArgsShort (Ps ++ List.replicate n E) j W args) : ArgsRest Ps E j W args := by
  induction Ps generalizing args with
  | nil => exact ArgsRest_nil_params.mpr (short_replicate h)
  | cons P Ps ih =>
    cases args with
    | nil =>
      apply ArgsRest_nil_args.mpr
      have hu := ArgsShort_nil_args.mp h
      exact fun A hm => hu A (List.mem_append_left _ hm)
    | cons a args =>
      rw [List.cons_append, ArgsShort_cons] at h
      exact ArgsRest_cons.mpr ⟨h.1, ih h.2⟩

theorem variadic_fixed (Rc : Fam) (Ps : List Fam) (E R : Fam) (extra : Nat) :
    FamLe (restsT [(Rc, Ps, E, R)]) (callsT [(Rc, Ps ++ List.replicate extra E, R)]) := by
  intro n W v hv
  refine ⟨hv.1, ?_⟩
  intro p hp
  have hp := List.mem_singleton.mp hp
  subst p
  apply (hv.2 (Rc, Ps, E, R) (by simp)).weaken
  · intro j hj U r hr
    exact hr
  · intro j hj U args ha
    exact short_rest ha
  · intro j hj U a ha
    exact ha

/-- Fuel makes the checker total even for a malformed cyclic bound document.
Successful checks are sound at every fuel; exhaustion only loses completeness. -/
def Ty.leUnderFuel (fuel : Nat) (parameters : List Parameter) : Ty → Ty → Bool
  | a, b => match fuel with
    | 0 => false
    | n + 1 => match a, b with
      | .rigid x, .rigid y => follows parameters parameters.length x y
      -- Every value is below top; a rigid name only through its bound.
      | .ground _, .top | .arrow .., .top | .array _, .top | .variadic .., .top | .top, .top => true
      | .rigid x, _ => parameters.any fun q => match q.upper with
          | some (.rigid _) | none => false
          | some terminal => follows parameters parameters.length x q.name &&
              Ty.leUnderFuel n parameters terminal b
      | .ground A, .ground B => A.all B.contains
      | .array a, .array b => decide (a = b)
      | a@(.variadic ..), b@(.variadic ..) => decide (a = b)
      | .variadic rc ps e r, .arrow rd qs t =>
          decide (rc = rd ∧ qs = ps ++ List.replicate (qs.length - ps.length) e ∧ r = t)
      | .arrow rc ps r, .arrow rd qs t =>
          Ty.leUnderFuel n parameters rd rc && ps.length == qs.length &&
            (qs.zip ps).all (fun (q, p) => Ty.leUnderFuel n parameters q p) &&
            Ty.leUnderFuel n parameters r t
      | _, _ => false

def Ty.depth : Ty → Nat
  | .rigid _ | .ground _ | .top => 1
  | .array a => 1 + a.depth
  | .variadic rc ps e r => 1 + (ps.map Ty.depth).foldl max (max rc.depth (max e.depth r.depth))
  | .arrow rc ps r => 1 + (ps.map Ty.depth).foldl max (max rc.depth r.depth)

/-- The structure a walk may have to enter through declared bounds. -/
def upperDepths (parameters : List Parameter) : Nat :=
  (parameters.map fun p => (p.upper.map Ty.depth).getD 0).foldl (· + ·) 0

/-- Inclusion under declared upper bounds. Ground unions use inclusion;
callables are contravariant in parameters and covariant in their result.
The fuel pays for every structural step of both sides and, once per
parameter, for entering that parameter's bound: `RigidJudgments` shows the
former alone rejects a declaratively valid inclusion through a callable bound. -/
def Ty.leUnder (parameters : List Parameter) (a b : Ty) : Bool :=
  Ty.leUnderFuel (parameters.length + upperDepths parameters + a.depth + b.depth + 1)
    parameters a b

private theorem denoteList_argsLe {G : NormalGraph Nat} {η parameters fuel qs ps}
    (hlen : ps.length = qs.length)
    (hall : (qs.zip ps).all (fun (q, p) => Ty.leUnderFuel fuel parameters q p) = true)
    (ih : ∀ {a b}, Ty.leUnderFuel fuel parameters a b = true →
      FamLe (a.denote G η) (b.denote G η)) :
    ArgsLe (Ty.denoteList G η qs) (Ty.denoteList G η ps) := by
  induction qs generalizing ps with
  | nil =>
    cases ps with
    | nil => exact .nil
    | cons p ps => simp at hlen
  | cons q qs ihList =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      simp only [List.length_cons] at hlen
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      exact .cons (ih hall.1) (ihList (Nat.add_right_cancel hlen) hall.2)

/-- The executable direct-subtyping check is semantically sound. This is the
bridge that prevents a producer-specific generic checker from inventing an
inclusion unsupported by the calculus. -/
theorem Ty.leUnderFuel_sound {G : NormalGraph Nat} {η parameters fuel a b}
    (hs : Satisfies G η parameters)
    (h : Ty.leUnderFuel fuel parameters a b = true) :
    FamLe (a.denote G η) (b.denote G η) := by
  induction fuel generalizing a b with
  | zero =>
    simp only [Ty.leUnderFuel] at h
    contradiction
  | succ n ih =>
    cases a with
    | rigid x =>
      cases b with
      | rigid y =>
        exact follows_sound hs h
      | ground B | arrow _ qs t | array e | variadic _ ps e r | top =>
        simp only [Ty.leUnderFuel] at h
        obtain ⟨q, hq, hstep⟩ := List.any_eq_true.mp h
        cases hu : q.upper with
        | none => simp [hu] at hstep
        | some upper => cases upper with
          | rigid name => simp [hu] at hstep
          | ground A | arrow _ ps r | array e | variadic _ ps e r | top =>
            simp only [hu, Bool.and_eq_true] at hstep
            exact fun k W v hv => (ih hstep.2) k W v
              ((hs q hq _ hu) k W v ((follows_sound hs hstep.1) k W v hv))
    | top =>
      cases b with
      | top => exact fun _ _ _ hv => hv
      | rigid _ | ground _ | array _ | variadic _ _ _ _ | arrow _ _ _ =>
        simp [Ty.leUnderFuel] at h
    | ground A =>
      cases b with
      | rigid y | array _ | variadic _ _ _ _ => simp [Ty.leUnderFuel] at h
      | top => exact fun _ _ _ hv => ProgramTyping.meaning_value hv
      | arrow _ qs t => simp [Ty.leUnderFuel] at h
      | ground B =>
        simp only [Ty.leUnderFuel] at h
        intro k W v hv
        obtain ⟨label, hlabel, hv⟩ := hv
        exact ⟨label, by simpa using (List.all_eq_true.mp h) label hlabel, hv⟩
    | arrow rc ps r =>
      cases b with
      | rigid y | array _ | variadic _ _ _ _ => simp [Ty.leUnderFuel] at h
      | top => exact fun _ _ _ hv => ⟨hv.1.val, hv.1.scoped⟩
      | ground B => simp [Ty.leUnderFuel] at h
      | arrow rd qs t =>
        simp only [Ty.leUnderFuel, Bool.and_eq_true] at h
        have hrecv := ih h.1.1.1
        have hdom := denoteList_argsLe (G := G) (η := η) (beq_iff_eq.mp h.1.1.2) h.1.2
          (fun hsub => ih hsub)
        have hresult := ih h.2
        exact callsT_single_mono hrecv hdom hresult
    | array e =>
      cases b with
      | rigid _ | ground _ | arrow _ _ _ | variadic _ _ _ _ => simp [Ty.leUnderFuel] at h
      | top =>
        intro _ _ _ hv
        obtain ⟨fields, rfl, _⟩ := hv
        exact ⟨rfl, trivial⟩
      | array f =>
        have heq : e = f := by simpa [Ty.leUnderFuel] using h
        subst f
        exact fun _ _ _ hv => hv
    | variadic rc ps e r =>
      cases b with
      | rigid _ | ground _ | array _ => simp [Ty.leUnderFuel] at h
      | top => exact fun _ _ _ hv => ⟨hv.1.val, hv.1.scoped⟩
      | arrow rd qs t =>
        have hh : rc = rd ∧ qs = ps ++ List.replicate (qs.length - ps.length) e ∧ r = t := by
          simpa [Ty.leUnderFuel] using h
        obtain ⟨rfl, hq, rfl⟩ := hh
        simp only [Ty.denote]
        have heq : Ty.denoteList G η qs = Ty.denoteList G η ps ++
            List.replicate (qs.length - ps.length) (e.denote G η) := by
          exact (congrArg (Ty.denoteList G η) hq).trans (by simp [Ty.denoteList_eq_map])
        rw [heq]
        exact variadic_fixed _ _ _ _ _
      | variadic rd qs f t =>
        have heq : Ty.variadic rc ps e r = .variadic rd qs f t := by simpa [Ty.leUnderFuel] using h
        rw [heq]
        exact fun _ _ _ hv => hv

theorem Ty.leUnder_sound {G : NormalGraph Nat} {η parameters a b}
    (hs : Satisfies G η parameters) (h : Ty.leUnder parameters a b = true) :
    FamLe (a.denote G η) (b.denote G η) :=
  Ty.leUnderFuel_sound hs h

/-- Inclusion with no parameters in scope: the same relation, with nothing to
chain through. -/
def Ty.le (a b : Ty) : Bool := Ty.leUnder [] a b

def Subject.pos : Subject → Span
  | .binding _ pos | .expression pos | .returned pos | .closureBody pos => pos

def Subject.toJson : Subject → Json
  | .binding name pos => Json.mkObj
      [("kind", Lean.toJson "binding"), ("name", Lean.toJson name), ("pos", Lean.toJson pos)]
  | .expression pos => Json.mkObj
      [("kind", Lean.toJson "expression"), ("pos", Lean.toJson pos)]
  | .returned pos => Json.mkObj
      [("kind", Lean.toJson "return-value"), ("pos", Lean.toJson pos)]
  | .closureBody pos => Json.mkObj
      [("kind", Lean.toJson "closure-body"), ("pos", Lean.toJson pos)]

partial def Ty.toJson : Ty → Json
  | .variadic rc ps e r => Json.mkObj [("kind", Lean.toJson "variadic"),
      ("receiver", rc.toJson), ("params", Lean.toJson (ps.map Ty.toJson)),
      ("element", e.toJson), ("result", r.toJson)]
  | .array element => Json.mkObj [("kind", Lean.toJson "array"), ("element", element.toJson)]
  | .rigid name => Json.mkObj [("kind", Lean.toJson "rigid"), ("name", Lean.toJson name)]
  | .top => Json.mkObj [("kind", Lean.toJson "top")]
  | .ground labels => Json.mkObj [("kind", Lean.toJson "ground"), ("labels", Lean.toJson labels)]
  | .arrow rc params result => Json.mkObj [("kind", Lean.toJson "arrow"),
      ("receiver", rc.toJson),
      ("params", Json.arr (params.map Ty.toJson).toArray), ("result", result.toJson)]

def Parameter.toJson (p : Parameter) : Json := Json.mkObj
  [("name", Lean.toJson p.name),
   ("scope", Lean.toJson (match p.scope with | .ambient => "ambient" | .quantified => "quantified")),
   ("upper", p.upper.map Ty.toJson |>.getD Json.null)]

def Binding.toJson (b : Binding) : Json := Json.mkObj
  [("name", Lean.toJson b.name), ("type", b.type.toJson)]

def Judgment.toJson : Judgment → Json
  | .subtyping parameters context subject actual expected => Json.mkObj
      [("kind", Lean.toJson "subtyping"),
       ("parameters", Json.arr (parameters.map Parameter.toJson).toArray),
       ("context", Json.arr (context.map Binding.toJson).toArray),
       ("subject", subject.toJson), ("actual", actual.toJson),
       ("expected", expected.toJson)]
  | .schemeIntroduction parameters context body actual expected => Json.mkObj
      [("kind", Lean.toJson "scheme-introduction"),
       ("parameters", Json.arr (parameters.map Parameter.toJson).toArray),
       ("context", Json.arr (context.map Binding.toJson).toArray),
       ("body", body.toJson), ("actual", actual.toJson),
       ("expected", expected.toJson)]

private def parametersText (T : SourceTypes.Table) (ps : List Parameter) : String :=
  String.intercalate ", " (ps.map fun p => match p.upper with
    | none => p.name
    | some upper => s!"{p.name} ≤ {upper.render T}")

def Judgment.render (T : SourceTypes.Table) : Judgment → String
  | .subtyping parameters _ _ actual expected =>
      s!"{actual.render T} ≤ {expected.render T} under [{parametersText T parameters}]"
  | .schemeIntroduction parameters _ _ actual expected =>
      s!"{actual.render T} ≤ {expected.render T} for every instantiation of [{parametersText T parameters}]"

def Judgment.context : Judgment → List Binding
  | .subtyping _ context _ _ _ | .schemeIntroduction _ context _ _ _ => context

def Judgment.system : Judgment → String
  | .subtyping .. => "generic"
  | .schemeIntroduction .. => "scheme"

def Judgment.message (T : SourceTypes.Table) : Judgment → String
  | j@(.subtyping ..) => s!"generic obligation: cannot establish {j.render T}"
  | j@(.schemeIntroduction ..) =>
      s!"quantified closure body does not satisfy its scheme universally: cannot establish {j.render T}"

#print axioms follows_sound
#print axioms Ty.leUnderFuel_sound
#print axioms Ty.leUnder_sound

end Verification.Model.DirectObligation
