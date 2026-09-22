import Verification.ExperimentState.SourceTypes

/-! Structured judgments checked before a ground graph request exists.

There is deliberately no prose field in this representation. A direct checker
either returns one of these closed judgment forms or refuses the source for a
separate reason. Readers derive every displayed sentence from these fields. -/
namespace Verification.ExperimentState.DirectObligation
open Lean

inductive Ty where
  | rigid (name : String)
  | ground (labels : List Nat)
  /-- A callable whose signature mentions a rigid parameter, such as the result
  `() => T` of a closure that retains its outer binder. -/
  | arrow (params : List Ty) (result : Ty)
  deriving BEq, Repr, Inhabited

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

partial def Ty.render (T : SourceTypes.Table) : Ty → String
  | .rigid name => name
  | .ground labels => SourceTypes.render T labels
  | .arrow params result =>
      s!"({String.intercalate ", " (params.map (Ty.render T))}) => {result.render T}"

open PositiveRules PositiveGraphs

mutual
  /-- Direct types denote ordinary semantic families once rigid names have an
  assignment. Callables use the calculus's ordered-argument semantics. -/
  def Ty.denote (G : NormalGraph Nat) (η : String → Fam) : Ty → Fam
    | .rigid name => η name
    | .ground labels => meaning G labels
    | .arrow params result =>
        callsT [(Ty.denoteList G η params, Ty.denote G η result)]
  def Ty.denoteList (G : NormalGraph Nat) (η : String → Fam) : List Ty → List Fam
    | [] => []
    | t :: ts => Ty.denote G η t :: Ty.denoteList G η ts
end

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

/-- Fuel makes the checker total even for a malformed cyclic bound document.
Successful checks are sound at every fuel; exhaustion only loses completeness. -/
def Ty.leUnderFuel (fuel : Nat) (parameters : List Parameter) : Ty → Ty → Bool
  | a, b => match fuel with
    | 0 => false
    | n + 1 => match a, b with
      | .rigid x, .rigid y => follows parameters parameters.length x y
      | .rigid x, _ => parameters.any fun q => match q.upper with
          | some (.rigid _) | none => false
          | some terminal => follows parameters parameters.length x q.name &&
              Ty.leUnderFuel n parameters terminal b
      | .ground A, .ground B => A.all B.contains
      | .arrow ps r, .arrow qs t =>
          ps.length == qs.length &&
            (qs.zip ps).all (fun (q, p) => Ty.leUnderFuel n parameters q p) &&
            Ty.leUnderFuel n parameters r t
      | _, _ => false

private def Ty.depth : Ty → Nat
  | .rigid _ | .ground _ => 1
  | .arrow ps r => 1 + (ps.map Ty.depth).foldl max r.depth

/-- Inclusion under declared upper bounds. Ground unions use inclusion;
callables are contravariant in parameters and covariant in their result. -/
def Ty.leUnder (parameters : List Parameter) (a b : Ty) : Bool :=
  Ty.leUnderFuel (parameters.length + a.depth + b.depth + 1) parameters a b

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
      | ground B =>
        simp only [Ty.leUnderFuel] at h
        obtain ⟨q, hq, hstep⟩ := List.any_eq_true.mp h
        cases hu : q.upper with
        | none => simp [hu] at hstep
        | some upper => cases upper with
        | rigid name => simp [hu] at hstep
        | arrow ps r =>
          simp only [hu, Bool.and_eq_true] at hstep
          obtain ⟨hreach, hterminal⟩ := hstep
          have hrigid : FamLe (η x) (Ty.denote G η (.arrow ps r)) :=
            fun k W v hv =>
              (hs q hq (.arrow ps r) hu) k W v
                ((follows_sound hs hreach) k W v hv)
          exact fun k W v hv => (ih hterminal) k W v (hrigid k W v hv)
        | ground A =>
          simp only [hu, Bool.and_eq_true] at hstep
          obtain ⟨hreach, hterminal⟩ := hstep
          have hrigid : FamLe (η x) (Ty.denote G η (.ground A)) :=
            fun k W v hv =>
              (hs q hq (.ground A) hu) k W v
                ((follows_sound hs hreach) k W v hv)
          exact fun k W v hv => (ih hterminal) k W v (hrigid k W v hv)
      | arrow qs t =>
        simp only [Ty.leUnderFuel] at h
        obtain ⟨q, hq, hstep⟩ := List.any_eq_true.mp h
        cases hu : q.upper with
        | none => simp [hu] at hstep
        | some upper => cases upper with
        | rigid name => simp [hu] at hstep
        | ground A =>
          simp only [hu, Bool.and_eq_true] at hstep
          obtain ⟨hreach, hterminal⟩ := hstep
          have hrigid : FamLe (η x) (Ty.denote G η (.ground A)) :=
            fun k W v hv =>
              (hs q hq (.ground A) hu) k W v
                ((follows_sound hs hreach) k W v hv)
          exact fun k W v hv => (ih hterminal) k W v (hrigid k W v hv)
        | arrow ps r =>
          simp only [hu, Bool.and_eq_true] at hstep
          obtain ⟨hreach, hterminal⟩ := hstep
          have hrigid : FamLe (η x) (Ty.denote G η (.arrow ps r)) :=
            fun k W v hv =>
              (hs q hq (.arrow ps r) hu) k W v
                ((follows_sound hs hreach) k W v hv)
          exact fun k W v hv => (ih hterminal) k W v (hrigid k W v hv)
    | ground A =>
      cases b with
      | rigid y => simp [Ty.leUnderFuel] at h
      | arrow qs t => simp [Ty.leUnderFuel] at h
      | ground B =>
        simp only [Ty.leUnderFuel] at h
        intro k W v hv
        obtain ⟨label, hlabel, hv⟩ := hv
        exact ⟨label, by simpa using (List.all_eq_true.mp h) label hlabel, hv⟩
    | arrow ps r =>
      cases b with
      | rigid y => simp [Ty.leUnderFuel] at h
      | ground B => simp [Ty.leUnderFuel] at h
      | arrow qs t =>
        simp only [Ty.leUnderFuel, Bool.and_eq_true] at h
        have hdom := denoteList_argsLe (G := G) (η := η) (beq_iff_eq.mp h.1.1) h.1.2
          (fun hsub => ih hsub)
        have hresult := ih h.2
        exact callsT_single_mono hdom hresult

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
  | .rigid name => Json.mkObj [("kind", Lean.toJson "rigid"), ("name", Lean.toJson name)]
  | .ground labels => Json.mkObj [("kind", Lean.toJson "ground"), ("labels", Lean.toJson labels)]
  | .arrow params result => Json.mkObj [("kind", Lean.toJson "arrow"),
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

end Verification.ExperimentState.DirectObligation
