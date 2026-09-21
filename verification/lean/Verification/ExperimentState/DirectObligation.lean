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
  deriving BEq, Repr

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
  | genericValidation | schemeIntroduction
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

def Ty.render (T : SourceTypes.Table) : Ty → String
  | .rigid name => name
  | .ground labels => SourceTypes.render T labels

def Ty.le : Ty → Ty → Bool
  | .rigid a, .rigid b => a == b
  | .ground A, .ground B => A.all B.contains
  | _, _ => false

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

def Ty.toJson : Ty → Json
  | .rigid name => Json.mkObj [("kind", Lean.toJson "rigid"), ("name", Lean.toJson name)]
  | .ground labels => Json.mkObj [("kind", Lean.toJson "ground"), ("labels", Lean.toJson labels)]

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

end Verification.ExperimentState.DirectObligation
