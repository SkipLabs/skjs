import Verification.Model.Source.SourceTypes

/-! Structured judgments checked before a ground graph request exists: a call
of a generic module value names its instance, and each type argument must lie
within its binder's bound, a subtyping judgment between two ground types.

There is deliberately no prose field in this representation. A check either
returns this closed judgment form or refuses the source for a separate reason.
Readers derive every displayed sentence from these fields. -/
namespace Verification.Model.DirectObligation
open Lean

/-- `actual ≤ expected` between two ground types, at the source span
`subject`. -/
inductive Judgment where
  | subtyping (subject : Span) (actual expected : List Nat)
  deriving BEq, Repr

inductive SourceRole where
  | entryClaim | expressionClaim | returnContract | bindingAnnotation
  | genericValidation | schemeIntroduction | schemeElimination
  /-- A write into captured storage: the value must meet the fixed contract. -/
  | storageWrite
  /-- An argument to a callable, such as a callback. -/
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

def Judgment.toJson : Judgment → Json
  | .subtyping subject actual expected => Json.mkObj
      [("kind", Lean.toJson "subtyping"), ("subject", Lean.toJson subject),
       ("actual", Lean.toJson actual), ("expected", Lean.toJson expected)]

def Judgment.render (T : SourceTypes.Table) : Judgment → String
  | .subtyping _ actual expected =>
      s!"{SourceTypes.render T actual} ≤ {SourceTypes.render T expected}"

end Verification.Model.DirectObligation
