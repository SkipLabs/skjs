import Verification.ExperimentState.SourceTypes

/-! Producer-independent claims for the current bounded fragment. Candidates
contain calculus type labels, never producer JSON. A decoding failure is retained
until a claim is used: exporters may include unrelated unsupported bindings such
as implicit `this`; those failures must never be interpreted as a type. -/
namespace Verification.ExperimentState.SourceClaims
open ProgramTyping

abbrev Candidate := Except String (Ty Nat)

structure Function where
  name : String
  namePos : Span
  params : List (String × Candidate)
  ret : Candidate
  envs : List (Nat × List (String × Candidate))
  exprs : List (Span × Candidate)
  /-- Current contents at source entries/results, separate from persistent
  types. An object has one location per named field, so what it currently holds
  is stated field by field; a point that names no record carries none. -/
  entryCurrent : List (Nat × List (String × List (String × Ty Nat))) := []
  exprCurrent : List (Span × List (String × Ty Nat)) := []
  /-- Per-arrow interior claims for a compiled scheme closure, keyed by the
  closure's span and ordered with the arrows of its claimed callable type. A
  polymorphic body has one source span but a different type at each checked
  instantiation, so the compilation supplies the substituted claims rather than
  re-casting one claim to every arrow's result. Empty for every ordinary
  closure. -/
  schemeArrows : List (Span × List (List (Span × Candidate))) := []

/-- Labels are checked against the request's own table, so even a direct caller
cannot turn an out-of-range label into its empty default. -/
def resolve (bound : Nat) (c : Candidate) : Except String (Ty Nat) := do
  let A ← c
  if RequestJson.validTy bound A then pure A
  else throw "source claim contains an out-of-range type label"

end Verification.ExperimentState.SourceClaims
