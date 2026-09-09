import Verification.ExperimentState.SourceTypes

/-! Producer-independent claims for the current bounded source slice. Candidates
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
  /-- Current contents at source entries/results, separate from persistent types. -/
  entryCurrent : List (Nat × List (String × Ty Nat)) := []
  exprCurrent : List (Span × Ty Nat) := []

/-- Labels are checked against the request's own table, so even a direct caller
cannot turn an out-of-range label into its empty default. -/
def resolve (bound : Nat) (c : Candidate) : Except String (Ty Nat) := do
  let A ← c
  if RequestJson.validTy bound A then pure A
  else throw "source claim contains an out-of-range type label"

end Verification.ExperimentState.SourceClaims
