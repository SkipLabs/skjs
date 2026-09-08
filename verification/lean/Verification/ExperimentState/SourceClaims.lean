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

/-- This source adapter uses SourceTypes.graph, not an arbitrary supplied graph.
Even direct callers must not turn an out-of-range label into its empty default. -/
def resolve (c : Candidate) : Except String (Ty Nat) := do
  let A ← c
  if RequestJson.validTy SourceTypes.types.length A then pure A
  else throw "source claim contains an out-of-range type label"

end Verification.ExperimentState.SourceClaims
