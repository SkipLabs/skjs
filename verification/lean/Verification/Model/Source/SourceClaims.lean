import Verification.Model.Source.SourceTypes

/-! Producer-independent claims for the current bounded fragment. Candidates
contain calculus type labels, never producer JSON. A decoding failure is retained
until a claim is used: exporters may include unrelated unsupported bindings such
as implicit `this`; those failures must never be interpreted as a type. -/
namespace Verification.Model.SourceClaims
open ProgramTyping

abbrev Candidate := Except String (Ty Nat)

/-- What one closure body claims under one of its advertised signatures. -/
structure Overlay where
  exprs : List (Span × Candidate)
  envs : List (Nat × List (String × Candidate)) := []
  entryCurrent : List (Nat × List (String × List (PropKey × Ty Nat))) := []
  exprCurrent : List (Span × List (PropKey × Ty Nat)) := []

  /-- Source annotations after a checked scheme substitution; not producer claims. -/
  initializedParams : Option (List (Ty Nat)) := none

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
  entryCurrent : List (Nat × List (String × List (PropKey × Ty Nat))) := []
  exprCurrent : List (Span × List (PropKey × Ty Nat)) := []
  /-- Per-arrow interior claims for one closure, keyed by its span and ordered
  with the arrows of its claimed callable type. Statement entries inside the
  body are stated per arrow as well: an entry environment replaces the context
  it is checked against, so one body's entries differ with its signature. One body has a different
  obligation at each arrow, so these are the claims it carries under each,
  rather than one claim re-cast to every arrow's result. A compiled scheme
  supplies the substituted claims for its checked instantiations; an overloaded
  closure's producer states them. Empty for a closure advertising one
  signature. -/
  arrowClaims : List (Span × List Overlay) := []

/-- A row replaces each named site's whole claim, including absence of a
refinement. Retaining the enclosing row's refinement would combine claims
from different signatures. -/
def Function.withOverlay (f : Function) (row : Overlay) : Function :=
  { f with
    exprs := row.exprs ++ f.exprs
    envs := row.envs ++ f.envs
    entryCurrent := row.entryCurrent ++ f.entryCurrent.filter (fun p =>
      !(row.envs.map Prod.fst).contains p.1)
    exprCurrent := row.exprCurrent ++ f.exprCurrent.filter (fun p =>
      !(row.exprs.map Prod.fst).contains p.1) }

/-- Labels are checked against the request's own table, so even a direct caller
cannot turn an out-of-range label into its empty default. -/
def resolve (bound : Nat) (c : Candidate) : Except String (Ty Nat) := do
  let A ← c
  if RequestJson.validTy bound A then pure A
  else throw "source claim contains an out-of-range type label"

end Verification.Model.SourceClaims
