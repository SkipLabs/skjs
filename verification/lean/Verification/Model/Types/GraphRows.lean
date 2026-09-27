import Verification.Model.Types.PositiveGraphs

/-! A label-independent row representation, shared by the finite source
protocol and parameterized graph presentations. This module only presents
`NormalGraph`; it does not define another interpretation of recursive types. -/
namespace Verification.Model.PositiveGraphs
open CallEffects PositiveNormalization

/-- One row of a graph, independent of how its labels are represented. A
finite wire table uses natural-number labels; a parameterized equation can
use symbolic applications. Names on parameter rows are diagnostic metadata.
The four alternatives are the same in both representations. -/
inductive GraphRow (ι : Type) where
  | clauses (union : List (Clause (List ι)))
  | scheme (binders : List ι) (signatures : List (Arrow (List ι)))
      (bounds : List (ι × List ι)) (variadic : List (RestArrow (List ι)))
  | param (label : ι) (name : String) (kind : ParameterKind)
  | meet (binder : ι) (union : List (Clause (List ι))) (also : List ι := [])
  deriving DecidableEq, Repr, Inhabited

/-- Only a clause row contributes ordinary clauses. Other row kinds have
separate interpretations; an unsupported kind must not turn into a clause. -/
def GraphRow.union : GraphRow ι → List (Clause (List ι))
  | .clauses cs => cs
  | .scheme .. | .param .. | .meet .. => []

/-- The types mentioned by a row, including scheme binders and bounds.
A parameter's identity is metadata, checked separately by the wire boundary. -/
def GraphRow.operands : GraphRow ι → List (List ι)
  | .clauses cs => cs.flatMap Clause.operands
  | .scheme bs sigs bounds rests => bs :: sigs.flatMap Arrow.operands ++
      bounds.map (fun b => b.1 :: b.2) ++ rests.flatMap RestArrow.operands
  | .param _ _ _ => []
  | .meet p cs ps => (p :: ps) :: cs.flatMap Clause.operands

/-- Interpret a single, exhaustive row description. This is shared by the
finite protocol and equation graphs: no representation gets its own choices
about parameters, quantification or dependent intersections. -/
def NormalGraph.ofRowMap (row : ι → GraphRow ι)
    (realm : Option (ArrayRealm ι) := none) : NormalGraph ι :=
  { realm
    rows i := (row i).union
    schemes i := match row i with
      | .scheme bs sigs bounds rests => some ⟨bs, sigs, bounds, rests⟩
      | .clauses .. | .param .. | .meet .. => none
    parameterKinds i := match row i with
      | .param _ _ k => some k
      | .clauses .. | .scheme .. | .meet .. => none
    meets i := match row i with
      | .meet p cs _ => some (p, cs)
      | .clauses .. | .scheme .. | .param .. => none
    meetParams i := match row i with
      | .meet _ _ ps => ps
      | .clauses .. | .scheme .. | .param .. => [] }

end Verification.Model.PositiveGraphs
