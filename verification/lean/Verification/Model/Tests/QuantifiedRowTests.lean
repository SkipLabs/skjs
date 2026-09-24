import Verification.Model.Source.RequestJson
import Verification.Model.Types.QuantifiedGraphs

/-! Parameter and scheme rows are opaque to every check: they have no clauses,
so no rule reads a clause off them. A parameter is below itself and below
`unknown`, and nothing else is proved about it. A scheme row has no
introduction rule yet, so no value is typed at one. -/
namespace Verification.Model.QuantifiedRowTests
open ProgramTyping ProgramCertificates CertificateProducer PositiveNormalization PositiveGraphs
  PositiveRules BranchRefinement

/-- 0 null, 1 true, 2 false, 3 undefined, 4 the parameter `T`, 5 the scheme
`<T>(x: T) => T` called on `undefined`, 6 unknown. Rows 4 and 5 hold a clause
that is never read. -/
def types : List (List (Clause (List Nat))) :=
  [[.nul], [.boolLit true], [.boolLit false], [.undef], [.nul], [.nul], [.top]]

def G : NormalGraph Nat where
  rows i := types[i]?.getD []
  params i := i == 4
  schemes i := if i == 5 then some ⟨[4], [([3], [[4]], [4])]⟩ else none

def pool : List (List Nat) := vocabulary G (List.range types.length) [] [[4], [0, 4]]

def found (Γ : List (List Nat)) (t : Tm) (A : List Nat) : Bool :=
  match expression G pool 12 Γ t A with
  | some e => checkTree G e
  | none => false

def subtypes (A B : List Nat) : Bool := (subtype G pool A B).isSome

-- No clause is read off a parameter or scheme row, alone or in a union.
#guard G 4 = [] && G 5 = [] && G 0 = [.nul]
#guard expand G [4] = [] && expand G [0, 4] = [] && expand G [5] = []
#guard expand G [0, 3] = [.nul, .undef]

-- A parameter is below itself, below a union holding it, and below unknown;
-- not below the clause its row happens to hold, nor another type.
#guard subtypes [4] [4]
#guard subtypes [0, 4] [0, 3, 4]
#guard subtypes [4] [6]
#guard !subtypes [4] [0]
#guard !subtypes [4] [0, 3]
#guard !subtypes [0, 4] [0]
#guard !subtypes [5] [0]

-- A test answers nothing about a parameter, and refinement keeps it.
#guard !decide (Answers G [4] .isNul true) && !decide (Answers G [4] .isNul false)
#guard decide (Answers G [0] .isNul true)
#guard tagSlice G [0, 4] .isNul false = [4]
#guard tagSlice G [0, 3] .isNul false = [3]

-- A variable of parameter type is used at that type only. `null` is not a `T`.
#guard found [[4]] (.var 0) [4]
#guard found [[4]] (.var 0) [4, 3]
#guard !found [[4]] (.var 0) [0]
#guard !found [] .nul [4]

-- No value is typed at a scheme row before its introduction rule.
#guard !found [] (.make (.closure 1 (.var 1)) .nul) [5]

end Verification.Model.QuantifiedRowTests
