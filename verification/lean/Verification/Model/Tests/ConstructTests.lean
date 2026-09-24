import Verification.Model.Source.RequestJson

/-! Class values and `new`: a class is construct-only code, which `new` runs and
a plain call cannot, and an arrow is call-only code, which `new` cannot run.
Evidence is produced by search and accepted only by the checker. -/
namespace Verification.Model.ConstructTests
open Lean ProgramTyping ProgramCertificates CertificateProducer RequestJson PositiveNormalization PositiveGraphs

/-- 0 null, 1 true, 2 false, 3 undefined, 4 a class taking and returning a
Boolean, 5 a function taking and returning a Boolean, 6 unknown. -/
def types : List (List (Clause (List Nat))) :=
  [[.nul], [.boolLit true], [.boolLit false], [.undef],
   [.ctors [([[1, 2]], [1, 2])]],
   [.arrs [([6], [[1, 2]], [1, 2])] []], [.top]]

def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []

def pool : List (List Nat) := vocabulary G (List.range types.length) [] [[1, 2]]

/-- A class whose body returns its parameter: slot 0 is the receiver `new`
passes, `undefined`, and slot 1 the parameter. -/
def classValue : Tm := .make (.closure 1 (.var 1) .construct) .nul

/-- The same body as an arrow's call-only code. -/
def arrowValue : Tm := .make (.closure 1 (.var 1)) .nul

def found (Γ : List (List Nat)) (t : Tm) (A : List Nat) : Bool :=
  match expression G pool 12 Γ t A with
  | some e => checkTree G e
  | none => false

-- A class value has its construct signature, and `new` on it yields the result.
#guard found [] classValue [4]
#guard found [[4]] (.construct (.var 0) [.tru]) [1, 2]
#guard found [] (.letE classValue (.construct (.var 0) [.tru])) [1, 2]

-- An arrow is no class, `new` cannot run an arrow, a plain call cannot run a
-- class, and a constructor's parameter contract holds.
#guard !found [] arrowValue [4]
#guard !found [[5]] (.construct (.var 0) [.tru]) [1, 2]
#guard !found [[4]] (.call (.var 0) [.tru]) [1, 2]
#guard !found [[4]] (.construct (.var 0) [.nul]) [1, 2]

-- A plain call dispatches nothing on construct-only code.
#guard CallArguments.dispatch (.closure 1 .nul .construct) .undef [] = none

-- A call-only closure's JSON is unchanged: its kind is left out. A class's
-- kind is spelled, and both read back as themselves.
#guard !((toJson (Tm.objAt [] (.closure 1 .nul))).compress.contains "kind")
#guard (toJson (Tm.objAt [] (.closure 1 .nul .construct))).compress.contains "construct"
#guard (fromJson? (toJson (Tm.objAt [] (.closure 1 .nul .construct))) : Except String Tm).toOption ==
  some (Tm.objAt [] (.closure 1 .nul .construct))
#guard (fromJson? (toJson (Tm.construct (.var 0) [.tru])) : Except String Tm).toOption ==
  some (Tm.construct (.var 0) [.tru])
#guard (fromJson? (toJson ([Clause.ctors [([[1, 2]], [1, 2])]] : List (Clause (List Nat))))
  : Except String (List (Clause (List Nat)))).toOption == some [Clause.ctors [([[1, 2]], [1, 2])]]

end Verification.Model.ConstructTests
