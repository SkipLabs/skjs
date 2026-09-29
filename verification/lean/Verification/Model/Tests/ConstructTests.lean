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
   [.arrs [⟨[6], [[1, 2]], [1, 2], .unrestricted⟩] []], [.top]]

def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []

def pool : List (List Nat) := vocabulary G (List.range types.length) [] [[1, 2]]

/-- A class whose code returns its parameter: slot 0 is the receiver `new`
passes, `undefined`, and slot 1 the parameter. -/
def classValue : Tm := .makeFn (.graph 1 [.var 1] [(.ret, none)] 0 [] .construct) .nul

/-- The same code as an arrow's call-only code. -/
def arrowValue : Tm := .makeFn (.graph 1 [.var 1] [(.ret, none)] 0 []) .nul

/-- Evidence found and checked, every code admitted: whether the code meets its
signatures is the unit's code table's question, not the creation's. -/
def found (Γ : List (List Nat)) (t : Tm) (A : List Nat) : Bool :=
  match expression G pool 12 Γ t A with
  | some e => checkTree G e (fun _ => true)
  | none => false

-- A class value has its construct signature, and `new` on it yields the result.
#guard found [] classValue [4]
#guard found [[4]] (.construct (.var 0) [.tru]) [1, 2]
#guard found [] (.letE classValue (.construct (.var 0) [.tru])) [1, 2]

-- An arrow is no class, a class is no arrow, `new` cannot run an arrow, a
-- plain call cannot run a class, and a constructor's parameter contract holds.
#guard !found [] arrowValue [4]
#guard !found [] classValue [5]
#guard !found [[5]] (.construct (.var 0) [.tru]) [1, 2]
#guard !found [[4]] (.call (.var 0) [.tru]) [1, 2]
#guard !found [[4]] (.construct (.var 0) [.nul]) [1, 2]

-- A plain call dispatches nothing on construct-only code.
#guard CallArguments.dispatch (.graph 1 [.var 1] [(.ret, none)] 0 [] .construct) .undef [] = none
-- `new` runs construct-only code without a rest, and no other.
#guard (CallArguments.construction (.graph 1 [.var 1] [(.ret, none)] 0 [] .construct)).isSome
#guard (CallArguments.construction (.graph 1 [.var 1] [(.ret, none)] 0 [])).isNone
#guard (CallArguments.construction (.graph 1 [.var 1] [(.ret, none)] 0 [] .construct true)).isNone

-- Graph code's kind and rest are spelled only when not `call` and `false`.
#guard !((toJson (Tm.objAt [] (.graph 1 [] [] 0 []))).compress.contains "kind")
#guard !((toJson (Tm.objAt [] (.graph 1 [] [] 0 []))).compress.contains "rest")
#guard (fromJson? (toJson (Tm.objAt [] (.graph 1 [] [] 0 [] .construct))) : Except String Tm).toOption ==
  some (Tm.objAt [] (.graph 1 [] [] 0 [] .construct))
#guard (fromJson? (toJson (Tm.objAt [] (.graph 1 [] [] 0 [] .call true))) : Except String Tm).toOption ==
  some (Tm.objAt [] (.graph 1 [] [] 0 [] .call true))
#guard (fromJson? (toJson (Tm.construct (.var 0) [.tru])) : Except String Tm).toOption ==
  some (Tm.construct (.var 0) [.tru])
#guard (fromJson? (toJson ([Clause.ctors [([[1, 2]], [1, 2])]] : List (Clause (List Nat))))
  : Except String (List (Clause (List Nat)))).toOption == some [Clause.ctors [([[1, 2]], [1, 2])]]

end Verification.Model.ConstructTests
