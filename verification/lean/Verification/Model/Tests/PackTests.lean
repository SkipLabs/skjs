import Verification.Model.Source.RequestJson

/-! Argument packs: the argument lists a tuple contract admits, as one value.
A pack contract covers another position by position and covariantly, within
its length bounds; subtyping evidence is produced by search and accepted only
by the checker. -/
namespace Verification.Model.PackTests
open Lean PositiveNormalization PositiveGraphs CertificateProducer

/-- 0 number, 1 string, 2 `[number, string]`, 3 `(number | string)[]`,
4 `[number]`, 5 `number[]`, 6 `[number, string?]`, 7 unknown. -/
def types : List (List (Clause (List Nat))) :=
  [[.num], [.str],
   [.pack ⟨[[0], [1]], [], none, false⟩ []],
   [.pack ⟨[], [], some [0, 1], false⟩ []],
   [.pack ⟨[[0]], [], none, false⟩ []],
   [.pack ⟨[], [], some [0], false⟩ []],
   [.pack ⟨[[0]], [[1]], none, false⟩ []],
   [.top]]

def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []

def pool : List (List Nat) := vocabulary G (List.range types.length) [] [[0, 1]]

def sub (A B : List Nat) : Bool :=
  match subtype G pool A B with
  | some p => PositiveCertificates.check G A B p
  | none => false

-- A tuple's positions within a rest's element, and a prefix within one
-- admitting further optional positions.
#guard sub [2] [3]
#guard sub [4] [5]
#guard sub [4] [6]
#guard sub [2] [6]
#guard sub [5] [3]
#guard sub [2] [7]

-- A rest admits lists of any length, so it is within no bounded tuple; a
-- position outside the target's family, or a list longer than the target
-- admits, is refused.
#guard !sub [5] [4]
#guard !sub [3] [5]
#guard !sub [2] [5]
#guard !sub [6] [4]
#guard !sub [2] [4]
#guard !sub [4] [2]

-- Meeting two packs keeps every contract, on the one list.
#guard meet (Clause.pack (⟨[[0]], [], none, false⟩ : Tuple (List Nat)) [])
    (.pack ⟨[], [], some [0], false⟩ []) =
  [.pack ⟨[[0]], [], none, false⟩ [⟨[], [], some [0], false⟩]]
#guard meet (Clause.pack (⟨[[0]], [], none, false⟩ : Tuple (List Nat)) []) .num = []

-- The pack value and the clause read back as themselves.
#guard (fromJson? (toJson (Tm.args [.num 1, .str "a"])) : Except String Tm).toOption ==
  some (Tm.args [.num 1, .str "a"])
#guard (fromJson? (toJson (types[6]!)) : Except String (List (Clause (List Nat)))).toOption ==
  some types[6]!

-- No program makes a pack.
#guard !ObjectCoherence.sourceTerm (.args [.num 1])

end Verification.Model.PackTests
