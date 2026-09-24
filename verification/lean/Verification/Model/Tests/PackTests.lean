import Verification.Model.Source.RequestJson

/-! Argument packs: the argument lists a tuple contract admits, as one value.
A pack contract covers another position by position and covariantly, within
its length bounds; subtyping evidence is produced by search and accepted only
by the checker. -/
namespace Verification.Model.PackTests
open Lean PositiveNormalization PositiveGraphs CertificateProducer

/-- 0 number, 1 string, 2 `[number, string]`, 3 `(number | string)[]`,
4 `[number]`, 5 `number[]`, 6 `[number, string?]`, 7 unknown, 8 `new (x: number)`,
9 `new (...p: [number])`, 10 `new (...p: number[])`, 11 `{a: number}`, 12
`[{a: number}]`, 13 `new (...p: [{a: number}])`, 14 `new (x: {a: number})`, 15
`new ()`, 16 `[]`, 17 `new (...p: [])`, 18 `new (...p: (number | string)[])`; every
constructor's result is unknown. -/
def types : List (List (Clause (List Nat))) :=
  [[.num], [.str],
   [.pack ⟨[[0], [1]], [], none, false⟩ []],
   [.pack ⟨[], [], some [0, 1], false⟩ []],
   [.pack ⟨[[0]], [], none, false⟩ []],
   [.pack ⟨[], [], some [0], false⟩ []],
   [.pack ⟨[[0]], [[1]], none, false⟩ []],
   [.top],
   [.ctors [([[0]], [7])]],
   [.ctors [] [([], [4], [7])]],
   [.ctors [] [([], [5], [7])]],
   [.refs [(.str "a", [0])] [] []],
   [.pack ⟨[[11]], [], none, false⟩ []],
   [.ctors [] [([], [12], [7])]],
   [.ctors [([[11]], [7])]],
   [.ctors [([], [7])]],
   [.pack ⟨[], [], none, false⟩ []],
   [.ctors [] [([], [16], [7])]],
   [.ctors [] [([], [3], [7])]]]

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

-- A class taking a number meets a construct signature whose rest is exactly
-- one number, and one taking nothing a rest of no position; not a rest of any
-- length, nor one of another arity.
#guard sub [8] [9]
#guard sub [15] [17]
#guard !sub [8] [10]
#guard !sub [15] [9]
-- A record position is not stable: the pack holds it below the current level
-- only, so the fixed signature is not shown to cover the rest.
#guard !sub [14] [13]
-- Variadic construct signatures compare their rests as packs.
#guard sub [18] [10]
#guard !sub [10] [18]
#guard sub [9] [9]

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

-- A construct signature list without variadic ones reads back as itself, and
-- so does one with them.
#guard (fromJson? (toJson (types[8]!)) : Except String (List (Clause (List Nat)))).toOption ==
  some types[8]!
#guard (fromJson? (toJson (types[9]!)) : Except String (List (Clause (List Nat)))).toOption ==
  some types[9]!
#guard !((toJson (types[8]!)).compress.contains "variadic")

-- No program makes a pack.
#guard !ObjectCoherence.sourceTerm (.args [.num 1])

end Verification.Model.PackTests
