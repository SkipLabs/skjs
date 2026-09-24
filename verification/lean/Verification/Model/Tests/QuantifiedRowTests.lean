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
that is never read. 7 `(x: boolean) => boolean`, 8 `(x: null) => null`,
9 `Box<T>`, 10 `<T>(x: T) => Box<T>`, 11 `Box<boolean>`,
12 `(x: boolean) => Box<boolean>`, 13 `Box<null>`, 14 `(x: boolean) => Box<null>`,
15 `(x: null) => boolean`, 16 `(x: T) => T` with `T` opaque, 17 the scheme
`<U>(x: U) => U`, 18 its parameter `U`, 19 `(x: U) => U` with `U` opaque. -/
def types : List (List (Clause (List Nat))) :=
  [[.nul], [.boolLit true], [.boolLit false], [.undef], [.nul], [.nul], [.top],
   [.arrs [([3], [[1, 2]], [1, 2])] []], [.arrs [([3], [[0]], [0])] []],
   [.refs [(valueField, [4])] [] []], [], [.refs [(valueField, [1, 2])] [] []],
   [.arrs [([3], [[1, 2]], [11])] []], [.refs [(valueField, [0])] [] []],
   [.arrs [([3], [[1, 2]], [13])] []], [.arrs [([3], [[0]], [1, 2])] []],
   [.arrs [([3], [[4]], [4])] []], [], [], [.arrs [([3], [[18]], [18])] []]]

def G : NormalGraph Nat where
  rows i := types[i]?.getD []
  params i := i == 4 || i == 18
  schemes i :=
    if i == 5 then some ⟨[4], [([3], [[4]], [4])]⟩
    else if i == 10 then some ⟨[4], [([3], [[4]], [9])]⟩
    else if i == 17 then some ⟨[18], [([3], [[18]], [18])]⟩
    else none

def pool : List (List Nat) :=
  vocabulary G (List.range types.length) [] [[4], [0, 4]] ++ (List.range types.length).map ([·])

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

-- Instantiation: a scheme row is below each instance of its signatures, the
-- instance named by a checked map.
#guard subtypes [5] [7]
#guard subtypes [5] [8]
#guard subtypes [10] [12]
-- Hand-written certificates: a domain closed under reads, and its free
-- parameter rows (computed here, checked by `FreeOk`).
def dom (S : List Nat) : List Nat := readsFrom G 64 S
def fm (D : List Nat) : PositiveRules.FreeMap Nat := freeMapOf G D 64 []
def inst (θ : PositiveRules.InstMap Nat) (roots : List Nat) : PositiveCertificates.Proof Nat :=
  .inst θ (dom roots) (fm (dom roots))
#guard PositiveCertificates.check G [5] [7] (inst [(4, [1, 2])] [3, 4, 1, 2])
-- The map must be an instance: `T` at `null` does not give `(x: boolean) => boolean`,
-- and `Box<null>` is not `Box<T>` at `boolean`.
#guard !PositiveCertificates.check G [5] [7] (inst [(4, [0])] [3, 4, 0])
#guard !PositiveCertificates.check G [10] [12] (inst [(4, [1, 2]), (9, [13])] [3, 4, 9, 1, 2])
#guard !subtypes [10] [14]
#guard !subtypes [5] [15]
#guard PositiveCertificates.check G [10] [12] (inst [(4, [1, 2]), (9, [11])] [3, 4, 9, 1, 2])
-- The domain must be closed under reads, and hold the instances.
#guard !PositiveCertificates.check G [5] [7] (.inst [(4, [1, 2])] [4, 3] (fm [4, 3]))
#guard !PositiveCertificates.check G [10] [12] (.inst [(4, [1, 2]), (9, [11])] [4, 3, 1, 2]
  (fm [4, 3, 1, 2]))
-- The free-parameter certificate must be sound: omitting `T` from `Box<T>`'s is refused.
#guard !PositiveCertificates.check G [10] [12]
  (.inst [(4, [1, 2]), (9, [11])] (dom [3, 4, 9, 1, 2]) ((fm (dom [3, 4, 9, 1, 2])).map
    fun p => if p.1 == 9 then (9, []) else p))

-- Generalization: `<T>(x: T) => T` is below `<U>(x: U) => U`, through the
-- instance `T := U` with `U` opaque; `(x: boolean) => boolean` is not.
#guard subtypes [5] [17]
#guard !subtypes [7] [17]
#guard PositiveCertificates.check G [5] [17]
  (.gen (dom [5]) (fm (dom [5])) [19] (inst [(4, [18])] [3, 4, 18]))
-- The domain must be closed under reads.
#guard !PositiveCertificates.check G [5] [17] (.gen [5, 3] (fm [5, 3]) [19] (inst [(4, [18])] [3, 4, 18]))
-- `(x: T) => T` at one `T` is not generic: its free parameter is the scheme's own binder.
#guard !subtypes [16] [5]
#guard !PositiveCertificates.check G [16] [5] (.gen (dom [16]) (fm (dom [16])) [16] .subset)
-- A scheme's own binder is not free in it: `<T>(x: T) => T` reads `T` only under its binder.
#guard fv (fm (dom [5])) 5 == [] && fv (fm (dom [16])) 16 == [4]

-- A value of the scheme is typed at an instance by subsumption.
#guard found [[5]] (.var 0) [7]
#guard found [[10]] (.var 0) [12]
#guard !found [[10]] (.var 0) [14]
-- Calling a generic function: `id(true)` is a Boolean, not `null`;
-- `wrap(true)` is a `Box<boolean>`, not a `Box<null>`.
#guard found [[5]] (.call (.var 0) [.tru]) [1, 2]
#guard !found [[5]] (.call (.var 0) [.tru]) [0]
#guard found [[10]] (.call (.var 0) [.tru]) [11]
#guard !found [[10]] (.call (.var 0) [.tru]) [13]

-- On the wire: a table of rows, where scheme and parameter rows are rows of
-- their own kind. Its graph is the one above.
open RequestJson in
def table : List Row :=
  (List.range types.length).map fun i =>
    if i == 4 then .param 4 else if i == 18 then .param 18
    else if i == 5 then .scheme [4] [([3], [[4]], [4])]
    else if i == 10 then .scheme [4] [([3], [[4]], [9])]
    else if i == 17 then .scheme [18] [([3], [[18]], [18])]
    else .clauses (types[i]?.getD [])
def wire : NormalGraph Nat := RequestJson.tableGraph table
#guard (List.range 20).all fun i =>
  wire.params i == G.params i && wire.plain i == G.plain i && wire i == G i &&
  (wire.schemes i).isSome == (G.schemes i).isSome
#guard (subtype wire pool [5] [7]).isSome && (subtype wire pool [10] [12]).isSome &&
  (subtype wire pool [10] [14]).isNone && (subtype wire pool [5] [17]).isSome
#guard RequestJson.validRows table
-- A parameter row names its own label, a scheme's binders are parameter rows,
-- and a scheme's labels index the table.
#guard !RequestJson.validRows (table.set 4 (.param 5))
#guard !RequestJson.validRows (table.set 5 (.scheme [3] [([3], [[3]], [3])]))
#guard !RequestJson.validRows (table.set 5 (.scheme [4] [([3], [[4]], [25])]))
-- A clause row is spelled as before; the other kinds read back as themselves.
#guard Lean.toJson (RequestJson.Row.clauses [.nul]) == Lean.toJson [Clause.nul (α := List Nat)]
#guard (Lean.fromJson? (Lean.toJson table) : Except String (List RequestJson.Row)).toOption == some table

end Verification.Model.QuantifiedRowTests
