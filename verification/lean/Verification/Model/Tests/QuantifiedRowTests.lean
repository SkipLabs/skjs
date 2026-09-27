import Verification.Model.Source.RequestJson
import Verification.Model.Types.QuantifiedGraphs

/-! Parameter and scheme rows are opaque to every check: they have no clauses,
so no rule reads a clause off them. A parameter is below itself and below
`unknown`, and nothing else is proved about it. A value is typed at a scheme
row only as graph code checked at its signatures (`funScheme`). -/
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
   [.arrs [⟨[3], [[1, 2]], [1, 2], .unrestricted⟩] []], [.arrs [⟨[3], [[0]], [0], .unrestricted⟩] []],
   [.refs [(valueField, [4])] [] []], [], [.refs [(valueField, [1, 2])] [] []],
   [.arrs [⟨[3], [[1, 2]], [11], .unrestricted⟩] []], [.refs [(valueField, [0])] [] []],
   [.arrs [⟨[3], [[1, 2]], [13], .unrestricted⟩] []], [.arrs [⟨[3], [[0]], [1, 2], .unrestricted⟩] []],
   [.arrs [⟨[3], [[4]], [4], .unrestricted⟩] []], [], [], [.arrs [⟨[3], [[18]], [18], .unrestricted⟩] []],
   [], [.arrs [⟨[3], [[1]], [1], .unrestricted⟩] []]]

def G : NormalGraph Nat where
  rows i := types[i]?.getD []
  parameterKinds i := if i == 4 || i == 18 then some .value else none
  schemes i :=
    if i == 5 then some ⟨[4], [⟨[3], [[4]], [4], .unrestricted⟩], [], []⟩
    else if i == 10 then some ⟨[4], [⟨[3], [[4]], [9], .unrestricted⟩], [], []⟩
    else if i == 17 then some ⟨[18], [⟨[3], [[18]], [18], .unrestricted⟩], [], []⟩
    else if i == 20 then some ⟨[4], [⟨[3], [[4]], [4], .unrestricted⟩], [(4, [1, 2])], []⟩
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

-- Instantiation: a scheme row is below each instance of its signatures, the
-- instance named by a checked map.
#guard subtypes [5] [7]
#guard subtypes [5] [8]
#guard subtypes [10] [12]
-- Certificates as the producer builds them, and tampered copies.
def dom (S : List Nat) : List Nat := readsFrom G 64 S
def fm (D : List Nat) : PositiveRules.FreeMap Nat := freeMapOf G D 64 []
def cert (A B : List Nat) : PositiveCertificates.Proof Nat := (instProof G 64 A B).getD .subset
#guard PositiveCertificates.check G [5] [7] (cert [5] [7])
-- The instances must be the ones the table uses: `T` at `null` does not give
-- `(x: boolean) => boolean`.
#guard match cert [5] [7] with
  | .inst c => !PositiveCertificates.check G [5] [7] (.inst { c with instances := [[0]] })
  | _ => false
-- An entry must map a row to its substituted copy: `Box<null>` is not `Box<T>`
-- at `boolean`.
#guard match cert [10] [12] with
  | .inst c => PositiveCertificates.check G [10] [12] (.inst c) &&
      !PositiveCertificates.check G [10] [12]
        (.inst { c with table := c.table.map fun e => if e.1 == 9 then (9, e.2.1, [13]) else e })
  | _ => false
#guard !subtypes [10] [14]
#guard !subtypes [5] [15]
-- The domain must hold the table's rows and be closed under reads, and the
-- free-parameter certificate must be sound.
#guard match cert [10] [12] with
  | .inst c =>
      !PositiveCertificates.check G [10] [12] (.inst { c with domain := c.domain.filter (· != 9) }) &&
      !PositiveCertificates.check G [10] [12]
        (.inst { c with free := c.free.map fun p => if p.1 == 9 then (9, []) else p })
  | _ => false

-- Generalization: `<T>(x: T) => T` is below `<U>(x: U) => U`, through the
-- instance `T := U` with `U` opaque; `(x: boolean) => boolean` is not.
#guard subtypes [5] [17]
#guard !subtypes [7] [17]
#guard PositiveCertificates.check G [5] [17] (.gen (dom [5]) (fm (dom [5])) [19] (cert [5] [19]))
-- The domain must be closed under reads.
#guard !PositiveCertificates.check G [5] [17] (.gen [5, 3] (fm [5, 3]) [19] (cert [5] [19]))
-- `(x: T) => T` at one `T` is not generic: its free parameter is the scheme's own binder.
#guard !subtypes [16] [5]
#guard !PositiveCertificates.check G [16] [5] (.gen (dom [16]) (fm (dom [16])) [16] .subset)
-- A scheme's own binder is not free in it: `<T>(x: T) => T` reads `T` only under its binder.
#guard fv (fm (dom [5])) 5 == [] && fv (fm (dom [16])) 16 == [4]

-- Bounds: `<T extends boolean>(x: T) => T` (20) is below `(x: true) => true`
-- (21), its instance at `true` within the bound, and not below
-- `(x: null) => null` (8), whose instance is outside it. The unbounded scheme
-- is below the bounded one; the bounded one is not below the unbounded one.
#guard subtypes [20] [21]
#guard !subtypes [20] [8]
#guard subtypes [5] [21] && subtypes [5] [8]
#guard subtypes [5] [20]
#guard !subtypes [20] [5]
-- The bound must hold of the instance the table uses.
#guard match cert [20] [21] with
  | .inst c => !PositiveCertificates.check G [20] [21] (.inst { c with instances := [[0]] })
  | _ => false

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
    if i == 4 then .param 4 "T" .value else if i == 18 then .param 18 "U" .value
    else if i == 5 then .scheme [4] [⟨[3], [[4]], [4], .unrestricted⟩] [] []
    else if i == 10 then .scheme [4] [⟨[3], [[4]], [9], .unrestricted⟩] [] []
    else if i == 17 then .scheme [18] [⟨[3], [[18]], [18], .unrestricted⟩] [] []
    else if i == 20 then .scheme [4] [⟨[3], [[4]], [4], .unrestricted⟩] [(4, [1, 2])] []
    else .clauses (types[i]?.getD [])
def wire : NormalGraph Nat := RequestJson.tableGraph table
#guard (List.range types.length).all fun i =>
  wire.params i == G.params i && wire.plain i == G.plain i && wire i == G i &&
  (wire.schemes i).isSome == (G.schemes i).isSome
#guard (subtype wire pool [5] [7]).isSome && (subtype wire pool [10] [12]).isSome &&
  (subtype wire pool [10] [14]).isNone && (subtype wire pool [5] [17]).isSome
#guard RequestJson.validRows table
-- A parameter row names its own label, a scheme's binders are parameter rows,
-- and a scheme's labels index the table.
#guard !RequestJson.validRows (table.set 4 (.param 5 "T" .value))
#guard !RequestJson.validRows (table.set 5 (.scheme [3] [⟨[3], [[3]], [3], .unrestricted⟩] [] []))
#guard !RequestJson.validRows (table.set 5 (.scheme [4] [⟨[3], [[4]], [25], .unrestricted⟩] [] []))
-- A pack binder and a value binder cannot exchange their instantiation types.
private def sortedKinds : NormalGraph Nat := RequestJson.tableGraph [
  .param 0 "P" .arguments, .param 1 "T" .value,
  .clauses [.pack ⟨[[3]], [], none, false, .dense⟩ []], .clauses [.num]]
#guard PositiveRules.instKinds sortedKinds [0,1] [[2],[3]]
#guard !PositiveRules.instKinds sortedKinds [0] [[3]]
#guard !PositiveRules.instKinds sortedKinds [1] [[2]]
#guard !PositiveRules.instKinds sortedKinds [0] [[2,3]]
-- A table certificate must not bypass the same check.
#guard PositiveRules.entryOk sortedKinds [] [] (0, [(0,[2])], [2])
#guard !PositiveRules.entryOk sortedKinds [] [] (0, [(0,[3])], [3])
-- The wire must state a kind; there is no implicit legacy/value default.
#guard (Lean.fromJson? (Lean.Json.mkObj [("param", Lean.toJson (0 : Nat)),
  ("name", Lean.toJson "P")]) : Except String RequestJson.Row).toOption.isNone
#guard (Lean.fromJson? (Lean.toJson (RequestJson.Row.param 0 "P" .arguments)) :
  Except String RequestJson.Row).toOption == some (.param 0 "P" .arguments)
-- A clause row is spelled as before; the other kinds read back as themselves.
#guard Lean.toJson (RequestJson.Row.clauses [.nul]) == Lean.toJson [Clause.nul (α := List Nat)]
#guard (Lean.fromJson? (Lean.toJson table) : Except String (List RequestJson.Row)).toOption == some table

-- A generic method of a generic type, with coloured binders:
-- `Box<T> { readonly value: T; readonly map<U>(f: (x: T) => U): Box<U> }`.
-- `Box<boolean>`'s `map` binds `Uᵃ` (5) and returns `Box<Uᵃ>` (10), whose
-- `map` binds `Uᵇ` (6) and returns `Box<Uᵇ>` (13), whose `map` binds `Uᵃ`
-- again and returns `Box<Uᵃ>`: a finite graph. `Box<null>` (16), as an
-- annotation lowers it, binds `Uᵃ`. Calling `map` at `U := null` returns it:
-- the table relates `Box<Uᵃ>` under `Uᵃ := null` to `Box<null>`, and `Box<Uᵃ>`'s
-- inner `map`, binding `Uᵇ`, to `Box<null>`'s, binding `Uᵃ`.
namespace Colours
def types : List (List (Clause (List Nat))) :=
  [[.nul], [.boolLit true], [.boolLit false], [.undef], [.top], [], [],
   [.refs [] [] [(valueField, [1, 2]), ("map", [8])]], [],
   [.arrs [⟨[4], [[1, 2]], [5], .unrestricted⟩] []],
   [.refs [] [] [(valueField, [5]), ("map", [11])]], [],
   [.arrs [⟨[4], [[5]], [6], .unrestricted⟩] []],
   [.refs [] [] [(valueField, [6]), ("map", [14])]], [],
   [.arrs [⟨[4], [[6]], [5], .unrestricted⟩] []],
   [.refs [] [] [(valueField, [0]), ("map", [17])]], [],
   [.arrs [⟨[4], [[0]], [5], .unrestricted⟩] []],
   [.arrs [⟨[7], [[20]], [16], .unrestricted⟩] []],
   [.arrs [⟨[4], [[1, 2]], [0], .unrestricted⟩] []],
   [.arrs [⟨[7], [[20]], [7], .unrestricted⟩] []],
   [.refs [] [] [(valueField, [0]), ("map", [23])]], [],
   [.arrs [⟨[4], [[0]], [6], .unrestricted⟩] []]]
def H : NormalGraph Nat where
  rows i := types[i]?.getD []
  parameterKinds i := if i == 5 || i == 6 then some .value else none
  schemes i :=
    if i == 8 then some ⟨[5], [⟨[7], [[9]], [10], .unrestricted⟩], [], []⟩
    else if i == 11 then some ⟨[6], [⟨[10], [[12]], [13], .unrestricted⟩], [], []⟩
    else if i == 14 then some ⟨[5], [⟨[13], [[15]], [10], .unrestricted⟩], [], []⟩
    else if i == 17 then some ⟨[5], [⟨[16], [[18]], [10], .unrestricted⟩], [], []⟩
    else if i == 23 then some ⟨[6], [⟨[22], [[24]], [13], .unrestricted⟩], [], []⟩
    else none
def pool : List (List Nat) := (List.range types.length).map ([·])
#guard match instProof H 64 [8] [19] with
  | some p => PositiveCertificates.check H [8] [19] p
  | none => false
-- `b.map(f)` for `f: (x: boolean) => null` is not a `Box<boolean>`.
#guard (instProof H 64 [8] [21]).all fun p => !PositiveCertificates.check H [8] [21] p
#guard (subtype H pool [8] [19]).isSome && (subtype H pool [8] [21]).isNone
-- Two copies of `Box<null>`, whose `map` binds `Uᵃ` (16) or `Uᵇ` (22), are one
-- type up to renaming, related by a table under the empty context; neither is
-- a `Box<boolean>`.
#guard match tableProof H 64 [22] [16], tableProof H 64 [16] [22] with
  | some p, some q => PositiveCertificates.check H [22] [16] p && PositiveCertificates.check H [16] [22] q
  | _, _ => false
#guard (subtype H pool [22] [16]).isSome && (subtype H pool [16] [22]).isSome
#guard (subtype H pool [22] [7]).isNone && (subtype H pool [7] [16]).isNone
end Colours

end Verification.Model.QuantifiedRowTests
