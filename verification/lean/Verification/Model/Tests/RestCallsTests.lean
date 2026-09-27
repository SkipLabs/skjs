import Verification.Model.Programs.CertificateProducer

/-! Variadic creation and calls, with and without spreads, searched by the
producer and accepted by the checker; and the spreads the checker refuses. -/
namespace Verification.Model.RestCallsTests
open ProgramTyping ProgramCertificates CertificateProducer PositiveNormalization

/-- 0 number, 1 undefined, 2 a store of `number | undefined` of any length,
3 its array, 4 `(a: number, ...r: (number | undefined)[]) => number`,
5 the store of a `[number]` tuple, 6 a store of `number` of any length,
7 `(a: number, ...r: number[]) => number`, 8 the array of 6, 9 the array of 5,
10 `(a: number, b: number) => number`, 11 `(a?: number, ...r: number[]) => number`,
12 unknown, 13 the rest `...(number | undefined)[]`, 14 the rest `...number[]`,
15 the rest `...[number, number]`, 16 `(...r: [number, number]) => number`, 17 the
store of a `[number, number]` tuple, 18 its array, 19 `(...r: [number, number])`
returning its rest as an array, 20 `(...r: number[])` returning its rest as an array, 21 the
rest `...[number]`, 22 `(a: number, ...r: [number]) => number`. Every
signature takes any
receiver; a signature's rest is an argument pack. -/
def G : PositiveGraphs.NormalGraph Nat := .ofRows fun
  | 0 => [.num]
  | 1 => [.undef]
  | 2 => [.list ⟨[], [], some [0,1], false, true⟩ []]
  | 3 => [.refs [(CallArguments.arrayStoreField, [2])] [] []]
  | 4 => [.arrs [] [⟨[12], ([[0]], [13]), [0], .unrestricted⟩]]
  | 5 => [.list ⟨[[0]], [], none, false, true⟩ []]
  | 6 => [.list ⟨[], [], some [0], false, true⟩ []]
  | 7 => [.arrs [] [⟨[12], ([[0]], [14]), [0], .unrestricted⟩]]
  | 8 => [.refs [(CallArguments.arrayStoreField, [6])] [] []]
  | 9 => [.refs [(CallArguments.arrayStoreField, [5])] [] []]
  | 10 => [.arrs [⟨[12], [[0], [0]], [0], .unrestricted⟩] []]
  | 11 => [.arrs [] [⟨[12], ([[0, 1]], [14]), [0], .unrestricted⟩]]
  | 12 => [.top]
  | 13 => [.pack ⟨[], [], some [0,1], false, true⟩ []]
  | 14 => [.pack ⟨[], [], some [0], false, true⟩ []]
  | 15 => [.pack ⟨[[0], [0]], [], none, false, true⟩ []]
  | 16 => [.arrs [] [⟨[12], ([], [15]), [0], .unrestricted⟩]]
  | 17 => [.list ⟨[[0], [0]], [], none, false, true⟩ []]
  | 18 => [.refs [(CallArguments.arrayStoreField, [17])] [] []]
  | 19 => [.arrs [] [⟨[12], ([], [15]), [18], .unrestricted⟩]]
  | 20 => [.arrs [] [⟨[12], ([], [14]), [18], .unrestricted⟩]]
  | 21 => [.pack ⟨[[0]], [], none, false, true⟩ []]
  | 22 => [.arrs [] [⟨[12], ([[0]], [21]), [0], .unrestricted⟩]]
  | _ => []

def pool : List (Ty Nat) := vocabulary G (List.range 23) [] [[0,1]]

/-- Graph code collecting a rest: its one node returns slot 2, the fixed
parameter; slot 0 is the store the call collected, slot 1 the receiver. -/
def restCode (slot : Nat) : Tm := .make (.graph 1 [.var slot] [(.ret, none)] 0 [] .call true) .nul

/-- Creation evidence, every code admitted: whether the code is checked at its
signatures is the unit's code table's question, not the creation's. -/
def created (t : Tm) (A : Ty Nat) : Bool :=
  match expression G pool 40 [] t A with
  | some e => checkTree G e (fun _ => true) && claim e == ⟨[], t, A⟩
  | none => false

-- Creation at a signature whose rest collects `number | undefined`, the store
-- of each signature at a pool type that is its rest store; not at a fixed
-- signature, which code collecting a rest does not offer.
#guard created (restCode 2) [4]
#guard created (restCode 2) [7]
#guard !created (restCode 2) [10]
-- Code without a rest offers a variadic signature too, discarding the rest.
#guard created (.make (.graph 1 [.var 1] [(.ret, none)] 0 []) .nul) [4]

/-- Against `...r: number[]`, in a context holding such a function and an
array: plain actuals and spreads are accepted, since these stores are dense and
a spread passes only its elements. -/
def searchIn (Γ : List (Ty Nat)) (t : Tm) : Bool :=
  match expression G pool 40 Γ t [0] with
  | some e => checkTree G e && claim e == ⟨Γ, t, [0]⟩
  | none => false

def spreadAt (i : Nat) : Tm := .spread (.readAt CallArguments.arrayStoreField (.var i))

-- Fixed actual only, several plain actuals, and a spread among them.
#guard searchIn [[4]] (.call (.var 0) [.num 1])
#guard searchIn [[4]] (.call (.var 0) [.num 1, .num 2, .undef])
#guard searchIn [[4], [3]] (.call (.var 0) [.num 1, spreadAt 1, .num 2])
#guard searchIn [[4], [3]] (.call (.var 0) [.num 1, spreadAt 1, spreadAt 1])
-- The fixed parameter cannot be supplied by a spread, nor omitted.
#guard !searchIn [[4], [3]] (.call (.var 0) [spreadAt 1])
#guard !searchIn [[4]] (.call (.var 0) [])
-- An element outside the element type is refused.
#guard !searchIn [[4]] (.call (.var 0) [.num 1, .nul])

#guard searchIn [[7],[8]] (.call (.var 0) [.num 1, .num 2])
#guard searchIn [[7],[8]] (.call (.var 0) [.num 1, spreadAt 1])
#guard searchIn [[7],[9]] (.call (.var 0) [.num 1, spreadAt 1])
#guard searchIn [[4],[8]] (.call (.var 0) [.num 1, spreadAt 1])

-- A variadic value meets a fixed signature whose positions it admits, and a
-- call through that fixed type is a call it already supports.
#guard (subtype G pool [7] [10]).isSome
#guard searchIn [[10]] (.call (.var 0) [.num 1, .num 2])
#guard searchIn [[7]] (.call (.var 0) [.num 1, .num 2])
-- A fixed signature does not meet a variadic one with an element rest: it
-- promises nothing past its own positions. It meets one whose rest is exactly
-- its further positions, when those are stable, as a number is.
#guard !(subtype G pool [10] [7]).isSome
#guard (subtype G pool [10] [16]).isSome
#guard (subtype G pool [10] [22]).isSome
#guard searchIn [[22]] (.call (.var 0) [.num 1, .num 2])
-- An optional fixed parameter before the rest may be omitted: the call binds
-- `undefined` there and collects nothing.
#guard searchIn [[11]] (.call (.var 0) [])
#guard searchIn [[11]] (.call (.var 0) [.num 1, .num 2])
-- A required one may not.
#guard !searchIn [[7]] (.call (.var 0) [])

-- Forged evidence: a `callRest` node that claims a spread where the term has a
-- plain actual, or the wrong element type, is refused by the checker.
private def restCallEvidence (flags : List Bool) (E : Ty Nat) : Evidence Nat :=
  .node ⟨[[4]], .call (.var 0) [.num 1, .num 2], [0]⟩ (.callRest .unrestricted 1 0 flags E)
    [.node ⟨[[4]], .var 0, [4]⟩ .var [],
     .node ⟨[[4]], .undef, [12]⟩ (.sub (.core ⟨[([1], [12])], []⟩))
       [.node ⟨[[4]], .undef, [1]⟩ .undef []],
     .node ⟨[[4]], .num 1, [0]⟩ .num [],
     .node ⟨[[4]], .num 2, [0,1]⟩ (.sub .subset) [.node ⟨[[4]], .num 2, [0]⟩ .num []]]
#guard checkTree G (restCallEvidence [false] [13])
#guard !checkTree G (restCallEvidence [true] [13])
#guard !checkTree G (restCallEvidence [false] [14])
#guard !checkTree G (restCallEvidence [] [13])

-- A call writes exactly the tuple's positions: not fewer, not more, and no
-- spread, whose length the tuple cannot bound.
#guard searchIn [[16]] (.call (.var 0) [.num 1, .num 2])
#guard !searchIn [[16]] (.call (.var 0) [.num 1])
#guard !searchIn [[16]] (.call (.var 0) [.num 1, .num 2, .num 3])
#guard !searchIn [[16], [18]] (.call (.var 0) [spreadAt 1])
#guard !searchIn [[16]] (.call (.var 0) [.num 1, .nul])

end Verification.Model.RestCallsTests
