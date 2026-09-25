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
  | 2 => [.list ⟨[], [], some [0,1], false⟩ []]
  | 3 => [.refs [(CallArguments.arrayStoreField, [2])] [] []]
  | 4 => [.arrs [] [([12], [[0]], [13], [0])]]
  | 5 => [.list ⟨[[0]], [], none, false⟩ []]
  | 6 => [.list ⟨[], [], some [0], false⟩ []]
  | 7 => [.arrs [] [([12], [[0]], [14], [0])]]
  | 8 => [.refs [(CallArguments.arrayStoreField, [6])] [] []]
  | 9 => [.refs [(CallArguments.arrayStoreField, [5])] [] []]
  | 10 => [.arrs [([12], [[0], [0]], [0])] []]
  | 11 => [.arrs [] [([12], [[0, 1]], [14], [0])]]
  | 12 => [.top]
  | 13 => [.pack ⟨[], [], some [0,1], false⟩ []]
  | 14 => [.pack ⟨[], [], some [0], false⟩ []]
  | 15 => [.pack ⟨[[0], [0]], [], none, false⟩ []]
  | 16 => [.arrs [] [([12], [], [15], [0])]]
  | 17 => [.list ⟨[[0], [0]], [], none, false⟩ []]
  | 18 => [.refs [(CallArguments.arrayStoreField, [17])] [] []]
  | 19 => [.arrs [] [([12], [], [15], [18])]]
  | 20 => [.arrs [] [([12], [], [14], [18])]]
  | 21 => [.pack ⟨[[0]], [], none, false⟩ []]
  | 22 => [.arrs [] [([12], [[0]], [21], [0])]]
  | _ => []

def pool : List (Ty Nat) := vocabulary G (List.range 23) [] [[0,1]]

/-- Slot 0 is the collected store, slot 1 the receiver, slot 2 the fixed
parameter. -/
def restFn : Tm := .make (.variadic 1 (.var 2)) .nul

/-- Build an array of the given store type, then call with actuals `args`,
where slot 0 is the array and slot 1 the function. -/
def program (store : List Tm) (args : List Tm) : Tm :=
  .letE restFn (.letE (.makeAt .absent [CallArguments.arrayStoreField] [.arrLit store])
    (.call (.var 1) args))

def spreadArray : Tm := .spread (.readAt CallArguments.arrayStoreField (.var 0))

def search (t : Tm) (A : Ty Nat) : Option (Evidence Nat) := expression G pool 40 [] t A

def accepted (t : Tm) (A : Ty Nat) : Bool :=
  match search t A with
  | some e => check G t A e
  | none => false

-- Creation alone, at a signature whose rest collects `number | undefined`.
#guard accepted restFn [4]
-- The body reads slot 2, the fixed parameter; slot 0 is the array.
#guard !accepted (.make (.variadic 1 (.var 0)) .nul) [4]
-- Slot 1 is the receiver, which may be any value: not a number.
#guard !accepted (.make (.variadic 1 (.var 1)) .nul) [4]
-- Fixed actual only, several plain actuals, and a spread among them.
#guard accepted (.letE restFn (.call (.var 0) [.num 1])) [0]
#guard accepted (.letE restFn (.call (.var 0) [.num 1, .num 2, .undef])) [0]
#guard accepted (program [.num 3] [.num 1, spreadArray, .num 2]) [0]
#guard accepted (program [.num 3] [.num 1, spreadArray, spreadArray]) [0]
-- The fixed parameter cannot be supplied by a spread, nor omitted.
#guard !accepted (program [.num 3] [spreadArray]) [0]
#guard !accepted (.letE restFn (.call (.var 0) [])) [0]
-- An element outside the element type is refused.
#guard !accepted (.letE restFn (.call (.var 0) [.num 1, .nul])) [0]

/-- Against `...r: number[]`, in a context holding such a function and an
array: a spread of a store that may have a hole would pass `undefined`, so it
is refused; plain actuals and a spread of a dense tuple are not. -/
def searchIn (Γ : List (Ty Nat)) (t : Tm) : Bool :=
  match expression G pool 40 Γ t [0] with
  | some e => checkTree G e && claim e == ⟨Γ, t, [0]⟩
  | none => false

def spreadAt (i : Nat) : Tm := .spread (.readAt CallArguments.arrayStoreField (.var i))

#guard searchIn [[7],[8]] (.call (.var 0) [.num 1, .num 2])
#guard !searchIn [[7],[8]] (.call (.var 0) [.num 1, spreadAt 1])
#guard searchIn [[7],[9]] (.call (.var 0) [.num 1, spreadAt 1])
#guard searchIn [[4],[8]] (.call (.var 0) [.num 1, spreadAt 1])

-- A variadic value meets a fixed signature whose positions it admits, and a
-- call through that fixed type is a call it already supports.
#guard (subtype G pool [7] [10]).isSome
#guard searchIn [[10]] (.call (.var 0) [.num 1, .num 2])
#guard (expression G pool 40 [] (.letE restFn (.call (.var 0) [.num 1, .num 2])) [0]).isSome
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
  .node ⟨[[4]], .call (.var 0) [.num 1, .num 2], [0]⟩ (.callRest 1 0 flags E)
    [.node ⟨[[4]], .var 0, [4]⟩ .var [],
     .node ⟨[[4]], .undef, [12]⟩ (.sub (.core ⟨[([1], [12])], []⟩))
       [.node ⟨[[4]], .undef, [1]⟩ .undef []],
     .node ⟨[[4]], .num 1, [0]⟩ .num [],
     .node ⟨[[4]], .num 2, [0,1]⟩ (.sub .subset) [.node ⟨[[4]], .num 2, [0]⟩ .num []]]
#guard checkTree G (restCallEvidence [false] [13])
#guard !checkTree G (restCallEvidence [true] [13])
#guard !checkTree G (restCallEvidence [false] [14])
#guard !checkTree G (restCallEvidence [] [13])

/-- Variadic code wrapping its rest store into an array and returning it. -/
def tupleFn : Tm :=
  .make (.variadic 0 (.letE (.makeAt .absent [CallArguments.arrayStoreField] [.var 0]) (.var 0))) .nul

-- The rest store holds a tuple rest's positions; an element rest's store holds
-- any number of actuals, so it is no pair.
#guard accepted tupleFn [19]
#guard !accepted tupleFn [20]
-- A call writes exactly the tuple's positions: not fewer, not more, and no
-- spread, whose length the tuple cannot bound.
#guard searchIn [[16]] (.call (.var 0) [.num 1, .num 2])
#guard !searchIn [[16]] (.call (.var 0) [.num 1])
#guard !searchIn [[16]] (.call (.var 0) [.num 1, .num 2, .num 3])
#guard !searchIn [[16], [18]] (.call (.var 0) [spreadAt 1])
#guard !searchIn [[16]] (.call (.var 0) [.num 1, .nul])

end Verification.Model.RestCallsTests
