import Verification.ExperimentState.CertificateProducer

/-! Variadic creation and calls, with and without spreads, searched by the
producer and accepted by the checker; and the spreads the checker refuses. -/
namespace Verification.ExperimentState.RestCallsTests
open ProgramTyping ProgramCertificates CertificateProducer PositiveNormalization

/-- 0 number, 1 undefined, 2 a store of `number | undefined` of any length,
3 its array, 4 `(a: number, ...r: (number | undefined)[]) => number`,
5 the store of a `[number]` tuple, 6 a store of `number` of any length,
7 `(a: number, ...r: number[]) => number`, 8 the array of 6, 9 the array of 5,
10 `(a: number, b: number) => number`, 11 `(a?: number, ...r: number[]) => number`. -/
def G : PositiveGraphs.NormalGraph Nat
  | 0 => [.num]
  | 1 => [.undef]
  | 2 => [.list ⟨[], [], some [0,1], false⟩ []]
  | 3 => [.refs [(CallArguments.arrayStoreField, [2])] [] []]
  | 4 => [.arrs [] [([[0]], [0,1], [0])]]
  | 5 => [.list ⟨[[0]], [], none, false⟩ []]
  | 6 => [.list ⟨[], [], some [0], false⟩ []]
  | 7 => [.arrs [] [([[0]], [0], [0])]]
  | 8 => [.refs [(CallArguments.arrayStoreField, [6])] [] []]
  | 9 => [.refs [(CallArguments.arrayStoreField, [5])] [] []]
  | 10 => [.arrs [([[0], [0]], [0])] []]
  | 11 => [.arrs [] [([[0, 1]], [0], [0])]]
  | _ => []

def pool : List (Ty Nat) := vocabulary G (List.range 12) [] [[0,1]]

def restFn : Tm := .make (.variadic 1 (.var 1)) .nul

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
-- The body reads slot 1, the fixed parameter; slot 0 is the array.
#guard !accepted (.make (.variadic 1 (.var 0)) .nul) [4]
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
-- A fixed signature does not meet a variadic one: it promises nothing past
-- its own positions.
#guard !(subtype G pool [10] [7]).isSome
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
     .node ⟨[[4]], .num 1, [0]⟩ .num [],
     .node ⟨[[4]], .num 2, [0,1]⟩ (.sub .subset) [.node ⟨[[4]], .num 2, [0]⟩ .num []]]
#guard checkTree G (restCallEvidence [false] [0,1])
#guard !checkTree G (restCallEvidence [true] [0,1])
#guard !checkTree G (restCallEvidence [false] [0])
#guard !checkTree G (restCallEvidence [] [0,1])

end Verification.ExperimentState.RestCallsTests
