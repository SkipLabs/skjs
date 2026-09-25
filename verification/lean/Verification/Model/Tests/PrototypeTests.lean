import Verification.Model.Programs.CertificateProducer

/-! Reads through the prototype: a key outside the object's own-key bound is
read from the prototype the object holds under the reserved key. Without a
bound, or with a bound that admits the key, the object may have its own field
of that name, and the read is refused. -/
namespace Verification.Model.PrototypeTests
open ProgramTyping ProgramCertificates CertificateProducer PositiveNormalization

/-- 0 number, 1 undefined, 2 a store of numbers, 3 unknown, 4 `() => number`,
5 a prototype with a `map` view at 4, 6 an array bounded to its store and
prototype keys, 7 the same array unbounded, 8 an array whose bound admits
`map`. -/
def G : PositiveGraphs.NormalGraph Nat := .ofRows fun
  | 0 => [.num]
  | 1 => [.undef]
  | 2 => [.list ⟨[], [], some [0], false⟩ []]
  | 3 => [.top]
  | 4 => [.arrs [([3], [], [0])] []]
  | 5 => [.refs [] [] [("map", [4])]]
  | 6 => [.refs [(CallArguments.arrayStoreField, [2])] [] [(CallArguments.protoField, [5])] [] []
      [[CallArguments.arrayStoreField, CallArguments.protoField]]]
  | 7 => [.refs [(CallArguments.arrayStoreField, [2])] [] [(CallArguments.protoField, [5])]]
  | 8 => [.refs [(CallArguments.arrayStoreField, [2])] [] [(CallArguments.protoField, [5])] [] []
      [[CallArguments.arrayStoreField, CallArguments.protoField, "map"]]]
  | _ => []

def pool : List (Ty Nat) := vocabulary G (List.range 9) [] []

/-- Searched by the producer and accepted by the checker. -/
def accepted (Γ : List (Ty Nat)) (t : Tm) (A : Ty Nat) : Bool :=
  match expression G pool 20 Γ t A with
  | some e => checkTree G e && claim e == ⟨Γ, t, A⟩
  | none => false

def readMap : Tm := .readAt "map" (.var 0)

-- The bounded array reads `map` from its prototype, and its store as its own.
#guard accepted [[6]] readMap [4]
#guard accepted [[6]] (.readAt CallArguments.arrayStoreField (.var 0)) [2]
-- Unbounded, or bounded so as to admit `map`, the object may hold its own `map`.
#guard !accepted [[7]] readMap [4]
#guard !accepted [[8]] readMap [4]

/-- Evidence naming the prototype read directly. -/
def protoEvidence (Ref : Ty Nat) : Evidence Nat :=
  .node ⟨[Ref], readMap, [4]⟩ (.readProto [5]) [.node ⟨[Ref], .var 0, Ref⟩ .var []]

#guard checkTree G (protoEvidence [6])
#guard !checkTree G (protoEvidence [7])
#guard !checkTree G (protoEvidence [8])

end Verification.Model.PrototypeTests
