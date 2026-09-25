import Verification.Model.Programs.CertificateProducer

/-! An own-key bound excluding an optional field's key and the prototype key
covers the field: the object lacks the key and has no prototype. No source form
states such a bound yet (a fresh object literal's exact keys would); retire this
once a pipeline case covers it. -/
namespace Verification.Model.OptionalBoundTests
open PositiveNormalization PositiveGraphs CertificateProducer

private def a : PropKey := .str "a"
private def b : PropKey := .str "b"
def types : List (List (Clause (List Nat))) :=
  [[.num],
   -- Own keys among `a`: no `b`, no prototype.
   [.refs [(a, [0])] [] [] [] [] [[a]]],
   -- An optional `b`, writable and readonly.
   [.refs [] [] [] [⟨b, false, [0]⟩]],
   [.refs [] [] [] [⟨b, true, [0]⟩]],
   -- A bound admitting `b`, or the prototype, says nothing of either.
   [.refs [(a, [0])] [] [] [] [] [[a, b]]],
   [.refs [(a, [0])] [] [] [] [] [[a, CallArguments.protoField]]],
   -- Unbounded: open, so `b` may be present at any type.
   [.refs [(a, [0])] [] []]]
def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def pool : List (List Nat) := (List.range types.length).map fun i => [i]

#guard (subtype G pool [1] [2]).isSome
#guard (subtype G pool [1] [3]).isSome
#guard !(subtype G pool [4] [2]).isSome
#guard !(subtype G pool [5] [3]).isSome
#guard !(subtype G pool [6] [3]).isSome

end Verification.Model.OptionalBoundTests
