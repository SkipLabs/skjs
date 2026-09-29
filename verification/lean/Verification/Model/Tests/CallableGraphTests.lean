import Verification.Model.Source.RequestJson
import Verification.Model.Programs.DirectProof
import Verification.Model.Semantics.GraphCoherence

/-! The callable fixtures the callable tests share: an overloaded callable
with a mutable bag field, its code, and a program allocating and using it. -/
namespace Verification.Model.CallableGraphTests
open Lean PositiveNormalization PositiveGraphs ProgramTyping ControlFlow CertificateProducer RequestJson

/-- Every signature here takes any receiver: label 7 is unknown, and label 8
`undefined`, the receiver a plain call passes. -/
def signatures : List (CallEffects.Arrow (List Nat)) :=
  [⟨[7],[[1]],[1],.unrestricted⟩,⟨[7],[[0]],[0],.unrestricted⟩]
def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.callable [(valueField, [1])] [] signatures []],[.arrs signatures []],
   [.callable [(valueField, [1])] [[(valueField,[1])]] signatures []],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [0,1])] [] signatures []],
   [.top],[.undef]]
def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
def labels := List.range types.length

/-- The callable's code: one node returning its parameter, frame slot 1, past
the receiver. -/
def code : CallCode := .graph 1 [.var 1] [(.ret, none)] 0 []
def program : Program :=
  [⟨.makeAt code [valueField] [.tru],.bind 1,none⟩,
   ⟨.var 0,.bind 2,none⟩,
   ⟨.write (.var 1) .fls,.effect 3,none⟩,
   ⟨.read (.var 0),.bind 4,none⟩,
   ⟨.app (.var 1) (.var 0),.ret,none⟩]
def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[2]⟩,⟨[[2],[2]],[0]⟩,⟨[[2],[2]],[1]⟩,⟨[[1],[2],[2]],[1]⟩]

end Verification.Model.CallableGraphTests
