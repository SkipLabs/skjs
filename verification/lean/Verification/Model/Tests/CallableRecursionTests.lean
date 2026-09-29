import Verification.Model.Tests.CallableGraphTests
import Verification.Model.Tests.GraphCodeFixtures

/-! A recursive invocation is tied through an allocated cell, rather than a
runtime identity embedded in source syntax. The code is checked once for the
calls it makes to itself; safety permits the infinite run. -/
namespace Verification.Model.CallableRecursionTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ControlFlow
open CertificateProducer RequestJson ProgramCertificates GraphCodeFixtures

private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.arrs [⟨[3], [[0]], [0], .unrestricted⟩] []], [.refs [(valueField, [0,1])] [] []], [.undef]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length
private def dispatch : Tm := .ite (.test .isFun (.var 0)) (.app (.var 0) .nul) .nul
/-- The body reads the captured cell, past its parameter and receiver. -/
private def body : Tm := .letE (.read (.var 2)) dispatch
private def program (body : Tm) : Program :=
  [⟨.alloc .nul,.bind 1,none⟩,
   ⟨.make (oneNode 1 body 1) .nul,.bind 2,none⟩,
   ⟨.write (.var 1) (.var 0),.effect 3,none⟩,
   ⟨.app (.var 0) .nul,.ret,none⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[1]⟩,⟨[[1],[2]],[0]⟩,⟨[[1],[2]],[0]⟩]
private def request (body : Tm) : Request RequestJson.Table Nat :=
  ⟨types,program body,claims,[0],0,[],oneNodeCodes 1 body [[2]] [⟨[3], [[0]], [0], .unrestricted⟩]⟩
#guard ok (roundtrip (request body))

-- The nullable cell must be guarded on every invocation, and the recursive
-- call's argument must satisfy its contract. Current contents are not captures.
#guard !ok (roundtrip (request (.app (.read (.var 2)) .nul)))
#guard !ok (roundtrip (request (.letE (.read (.var 2))
  (.ite (.test .isFun (.var 0)) (.app (.var 0) .tru) .nul))))

end Verification.Model.CallableRecursionTests
