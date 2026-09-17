import Verification.ExperimentState.CertificateProducer
import Verification.ExperimentState.ControlFlowTests

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Verification.ExperimentState.CertificateProducerTests
open ProgramTyping ProgramTypingTests ControlFlow CertificateProducer

def labels : List (Fin 6) := [0,1,2,3,4,5]

def loopClaims : List (PointClaim (Fin 6)) :=
  [⟨[],[2]⟩, ⟨[[2]],[3]⟩, ⟨[[3],[2]],[1]⟩,
   ⟨[[3],[2]],[0]⟩, ⟨[[3],[2]],[1]⟩]

def diamondClaims : List (PointClaim (Fin 6)) :=
  [⟨[],[1]⟩, ⟨[],[0]⟩, ⟨[],[1]⟩, ⟨[[0,1]],[0,1]⟩]

def succeeds (r : Except Failure α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

#guard succeeds (produce G labels 8 [1] ControlFlowTests.loop loopClaims 0)
#guard succeeds (produce G labels 8 [0,1] ControlFlowTests.diamond diamondClaims 0)

/-- Extracted-shaped binding changes: retain an alias, insert a local, permute
slots, exit its scope, then write through an alias and call the captured closure.
Maps describe simultaneous selection from the pre-transfer environment. -/
def mapped : Program :=
  [⟨.alloc .tru, .bind ⟨1, some [0,0]⟩⟩,
   ⟨.nul, .bind ⟨2, some [2,0,1]⟩⟩,
   ⟨dispatch, .bind ⟨3, some [0,3,1]⟩⟩,
   ⟨.write (.var 1) .fls, .effect ⟨4, some [0,2]⟩⟩,
   ⟨.app (.var 0) .nul, .ret⟩]

def mappedClaims : List (PointClaim (Fin 6)) :=
  [⟨[],[2]⟩, ⟨[[2],[2]],[0]⟩, ⟨[[2],[0],[2]],[3]⟩,
   ⟨[[3],[2],[2]],[0]⟩, ⟨[[3],[2]],[1]⟩]

#guard succeeds (produce G labels 8 [1] mapped mappedClaims 0)

/-- No hand-built evidence tree or per-program typing derivation. Kernel
reduction checks the produced certificate, then the general theorem applies. -/
def mappedCertificate : ControlFlow.Certificate (Fin 6) :=
  match produce G labels 8 [1] mapped mappedClaims 0 with
  | .ok C => C
  | .error _ => []

theorem mapped_accepted : accept G [1] mapped mappedClaims mappedCertificate 0 = true := by cbv

theorem mapped_safe (n : Nat) : SafeGraph mapped (PositiveRules.meaning G [1]) n
    (ofList []) [] (.at 0 (fun _ => .nul)) := accepted_safe mapped_accepted n

theorem mapped_returns_false : Execution mapped 17 [] (.at 0 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.makeV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.makeV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.writeV rfl (by decide)))
  apply Execution.next (.effect rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.beta rfl))
  apply Execution.next (.expr (.iteC (.testV rfl)))
  apply Execution.next (.expr .iteT)
  apply Execution.next (.expr (.readV rfl))
  apply Execution.next (.ret rfl)
  exact .refl

-- Structural subtype search must build a union-of-domains arrow certificate.
#guard (subtype G [[],[0],[1],[0,1],[2],[3],[4],[5]] [3] [4]).isSome
#guard !(subtype G [[],[0],[1],[0,1],[2],[3],[4],[5]] [2] [1]).isSome

/-- Both branch targets independently select their input slots. -/
def mappedDiamond : Program :=
  [⟨.nul, .bind 1⟩, ⟨.tru, .bind 2⟩,
   ⟨.tru, .branch ⟨3, some [1,0]⟩ ⟨4, some [0,1]⟩⟩,
   ⟨.var 0, .bind ⟨5, some [0]⟩⟩,
   ⟨.var 0, .bind ⟨5, some [0]⟩⟩, ⟨.var 0, .ret⟩]
def mappedDiamondClaims : List (PointClaim (Fin 6)) :=
  [⟨[],[0]⟩, ⟨[[0]],[1]⟩, ⟨[[1],[0]],[1]⟩,
   ⟨[[0],[1]],[0]⟩, ⟨[[1],[0]],[1]⟩, ⟨[[0,1]],[0,1]⟩]
#guard succeeds (produce G labels 8 [0,1] mappedDiamond mappedDiamondClaims 0)
#guard !(succeeds (produce G labels 8 [0,1]
  (mappedDiamond.set 2 ⟨.tru, .branch ⟨3, some [1,0]⟩ ⟨4, some [1,0]⟩⟩)
  mappedDiamondClaims 0))

-- Ordinary nested lets and overload bodies also require no evidence hints.
#guard succeeds (produce G labels 12 [0,1] [⟨program,.ret⟩] [⟨[],[0,1]⟩] 0)
-- Recursive references: the generated cyclic table closes through invariance.
def recursiveG : PositiveGraphs.NormalGraph (Fin 3) := fun i =>
  match i.val with | 0 => [.refs [(valueField, [0])] [] []] | 1 => [.refs [(valueField, [1])] [] []] | _ => [.bool]
#guard (subtype recursiveG [[],[0],[1],[2]] [0] [1]).isSome
#guard !(subtype recursiveG [[],[0],[1],[2]] [0] [2]).isSome

-- Bad claims, including an unreachable boolean predecessor, cannot be repaired.
#guard !(succeeds (produce G labels 8 [0] ControlFlowTests.diamond
  (diamondClaims.set 3 ⟨[[0]],[0]⟩) 0))
#guard !(succeeds (produce G labels 8 [1] mapped
  (mappedClaims.set 3 ⟨[[3],[1],[2]],[0]⟩) 0))
#guard !(succeeds (produce G labels 8 [1] mapped mappedClaims.tail 0))
#guard !(succeeds (produce G labels 8 [1] mapped mappedClaims 99))
#guard !(succeeds (produce G labels 0 [1] mapped mappedClaims 0))
-- A map is not a certificate hint: changed maps are rechecked against the code.
#guard !(accept G [1] (mapped.set 1 ⟨.nul, .bind ⟨2, some [0,2,1]⟩⟩)
  mappedClaims mappedCertificate 0)
#guard !(accept G [1] (mapped.set 0 ⟨.alloc .tru, .bind ⟨1, some [0,99]⟩⟩)
  mappedClaims mappedCertificate 0)
#guard !(accept G [1] (mapped.set 0 ⟨.alloc .tru, .bind ⟨1, some [0]⟩⟩)
  mappedClaims mappedCertificate 0)
#guard !(accept G [1] (mapped.set 0 ⟨.alloc .tru, .bind ⟨1, some [0,0,0]⟩⟩)
  mappedClaims mappedCertificate 0)
-- A perfectly valid certificate for a different set of claims is rejected.
#guard !(accept G [1] mapped (mappedClaims.set 4 ⟨[[3],[2]],[0,1]⟩) mappedCertificate 0)

-- Exact evidence counts apply to explicit maps, too.
#guard !(accept G [1] mapped mappedClaims
  (mappedCertificate.map fun c => {c with edges := c.edges.map List.tail}) 0)
#guard !(accept G [1] mapped mappedClaims
  (mappedCertificate.map fun c => {c with edges := c.edges.map (fun ps => ps ++ [.subset])}) 0)

#print axioms mapped_safe
#print axioms mapped_returns_false
end Verification.ExperimentState.CertificateProducerTests
