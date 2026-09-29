import Verification.Model.Programs.CertificateProducer
import Verification.Model.Tests.ControlFlowTests

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Verification.Model.CertificateProducerTests
open ProgramTyping ProgramTypingTests ControlFlow CertificateProducer

/-- A finite graph's labels have no syntax to substitute into. -/
instance : Instantiates (Fin n) := ⟨fun _ _ _ => none⟩

def labels : List (Fin 7) := [0,1,2,3,4,5,6]

def loopClaims : List (PointClaim (Fin 7)) :=
  [⟨[],[2]⟩, ⟨[[2]],[3]⟩, ⟨[[3],[2]],[1]⟩,
   ⟨[[3],[2]],[0]⟩, ⟨[[3],[2]],[1]⟩]

def diamondClaims : List (PointClaim (Fin 7)) :=
  [⟨[],[1]⟩, ⟨[],[0]⟩, ⟨[],[1]⟩, ⟨[[0,1]],[0,1]⟩]

def succeeds (r : Except Failure α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

/-- Every code admitted: whether a code meets its signatures is its table's
question, not its creation's. -/
def admitted : CodeEntry (Fin 7) → Bool := fun _ => true

#guard succeeds (produce G labels 8 [1] ControlFlowTests.loop loopClaims 0 (codes := admitted))
#guard succeeds (produce G labels 8 [0,1] ControlFlowTests.diamond diamondClaims 0)

/-- Extracted-shaped binding changes: retain an alias, insert a local, permute
slots, exit its scope, then write through an alias and call the captured closure.
Maps describe simultaneous selection from the pre-transfer environment. -/
def mapped : Program :=
  [⟨.alloc .tru, .bind ⟨1, some [0,0]⟩,none⟩,
   ⟨.nul, .bind ⟨2, some [2,0,1]⟩,none⟩,
   ⟨.make ControlFlowTests.dispatchCode .nul, .bind ⟨3, some [0,3,1]⟩,none⟩,
   ⟨.write (.var 1) .fls, .effect ⟨4, some [0,2]⟩,none⟩,
   ⟨.app (.var 0) .nul, .ret,none⟩]

def mappedClaims : List (PointClaim (Fin 7)) :=
  [⟨[],[2]⟩, ⟨[[2],[2]],[0]⟩, ⟨[[2],[0],[2]],[3]⟩,
   ⟨[[3],[2],[2]],[0]⟩, ⟨[[3],[2]],[1]⟩]

#guard succeeds (produce G labels 8 [1] mapped mappedClaims 0 (codes := admitted))
-- The creation names code the table must hold.
#guard !succeeds (produce G labels 8 [1] mapped mappedClaims 0)

/-- Shared generated evidence for executable tampering checks. -/
def mappedCertificate : ControlFlow.Certificate (Fin 7) :=
  match produce G labels 8 [1] mapped mappedClaims 0 (codes := admitted) with
  | .ok C => C
  | .error _ => []

-- Structural subtype search must build a union-of-domains arrow certificate.
#guard (subtype G [3] [4]).isSome
#guard !(subtype G [2] [1]).isSome

/-- Both branch targets independently select their input slots. -/
def mappedDiamond : Program :=
  [⟨.nul, .bind 1,none⟩, ⟨.tru, .bind 2,none⟩,
   ⟨.tru, .branch ⟨3, some [1,0]⟩ ⟨4, some [0,1]⟩,none⟩,
   ⟨.var 0, .bind ⟨5, some [0]⟩,none⟩,
   ⟨.var 0, .bind ⟨5, some [0]⟩,none⟩, ⟨.var 0, .ret,none⟩]
def mappedDiamondClaims : List (PointClaim (Fin 7)) :=
  [⟨[],[0]⟩, ⟨[[0]],[1]⟩, ⟨[[1],[0]],[1]⟩,
   ⟨[[0],[1]],[0]⟩, ⟨[[1],[0]],[1]⟩, ⟨[[0,1]],[0,1]⟩]
#guard succeeds (produce G labels 8 [0,1] mappedDiamond mappedDiamondClaims 0)
#guard !(succeeds (produce G labels 8 [0,1]
  (mappedDiamond.set 2 ⟨.tru, .branch ⟨3, some [1,0]⟩ ⟨4, some [1,0]⟩,none⟩)
  mappedDiamondClaims 0))

-- Ordinary nested lets and calls through a widened overload also require no
-- evidence hints.
#guard succeeds (produce G labels 12 [0,1] [⟨programBody,.ret,none⟩] [⟨[[3]],[0,1]⟩] 0 (inputs := [[3]]))
-- Recursive references: the generated cyclic table closes through invariance.
def recursiveG : PositiveGraphs.NormalGraph (Fin 3) := .ofRows fun i =>
  match i.val with | 0 => [.refs [(valueField, [0])] [] []] | 1 => [.refs [(valueField, [1])] [] []] | _ => [.bool]
#guard (subtype recursiveG [0] [1]).isSome
#guard !(subtype recursiveG [0] [2]).isSome

-- Bad claims, including an unreachable boolean predecessor, cannot be repaired.
#guard !(succeeds (produce G labels 8 [0] ControlFlowTests.diamond
  (diamondClaims.set 3 ⟨[[0]],[0]⟩) 0))
#guard !(succeeds (produce G labels 8 [1] mapped
  (mappedClaims.set 3 ⟨[[3],[1],[2]],[0]⟩) 0 (codes := admitted)))
#guard !(succeeds (produce G labels 8 [1] mapped mappedClaims.tail 0 (codes := admitted)))
#guard !(succeeds (produce G labels 8 [1] mapped mappedClaims 99 (codes := admitted)))
#guard !(succeeds (produce G labels 0 [1] mapped mappedClaims 0 (codes := admitted)))
-- The unchanged program is accepted with its certificate.
#guard accept G [1] mapped mappedClaims mappedCertificate 0 [] admitted
-- A map is not a certificate hint: changed maps are rechecked against the code.
#guard !(accept G [1] (mapped.set 1 ⟨.nul, .bind ⟨2, some [0,2,1]⟩,none⟩)
  mappedClaims mappedCertificate 0 [] admitted)
#guard !(accept G [1] (mapped.set 0 ⟨.alloc .tru, .bind ⟨1, some [0,99]⟩,none⟩)
  mappedClaims mappedCertificate 0 [] admitted)
#guard !(accept G [1] (mapped.set 0 ⟨.alloc .tru, .bind ⟨1, some [0]⟩,none⟩)
  mappedClaims mappedCertificate 0 [] admitted)
#guard !(accept G [1] (mapped.set 0 ⟨.alloc .tru, .bind ⟨1, some [0,0,0]⟩,none⟩)
  mappedClaims mappedCertificate 0 [] admitted)
-- A perfectly valid certificate for a different set of claims is rejected.
#guard !(accept G [1] mapped (mappedClaims.set 4 ⟨[[3],[2]],[0,1]⟩) mappedCertificate 0 [] admitted)

-- Exact evidence counts apply to explicit maps, too.
#guard !(accept G [1] mapped mappedClaims
  (mappedCertificate.map fun c => {c with edges := c.edges.map List.tail}) 0 [] admitted)
#guard !(accept G [1] mapped mappedClaims
  (mappedCertificate.map fun c => {c with edges := c.edges.map (fun ps => ps ++ [.subset])}) 0 [] admitted)

end Verification.Model.CertificateProducerTests
