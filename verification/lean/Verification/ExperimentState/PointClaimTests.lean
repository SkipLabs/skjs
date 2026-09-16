import Verification.ExperimentState.PointClaims
import Verification.ExperimentState.ProgramTypingTests

namespace Verification.ExperimentState.PointClaimTests
open ProgramTyping ProgramTypingTests ProgramCertificates PointClaims

-- A supplied merge type is justified from both predecessors, independently.
#guard checkIncoming G [[0,1],[2]]
  [([[0],[2]], [.subset,.subset]), ([[1],[2]], [.subset,.subset])]
#guard !(checkIncoming G [[0],[2]]
  [([[0],[2]], [.subset,.subset]), ([[1],[2]], [.subset,.subset])])
-- Forgetting a suffix is sound; inventing or reordering slots is not.
#guard checkEdge G [[0],[2]] [[0,1]] [.subset]
#guard !(checkEdge G [[0]] [[0],[2]] [.subset,.subset])
#guard !(checkEdge G [[0],[2]] [[2],[0]] [.subset,.subset])
#guard !(checkEdge G [[0]] [[0]] [])
#guard !(checkEdge G [[0]] [] [.subset])

def writeEvidence : Evidence (Fin 6) :=
  .node ⟨[[2]], .write (.var 0) .fls, [0]⟩ .write
    [.node ⟨[[2]], .var 0, [2]⟩ .var [], .node ⟨[[2]], .fls, [1]⟩ .fls []]

def continuationEvidence : Evidence (Fin 6) :=
  .node ⟨[[0,1],[2]], .read (.var 1), [1]⟩ .read
    [.node ⟨[[0,1],[2]], .var 1, [2]⟩ .var []]

#guard checkTree G writeEvidence
#guard checkTree G continuationEvidence
#guard checkEdge G [[0],[2]] [[0,1],[2]] [.subset,.subset]

set_option maxHeartbeats 800000 in
/-- The write changes the heap; the checked point claim preserves the reference
needed by the continuation and widens the write's result to the supplied union. -/
theorem checked_write_then_read (n W h ρ) (he : EnvOk G [[2]] ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (PositiveRules.meaning G [1]) n W h
      (.letE (instantiate 0 ρ (.write (.var 0) .fls)) (instantiate 1 ρ (.read (.var 1)))) :=
  checked_bind_claim (ea := writeEvidence) (eb := continuationEvidence)
    rfl (by cbv) (by decide : checkEdge G [[0],[2]] [[0,1],[2]] [.subset,.subset] = true)
    rfl (by cbv) n W h ρ he hw hh

#print axioms checked_write_then_read
end Verification.ExperimentState.PointClaimTests
