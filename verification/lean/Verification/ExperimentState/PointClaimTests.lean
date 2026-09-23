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

end Verification.ExperimentState.PointClaimTests
