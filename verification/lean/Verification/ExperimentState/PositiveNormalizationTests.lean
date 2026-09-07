import Verification.ExperimentState.PositiveCertificates
import Verification.ExperimentState.ModelBoundaries

namespace Verification.ExperimentState.PositiveNormalizationTests
open PositiveNormalization PositiveGraphs PositiveCertificates ReferenceConjunctions

private def checkCoreSource [DecidableEq ι] (G : PositiveGraphs.Graph ι) (S T : List ι)
    (cert : Certificate ι) : Bool := checkSource G S T (.core cert)

-- Distribution retains conjunctions of reference contracts instead of treating
-- them as an invariant of intersected contents or as bottom.
#guard normalize (Formula.inter (.atom (.refs (0 : Nat) []))
  (.union (.atom (.refs 1 [])) (.atom .nul))) = [.refs 0 [1]]
#guard normalize (Formula.inter (.atom (.arrs [((0 : Nat), 1)]))
  (.atom (.arrs [(1, 0)]))) = [.arrs [(0, 1), (1, 0)]]
#guard normalize (Formula.inter (.atom (.refs (0 : Nat) [])) (.atom .bool)) = []

def G : PositiveGraphs.Graph (Fin 12) := fun i => match i.val with
  | 0 => .atom .nul
  | 1 => .atom .bool
  | 2 => .inter (.atom (.refs [0] [])) (.atom (.refs [1] []))
  | 3 => .atom (.refs [0] [])
  | 4 => .inter (.atom (.refs [4] [])) (.atom (.refs [4] []))
  | 5 => .atom (.refs [5] [])
  | 6 => .inter (.atom (.refs [3] [])) (.atom (.refs [7] []))
  | 7 => .atom (.refs [1] [])
  | 8 => .atom (.refs [3] [])
  | 9 => .inter (.atom (.arrs [([0], [0])])) (.atom (.arrs [([1], [0])]))
  | 10 => .atom (.arrs [([0, 1], [0])])
  | _ => .inter (.atom .nul) (.atom .bool)

-- Conjunction elimination, including nested reference constraints.
#guard checkCoreSource G [2] [3] ⟨[([2], [3]), ([0], [0])], []⟩
#guard checkCoreSource G [6] [8] ⟨[([6], [8]), ([3], [3]), ([0], [0])], []⟩
-- The opposite direction would invent a constraint.
#guard !(checkCoreSource G [3] [2] ⟨[([3], [2]), ([0], [0])], []⟩)
-- The incompatible reference conjunction is not dropped as bottom.
#guard normalizeGraph G 2 = [.refs [0] [[1]]]
#guard !(checkCoreSource G [2] [] ⟨[([2], [])], []⟩)
-- Disjoint atoms really do normalize to bottom.
#guard checkCoreSource G [11] [] ⟨[([11], [])], []⟩
-- Recursive normalization and checking, with no unfolding of cycles.
#guard checkCoreSource G [4] [5] ⟨[([4], [5]), ([5], [4])], []⟩

-- Previously supported domain splitting survives the representation extension.
def splitCert : Certificate (Fin 12) :=
  ⟨[([9], [10]), ([0], [0]), ([1], [1])],
    [([([0], [0]), ([1], [0])], (([0, 1], [0]),
      .union [0] [1] (.source ([0], [0])) (.source ([1], [0]))))]⟩
#guard checkCoreSource G [9] [10] splitCert
#guard !(checkCoreSource G [10] [9] splitCert)

-- The iterative combination rule also survives; every pair of result unions
-- overlaps but their triple intersection is empty.
def TripleG : PositiveGraphs.Graph (Fin 5) := fun i => match i.val with
  | 0 => .atom .nul
  | 1 => .atom .bool
  | 2 => .atom (.arrs [])
  | 3 => .atom (.arrs [([0], [0, 1]), ([0], [1, 2]), ([0], [0, 2])])
  | _ => .atom (.arrs [([0], [])])

def tripleCert : Certificate (Fin 5) :=
  ⟨[([3], [4]), ([0], [0]), ([1], [1]), ([0, 1], [0, 1]),
    ([1, 2], [1, 2]), ([0, 2], [0, 2])],
   [([([0], [0, 1]), ([0], [1, 2]), ([0], [0, 2])], (([0], []),
     .combine [1] [0, 2]
       (.combine [0, 1] [1, 2] (.source ([0], [0, 1])) (.source ([0], [1, 2])))
       (.source ([0], [0, 2]))))]⟩
#guard checkCoreSource TripleG [3] [4] tripleCert

-- Explicit structural closure and malformed-evidence checks exercise the
-- consolidated public checker, rather than just its cyclic-table component.
#guard checkSource G [0, 0] [1, 0] (.trans [0] .subset .subset)
#guard !(checkSource G [1] [0] (.trans [0] .subset .subset))
#guard !(checkCoreSource G [9] [10] ⟨[([9], [10])], splitCert.arrows⟩)
#guard !(checkArrow (normalizeGraph G) [([0], [0]), ([1], [1])]
  [([0], [0]), ([1], [0])] [0, 1] [0]
  (.union [0] [] (.source ([0], [0])) .empty))

example : PositiveRules.Sub (normalizeGraph G) [0, 0] [1, 0] :=
  check_sound (by decide : check (normalizeGraph G) [0, 0] [1, 0]
    (.trans [0] .subset .subset) = true)

theorem checked_recursive_example : FamLe
    (Tower.setSem (PositiveGraphs.denote G) [4])
    (Tower.setSem (PositiveGraphs.denote G) [5]) :=
  accepted_source (by decide : checkCoreSource G [4] [5]
    ⟨[([4], [5]), ([5], [4])], []⟩ = true)

/-- Nested incompatible contracts have real overlap at an informative budget,
with a satisfying cyclic heap, not just at the universal zero approximation. -/
theorem nested_inhabited :
    HeapOk 1 (ofList [res R]) [.loc 0] ∧
    refsT (refT nulT) [refT boolT] 1 (ofList [res R]) (.loc 0) := by
  have hR := R_cyclic 1
  have hn := (ModelBoundaries.nested_agrees_cycle 2 nulT 1 (by omega) _ _).mpr hR
  have hb := (ModelBoundaries.nested_agrees_cycle 2 boolT 1 (by omega) _ _).mpr hR
  exact ⟨cyclic_heap_ok 1, hn, by simpa [ModelBoundaries.nestedRef] using hb⟩

#print axioms checked_recursive_example
#print axioms nested_inhabited
end Verification.ExperimentState.PositiveNormalizationTests
