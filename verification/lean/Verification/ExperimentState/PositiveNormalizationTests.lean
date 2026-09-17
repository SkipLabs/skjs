import Verification.ExperimentState.PositiveCertificates
import Verification.ExperimentState.ModelBoundaries

namespace Verification.ExperimentState.PositiveNormalizationTests
open PositiveNormalization PositiveGraphs PositiveCertificates ReferenceConjunctions

private def checkCoreSource [DecidableEq ι] (G : PositiveGraphs.Graph ι) (S T : List ι)
    (cert : Certificate ι) : Bool := checkSource G S T (.core cert)

-- Distribution retains conjunctions of reference contracts instead of treating
-- them as an invariant of intersected contents or as bottom.
#guard normalize (Formula.inter (.atom (.refs [("value", (0 : Nat))] [] []))
  (.union (.atom (.refs [("value", 1)] [] [])) (.atom .nul)))
    = [.refs [("value", 0)] [[("value", 1)]] []]
#guard normalize (Formula.inter (.atom (.arrs [([(0 : Nat)], 1)]))
  (.atom (.arrs [([1], 0)]))) = [.arrs [([0], 1), ([1], 0)]]
#guard normalize (Formula.inter (.atom (.refs [("value", (0 : Nat))] [] [])) (.atom .bool)) = []

def G : PositiveGraphs.Graph (Fin 12) := fun i => match i.val with
  | 0 => .atom .nul
  | 1 => .atom .bool
  | 2 => .inter (.atom (.refs [(valueField, [0])] [] [])) (.atom (.refs [(valueField, [1])] [] []))
  | 3 => .atom (.refs [(valueField, [0])] [] [])
  | 4 => .inter (.atom (.refs [(valueField, [4])] [] [])) (.atom (.refs [(valueField, [4])] [] []))
  | 5 => .atom (.refs [(valueField, [5])] [] [])
  | 6 => .inter (.atom (.refs [(valueField, [3])] [] [])) (.atom (.refs [(valueField, [7])] [] []))
  | 7 => .atom (.refs [(valueField, [1])] [] [])
  | 8 => .atom (.refs [(valueField, [3])] [] [])
  | 9 => .inter (.atom (.arrs [([[0]], [0])])) (.atom (.arrs [([[1]], [0])]))
  | 10 => .atom (.arrs [([[0, 1]], [0])])
  | _ => .inter (.atom .nul) (.atom .bool)

-- Conjunction elimination, including nested reference constraints.
#guard checkCoreSource G [2] [3] ⟨[([2], [3]), ([0], [0])], []⟩
#guard checkCoreSource G [6] [8] ⟨[([6], [8]), ([3], [3]), ([0], [0])], []⟩
-- The opposite direction would invent a constraint.
#guard !(checkCoreSource G [3] [2] ⟨[([3], [2]), ([0], [0])], []⟩)
-- The incompatible reference conjunction is not dropped as bottom.
#guard normalizeGraph G 2 = [.refs [(valueField, [0])] [[(valueField, [1])]] []]
#guard !(checkCoreSource G [2] [] ⟨[([2], [])], []⟩)
-- Disjoint atoms really do normalize to bottom.
#guard checkCoreSource G [11] [] ⟨[([11], [])], []⟩
-- Recursive normalization and checking, with no unfolding of cycles.
#guard checkCoreSource G [4] [5] ⟨[([4], [5]), ([5], [4])], []⟩

-- Previously supported domain splitting survives the representation extension.
def splitCert : Certificate (Fin 12) :=
  ⟨[([9], [10]), ([0], [0]), ([1], [1])],
    [([([[0]], [0]), ([[1]], [0])], (([[0, 1]], [0]),
      .union [] [0] [1] [] (.source ([[0]], [0])) (.source ([[1]], [0]))))]⟩
#guard checkCoreSource G [9] [10] splitCert
#guard !(checkCoreSource G [10] [9] splitCert)

-- The iterative combination rule also survives; every pair of result unions
-- overlaps but their triple intersection is empty.
def TripleG : PositiveGraphs.Graph (Fin 5) := fun i => match i.val with
  | 0 => .atom .nul
  | 1 => .atom .bool
  | 2 => .atom (.arrs [])
  | 3 => .atom (.arrs [([[0]], [0, 1]), ([[0]], [1, 2]), ([[0]], [0, 2])])
  | _ => .atom (.arrs [([[0]], [])])

def tripleCert : Certificate (Fin 5) :=
  ⟨[([3], [4]), ([0], [0]), ([1], [1]), ([0, 1], [0, 1]),
    ([1, 2], [1, 2]), ([0, 2], [0, 2])],
   [([([[0]], [0, 1]), ([[0]], [1, 2]), ([[0]], [0, 2])], (([[0]], []),
     .combine [1] [0, 2]
       (.combine [0, 1] [1, 2] (.source ([[0]], [0, 1])) (.source ([[0]], [1, 2])))
       (.source ([[0]], [0, 2]))))]⟩
#guard checkCoreSource TripleG [3] [4] tripleCert

-- A `bool` source clause is covered by the pair of Boolean singleton clauses.
-- The source side of a coverage obligation splits, so a single source clause
-- may be discharged by several target clauses.
def BoolG : PositiveGraphs.Graph (Fin 6) := fun i => match i.val with
  | 0 => .atom .bool
  | 1 => .atom (.boolLit true)
  | 2 => .atom (.boolLit false)
  | 3 => .atom .nul
  | 4 => .atom (.refs [(valueField, [0])] [] [])
  | _ => .atom (.refs [(valueField, [1, 2])] [] [])

#guard PositiveRules.sourceClauses (normalizeGraph BoolG) [0]
  = [.boolLit true, .boolLit false]
#guard PositiveRules.sourceClauses (normalizeGraph BoolG) [1] = [.boolLit true]
#guard checkCoreSource BoolG [0] [1, 2] ⟨[([0], [1, 2])], []⟩
-- An unrelated further alternative in the target does not disturb the covering.
#guard checkCoreSource BoolG [0] [1, 2, 3] ⟨[([0], [1, 2, 3])], []⟩
-- Controls: the directions that were already derivable still are.
#guard checkCoreSource BoolG [1] [0] ⟨[([1], [0])], []⟩
#guard checkCoreSource BoolG [0] [0] ⟨[([0], [0])], []⟩
-- One singleton alone does not cover `bool`, in either polarity.
#guard !(checkCoreSource BoolG [0] [1] ⟨[([0], [1])], []⟩)
#guard !(checkCoreSource BoolG [0] [2] ⟨[([0], [2])], []⟩)
#guard !(checkCoreSource BoolG [0] [3] ⟨[([0], [3])], []⟩)
-- Splitting the source cannot manufacture a covering of a different shape.
#guard !(checkCoreSource BoolG [3] [1, 2] ⟨[([3], [1, 2])], []⟩)
-- Both directions are now derivable, so the invariant reference contracts
-- `ref bool` and `ref (true | false)` become interchangeable.
#guard checkCoreSource BoolG [4] [5]
  ⟨[([4], [5]), ([0], [1, 2]), ([1, 2], [0])], []⟩
#guard checkCoreSource BoolG [5] [4]
  ⟨[([5], [4]), ([0], [1, 2]), ([1, 2], [0])], []⟩
-- A reference to one singleton is still not a reference to `bool`.
#guard !(checkCoreSource BoolG [4] [5] ⟨[([4], [5]), ([0], [1]), ([1], [0])], []⟩)

theorem checked_boolean_split : FamLe
    (Tower.setSem (PositiveGraphs.denote BoolG) [0])
    (Tower.setSem (PositiveGraphs.denote BoolG) [1, 2]) :=
  accepted_source (by decide : checkCoreSource BoolG [0] [1, 2]
    ⟨[([0], [1, 2])], []⟩ = true)

-- Explicit structural closure and malformed-evidence checks exercise the
-- consolidated public checker, rather than just its cyclic-table component.
#guard checkSource G [0, 0] [1, 0] (.trans [0] .subset .subset)
#guard !(checkSource G [1] [0] (.trans [0] .subset .subset))
#guard !(checkCoreSource G [9] [10] ⟨[([9], [10])], splitCert.arrows⟩)
#guard !(checkArrow (normalizeGraph G) [([0], [0]), ([1], [1])]
  [([[0]], [0]), ([[1]], [0])] [[0, 1]] [0]
  (.union [] [0] [] [] (.source ([[0]], [0])) .empty))

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
    HeapOk 1 (ofList [res R]) [.obj 0 .absent] ∧
    refsT [(valueField, refT nulT)] [[(valueField, refT boolT)]] 1 (ofList [res R])
      (.obj 0 .absent) := by
  have hR := R_cyclic 1
  have hn := (ModelBoundaries.nested_agrees_cycle 2 nulT 1 (by omega) _ _).mpr hR
  have hb := (ModelBoundaries.nested_agrees_cycle 2 boolT 1 (by omega) _ _).mpr hR
  refine ⟨cyclic_heap_ok 1, hn, ?_⟩
  intro B hB
  simp only [List.mem_singleton] at hB
  subst hB
  show recT [(valueField, refT boolT)] 1 (ofList [res R]) (.obj 0 .absent)
  simpa [ModelBoundaries.nestedRef, refT] using hb

#print axioms checked_recursive_example
#print axioms checked_boolean_split
#print axioms nested_inhabited
end Verification.ExperimentState.PositiveNormalizationTests
