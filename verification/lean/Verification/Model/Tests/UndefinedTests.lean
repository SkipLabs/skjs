import Verification.Model.Source.SourceExtraction

/-! Exact undefined contracts, table growth and checked rules. The source suite
separately exercises exported claims and execution; these pin the consumer. -/
namespace Verification.Model.UndefinedTests
open ProgramTyping ProgramCertificates SourceTypes PositiveRules HeapExpressionRules

#guard encode ⟨false,[.undef]⟩ == [3]
#guard encode ⟨false,[.null,.bool,.undef]⟩ == [0,1,2,3]

-- Interning gives distinct contracts distinct labels, returns a known label
-- without a new row, and never lets undefined collapse into a smaller operand.
private def lowered : Except String (List Nat × Table) :=
  (do return [← CellClaims.cellReference [3], ← CellClaims.cellReference [], ← use (.arrs [⟨[3], [[3]], [1,2], .unrestricted⟩] []),
      ← use (.arrs [⟨[3], [[]], [1,2], .unrestricted⟩] []), ← CellClaims.cellReference [3]]).run initial
#guard lowered.toOption.map (·.1) == some [4,5,6,7,4]
#guard lowered.toOption.map (·.2.length) == some 8
-- A clause the table lacks is out of range, never a different contract.
#guard label initial (.refs [(valueField, [3])] [] []) == initial.length
-- A location under two contracts has a label of its own, not the plain cell's.
private def pair := intern initial (.refs [(valueField, [0])] [[(valueField,[1,2])]] [])
#guard label pair (.refs [(valueField, [0])] [[(valueField,[1,2])]] []) == 4
#guard label pair (.refs [(valueField, [0])] [] []) == pair.length

private def G := graph initial
private def undefProof : Evidence Nat := .node ⟨[],.undef,[3]⟩ .undef []
#guard checkTree G undefProof
#guard !checkTree G (.node ⟨[],.undef,[0]⟩ .undef [])
#guard (pureOutput ⟨[],[],[]⟩ .undef).values == [⟨0,[.undef],valueField⟩]
#guard HeapKnowledge.atoms G [0,3] == some [.nul,.undef]

private def write (A : Ty Nat) : Bool :=
  let T := intern initial (.refs [(valueField,A)] [] [])
  let Ref := [label T (.refs [(valueField,A)] [] [])]
  let Γ := [Ref,[3]]
  checkTree (graph T) (.node ⟨Γ,.write (.var 0) (.var 1),[0]⟩ .write
    [.node ⟨Γ,.var 0,Ref⟩ .var [],.node ⟨Γ,.var 1,A⟩ (.sub .subset)
      [.node ⟨Γ,.var 1,[3]⟩ .var []]])
-- The write rule requires the RHS at the invariant, so a direct singleton
-- storage contract accepts undefined and a Boolean one cannot.
#guard write [3]
#guard write [1,2,3]
#guard !write [1,2]

#guard decide (Answers G [0,3] .isNullish true)
#guard !decide (Answers G [0,3] .isNul true)
#guard !decide (Answers G [0,3] .isUndef true)
#guard BranchRefinement.tagSlice G [0,1,2,3] .isUndef true == [3]
#guard BranchRefinement.tagSlice G [0,1,2,3] .isNul false == [1,2,3]
#guard BranchRefinement.tagSlice G [0,1,2,3] .isNullish false == [1,2]

#print axioms SourceTypes.translate_exact
#print axioms CellClaims.reference_exact
#print axioms HasTy.sound
end Verification.Model.UndefinedTests
