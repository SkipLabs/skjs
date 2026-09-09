import Verification.ExperimentState.SourceExtraction

/-! Exact undefined contracts and checked rules. The source suite separately
exercises exported claims and execution; these checks pin the consumer itself. -/
namespace Verification.ExperimentState.UndefinedTests
open ProgramTyping ProgramCertificates SourceTypes PositiveRules HeapExpressionRules

#guard encode ⟨false,[.undef]⟩ == [75]
#guard encode ⟨false,[.null,.bool,.undef]⟩ == [0,1,2,75]
#guard CellClaims.referenceLabel [75] != CellClaims.referenceLabel []
#guard FunctionClaims.label [75] [1,2] != FunctionClaims.label [] [1,2]
#guard FunctionClaims.label [1,2] [75] != FunctionClaims.label [1,2] []
-- Unknown operands cannot silently lose labels during selection.
#guard CellClaims.referenceLabel [999] == types.length
#guard FunctionClaims.label [999] [75] == types.length

private def undefProof : Evidence Nat := .node ⟨[],.undef,[75]⟩ .undef []
#guard checkTree graph undefProof
#guard !checkTree graph (.node ⟨[],.undef,[0]⟩ .undef [])
#guard (pureOutput ⟨[],[],[]⟩ .undef).values == [⟨0,[.undef]⟩]
#guard HeapKnowledge.literals graph [0,75] == some [.nul,.undef]

private def write (A : Ty Nat) : Evidence Nat :=
  let Ref := [CellClaims.referenceLabel A]
  let Γ := [Ref,[75]]
  .node ⟨Γ,.write (.var 0) (.var 1),[0]⟩ .write
    [.node ⟨Γ,.var 0,Ref⟩ .var [],.node ⟨Γ,.var 1,A⟩ (.sub .subset)
      [.node ⟨Γ,.var 1,[75]⟩ .var []]]
-- The write rule requires the RHS at the invariant, so a direct singleton
-- storage contract accepts undefined and a Boolean one cannot.
#guard checkTree graph (write [75])
#guard checkTree graph (write [1,2,75])
#guard !checkTree graph (write [1,2])

#guard decide (Answers graph [0,75] .isNullish true)
#guard !decide (Answers graph [0,75] .isNul true)
#guard !decide (Answers graph [0,75] .isUndef true)
#guard BranchRefinement.tagSlice graph [0,1,2,75] .isUndef true == [75]
#guard BranchRefinement.tagSlice graph [0,1,2,75] .isNul false == [1,2,75]
#guard BranchRefinement.tagSlice graph [0,1,2,75] .isNullish false == [1,2]

#print axioms SourceTypes.translate_exact
#print axioms CellClaims.reference_exact
#print axioms FunctionClaims.translate_exact
#print axioms HasTy.sound
end Verification.ExperimentState.UndefinedTests
