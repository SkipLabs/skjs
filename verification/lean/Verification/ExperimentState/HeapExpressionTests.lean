import Verification.ExperimentState.HeapExpressionRules
import Verification.ExperimentState.SourceTypes

/-! Execute the checked rules on a primitive/reference graph of the kind the
source pipeline builds. These exercise evidence validation, not hand-assumed HasTy
premises. Full source/CFG acceptance still requires checked edge integration. -/
namespace Verification.ExperimentState.HeapExpressionTests
open ProgramCertificates HeapExpressionRules HeapKnowledge

private def T : SourceTypes.Table := SourceTypes.initial ++ [[.refs [(valueField, [1,2])] []]]
private def G := SourceTypes.graph T
private def boolTy : List Nat := [1,2]
private def refBool : List Nat := [4]
private def writeClaim : Sequent Nat :=
  ⟨[refBool,boolTy],.write (.var 0) (.var 1),[0]⟩
private def writeProof : Evidence Nat := .node writeClaim .write
  [.node ⟨writeClaim.context,.var 0,refBool⟩ .var [],
   .node ⟨writeClaim.context,.var 1,boolTy⟩ .var []]
private def beforeWrite : Knowledge :=
  ⟨[⟨0,[.fls],valueField⟩,⟨2,[.fls],valueField⟩],[⟨1,[.tru],valueField⟩,⟨3,[.fls],valueField⟩],[]⟩
private def afterWrite := writeOutput beforeWrite 0 valueField [.tru]

-- The storage contract permits true; current contents are separately updated.
#guard checkStep G writeClaim beforeWrite
  (.written 0 1 [.tru] writeProof) == some afterWrite
-- Resetting at a source entry may leave no old observation at all.
#guard checkStep G writeClaim ⟨[],[],[]⟩ (.written 0 1 [.tru,.fls] writeProof) ==
  some (writeOutput ⟨[],[],[]⟩ 0 valueField [.tru,.fls])
-- An old alias fact is discarded, but immutable snapshots survive the write.
#guard afterWrite.cells == [⟨1,[.tru],valueField⟩]
#guard afterWrite.values == [⟨0,[.nul],valueField⟩,⟨2,[.tru],valueField⟩,⟨4,[.fls],valueField⟩]
#guard checkStep G writeClaim beforeWrite
  (.written 0 1 [.fls] writeProof) == none

-- Transfer selects the written cell. Its old false observation cannot survive.
private def afterEdge := HeapKnowledge.project afterWrite (some [1]) 1
#guard HeapKnowledge.check afterWrite afterEdge (some [1])
#guard afterEdge.cells == [⟨0,[.tru],valueField⟩]
#guard !(HeapKnowledge.check afterWrite ⟨[⟨0,[.fls],valueField⟩],[],[]⟩ (some [1]))

-- Check a producer's wider Boolean read claim, then use the precise immutable
-- result to discharge a true return contract. A stale false claim is rejected.
private def readClaim : Sequent Nat := ⟨[refBool],.read (.var 0),boolTy⟩
private def readProof : Evidence Nat := .node readClaim .read
  [.node ⟨readClaim.context,.var 0,refBool⟩ .var []]
#guard checkStep G readClaim ⟨[],[],[]⟩ (.typedRead 0 [(valueField,boolTy)] readProof) ==
  some (readFrame ⟨[],[],[]⟩ 0 valueField)
#guard (readFrame ⟨[],[],[]⟩ 0 valueField).links == [⟨1,0,false,valueField⟩]
-- Neither a false storage contract nor a changed read claim can use that proof.
#guard checkStep G readClaim ⟨[],[],[]⟩ (.typedRead 0 [(valueField, [1])] readProof) == none
#guard checkStep G {readClaim with type := [1]} ⟨[],[],[]⟩ (.typedRead 0 [(valueField,boolTy)] readProof) == none
private def afterRead := readOutput afterEdge 0 valueField [.tru]
#guard checkStep G readClaim afterEdge (.observedRead 0 [.tru]) == some afterRead
#guard checkStep G {readClaim with type := [2]} afterEdge (.observedRead 0 [.tru]) == none
#guard checkStep G readClaim afterEdge (.observedRead 0 [.fls]) == none
#guard (checkStep G ⟨[boolTy,refBool],.var 0,[1]⟩ afterRead (.knownValue 0 [.tru])).isSome
#guard checkStep G ⟨[boolTy,refBool],.var 0,[2]⟩ afterRead (.knownValue 0 [.tru]) == none
-- A certificate cannot change the expression or use an out-of-scope fact.
#guard checkStep G {readClaim with term := .nul} afterEdge (.observedRead 0 [.tru]) == none
#guard checkStep G {readClaim with context := []} afterEdge (.observedRead 0 [.tru]) == none

private def allocClaim : Sequent Nat := ⟨[boolTy],.alloc (.var 0),refBool⟩
private def allocProof : Evidence Nat := .node allocClaim .alloc
  [.node ⟨[boolTy],.var 0,boolTy⟩ .var []]
#guard checkStep G allocClaim ⟨[],[⟨0,[.fls],valueField⟩],[]⟩ (.allocated allocProof) ==
  some (allocOutput ⟨[],[⟨0,[.fls],valueField⟩],[]⟩ [(valueField, [.fls])])
-- With no current observation, the initializer invariant gives Boolean contents.
#guard checkStep G allocClaim ⟨[],[],[]⟩ (.allocated allocProof) ==
  some (allocOutput ⟨[],[],[]⟩ [(valueField,[.tru,.fls])])

-- Administrative source copies preserve the cell fact through aliasing.
private def copyClaim : Sequent Nat := ⟨[refBool],.var 0,refBool⟩
private def copyProof : Evidence Nat := .node copyClaim .var []
#guard checkStep G copyClaim afterEdge (.pure copyProof) == some (copy afterEdge 0)
#guard (copy afterEdge 0).cells == [⟨0,[.tru],valueField⟩,⟨1,[.tru],valueField⟩]
-- Ordinary evidence promises no heap preservation, even for a known write.
#guard checkStep G writeClaim beforeWrite (.ordinary writeProof) ==
  some (ordinaryOutput beforeWrite)
#guard (ordinaryOutput beforeWrite).cells == []
-- Observations never authorize a write forbidden by the storage invariant.
private def narrowWrite : Sequent Nat :=
  ⟨[[5],boolTy],.write (.var 0) (.var 1),[0]⟩
private def invalidWrite : Evidence Nat := .node narrowWrite .write
  [.node ⟨narrowWrite.context,.var 0,[5]⟩ .var [],
   .node ⟨narrowWrite.context,.var 1,boolTy⟩ .var []]
#guard checkStep G narrowWrite beforeWrite
  (.written 0 1 [.tru] invalidWrite) == none

-- Pure computational guards frame existing facts. Function creation allocates
-- without running its body, and therefore needs a distinct effect rule.
#guard pureTerm (.ite (.test .isNul (.var 0)) .tru .fls)
#guard !pureTerm (.funE (.write (.var 0) .fls))
#guard !pureTerm (.ite .tru .nul (.write (.var 0) .fls))
#guard !pureTerm (.test .isNul (.read (.var 0)))
#guard !pureTerm (.app (.funE .nul) .nul)
#guard !pureTerm (.alloc .tru)

-- A creation preserves old facts even when its uncalled body would mutate a cell.
private def CG := SourceTypes.graph (T ++ [[.arrs []]])
private def creationClaim : Sequent Nat :=
  ⟨[refBool,boolTy,refBool,boolTy],.funE (.write (.var 1) .fls),[5]⟩
private def creationProof : Evidence Nat := .node creationClaim .funE []
#guard checkStep CG creationClaim beforeWrite (.created creationProof) == some (shift beforeWrite)
#guard checkStep CG creationClaim beforeWrite (.pure creationProof) == none
-- Arity changes the body's bound variables, never the effects of creation.
private def creationAt (arity : Nat) : Sequent Nat :=
  ⟨creationClaim.context,.make (.closure arity (.write (.var arity) .fls)) .nul,[5]⟩
#guard [0,2].all fun arity =>
  let j := creationAt arity
  checkStep CG j beforeWrite (.created (.node j .funE [])) == some (shift beforeWrite)

-- An actual write cannot obtain the creation frame, even with a valid typing proof.
#guard checkStep G writeClaim beforeWrite (.created writeProof) == none

#print axioms pure_step
#print axioms pure_frame
end Verification.ExperimentState.HeapExpressionTests
