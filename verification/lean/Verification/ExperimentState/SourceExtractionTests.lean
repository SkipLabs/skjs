import Verification.ExperimentState.SourceExtraction

namespace Verification.ExperimentState.SourceExtractionTests
open Lean PositiveNormalization ProgramTyping RequestJson SourceExtraction

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

private def is [BEq α] (r : Except String α) (expected : α) : Bool :=
  match r with | .ok a => a == expected | .error _ => false

-- Exact finite-set translation, including normalization of unions.
#guard is (SourceTypes.translate ⟨false,[.bool]⟩) ([1,2])
#guard is (SourceTypes.translate ⟨false,[.boolLit true]⟩) ([1])
#guard is (SourceTypes.translate ⟨false,[.boolLit false]⟩) ([2])
#guard is (SourceTypes.translate ⟨false,[.boolLit false,.null,.boolLit true,.null]⟩) ([0,1,2])
#guard is (SourceTypes.translate ⟨false,[]⟩) ([])
#guard !ok (SourceTypes.translate ⟨true,[]⟩)
#guard !ok (SourceTypes.translate ⟨false,[.str]⟩)
#guard (meet (.boolLit true) (.boolLit false) : List (Clause (List Nat))) == []
#guard (meet .bool (.boolLit true) : List (Clause (List Nat))) == [.boolLit true]

private def request (t : Tm) (A : Ty Nat) : Request :=
  ⟨1, SourceTypes.types, [⟨t,.ret⟩], [⟨[],A⟩], A, 0⟩
#guard ok (RequestJson.produceJson (toJson (request .tru [1])) 5)
#guard ok (RequestJson.produceJson (toJson (request .fls [2])) 5)
#guard ok (RequestJson.produceJson (toJson (request .tru [1,2])) 5)
#guard !ok (RequestJson.produceJson (toJson (request .tru [2])) 5)
#guard !ok (RequestJson.produceJson (toJson (request .fls [1])) 5)

#guard PositiveCertificates.checkClause SourceTypes.graph [] [] (.boolLit true) .bool
#guard !PositiveCertificates.checkClause SourceTypes.graph [] [] .bool (.boolLit true)
#guard !PositiveCertificates.checkClause SourceTypes.graph [] [] (.boolLit true) (.boolLit false)

-- Name resolution after a second binding must select the older slot.
private def f : Verification.Fn := ⟨"f",(0,1),[],⟨false,[.boolLit true]⟩,
  [.cst (2,3) "x" none (.lit (4,5) (.vbool true)),
   .cst (6,7) "y" none (.lit (8,9) (.vbool false)),
   .ret (10,11) (.var (12,13) "x")]⟩
private def t : Core.Ty := ⟨false,[.boolLit true]⟩
private def b : Core.Ty := ⟨false,[.boolLit false]⟩
private def fc : FunTypeClaims := ⟨"f",(0,1),[],some t,
  [(2,[]),(6,[("x",some t)]),(10,[("x",some t),("y",some b)])],
  [((4,5),some t),((8,9),some b),((12,13),some t)]⟩
#guard is ((extractFn f fc).map (fun r => r.program[4]?.map ControlFlow.Node.expression)) ((some (.var 1)))
#guard ok (do RequestJson.produceJson (toJson (← extractFn f fc)) 6)
end Verification.ExperimentState.SourceExtractionTests
