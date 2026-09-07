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
#guard is ((extractFn f fc).map (fun r => r.program[1]?.map ControlFlow.Node.expression)) ((some (.var 1)))
#guard ok (do RequestJson.produceJson (toJson (← extractFn f fc)) 6)
-- Test execution of this primitive subset uses the calculus's substitution and
-- simultaneous environment transfer. It is a compiler regression, not a source
-- preservation proof or a second maintained evaluator.
private def runPrimitive : Nat → ControlFlow.Program → Nat → Env → Option Tm
  | 0, _, _, _ => none
  | fuel+1, P, label, ρ => do
    let node ← P[label]?
    let v := instantiate 0 ρ node.expression
    if !isVal v then none else
      match node.continuation with
      | .ret => some v
      | .bind next => runPrimitive fuel P next.label (PointClaims.mapEnv next.mapping (push v ρ))
      | .effect next => runPrimitive fuel P next.label (PointClaims.mapEnv next.mapping ρ)
      | .branch yes no =>
        let target ← match v with | .tru => some yes | .fls => some no | _ => none
        runPrimitive fuel P target.label (PointClaims.mapEnv target.mapping ρ)
      | .branchBind yes no =>
        let target ← match v with | .tru => some yes | .fls => some no | _ => none
        runPrimitive fuel P target.label (PointClaims.mapEnv target.mapping (push v ρ))

private def runRequest (r : Request) : Option Tm := runPrimitive 100 r.program r.start (fun _ => .nul)

private def branchFn (q : Bool) : Verification.Fn :=
  ⟨"branch",(0,1),[],t,
    [.cst (2,3) "outer" none (.lit (4,5) (.vbool true)),
     .ite (6,17) (.lit (8,9) (.vbool q))
       [.cst (10,11) "local" none (.lit (12,13) (.vbool false))]
       (some [.cst (14,15) "local" none (.lit (16,17) .vnull)]),
     .ret (18,21) (.var (20,21) "outer")]⟩
private def branchClaims (q : Bool) : FunTypeClaims :=
  ⟨"branch",(0,1),[],some t,
    [(2,[]),(6,[("outer",some t)]),(10,[("outer",some t)]),
     (14,[("outer",some t)]),(18,[("outer",some t)])],
    [((4,5),some t),((8,9),some ⟨false,[.boolLit q]⟩),
     ((12,13),some b),((16,17),some ⟨false,[.null]⟩),((20,21),some t)]⟩

#guard is ((extractFn (branchFn true) (branchClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (branchFn false) (branchClaims false)).map runRequest) (some .tru)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (branchFn true) (branchClaims true))) 8)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (branchFn false) (branchClaims false))) 8)

-- A shared continuation has exactly one return node, with two predecessors
-- reaching its source-expression node. Continuation duplication fails this test.
private def targets : ControlFlow.Continuation → List Nat
  | .ret => []
  | .bind t | .effect t => [t.label]
  | .branch y n | .branchBind y n => [y.label,n.label]
#guard is ((extractFn (branchFn true) (branchClaims true)).map fun r =>
  (r.program.filter (fun n => n.continuation == .ret)).length) 1
#guard is ((extractFn (branchFn true) (branchClaims true)).map fun r =>
  (r.program.flatMap (fun n => targets n.continuation)).count 1) 2

private def choiceFn (q : Bool) : Verification.Fn :=
  ⟨"choice",(0,1),[],⟨false,[.bool]⟩,
    [.ite (2,11) (.lit (4,5) (.vbool q))
      [.ret (6,9) (.lit (8,9) (.vbool true))]
      (some [.ret (10,13) (.lit (12,13) (.vbool false))])]⟩
private def choiceClaims (q : Bool) : FunTypeClaims :=
  ⟨"choice",(0,1),[],some ⟨false,[.bool]⟩,[(2,[]),(6,[]),(10,[])],
    [((4,5),some ⟨false,[.boolLit q]⟩),((8,9),some t),((12,13),some b)]⟩
#guard is ((extractFn (choiceFn true) (choiceClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (choiceFn false) (choiceClaims false)).map runRequest) (some .fls)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (choiceFn true) (choiceClaims true))) 8)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (choiceFn false) (choiceClaims false))) 8)

-- The tested binding is older than another local, so the refinement map must
-- select its copied value rather than refine whichever slot happens to be first.
private def variableFn (q : Bool) : Verification.Fn :=
  ⟨"variable",(0,1),[],⟨false,[.bool]⟩,
    [.cst (2,3) "tested" (some ⟨false,[.bool]⟩) (.lit (4,5) (.vbool q)),
     .cst (6,7) "other" (some ⟨false,[.bool]⟩) (.lit (8,9) (.vbool false)),
     .ite (10,21) (.var (12,13) "tested")
       [.ret (14,17) (.var (16,17) "tested")]
       (some [.ret (18,21) (.var (20,21) "tested")])]⟩
private def variableClaims (q : Bool) : FunTypeClaims :=
  let bool : Core.Ty := ⟨false,[.bool]⟩
  ⟨"variable",(0,1),[],some bool,
    [(2,[]),(6,[("tested",some bool)]),
     (10,[("tested",some bool),("other",some bool)]),
     (14,[("tested",some t),("other",some bool)]),
     (18,[("tested",some b),("other",some bool)])],
    [((4,5),some ⟨false,[.boolLit q]⟩),((8,9),some b),
     ((12,13),some bool),((16,17),some t),((20,21),some b)]⟩
#guard is ((extractFn (variableFn true) (variableClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (variableFn false) (variableClaims false)).map runRequest) (some .fls)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (variableFn true) (variableClaims true))) 8)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (variableFn false) (variableClaims false))) 8)

end Verification.ExperimentState.SourceExtractionTests
