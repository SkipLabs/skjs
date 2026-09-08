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
  ⟨2, SourceTypes.types, [⟨t,.ret⟩], [⟨[],A⟩], A, 0, []⟩
#guard ok (RequestJson.produceJson (toJson (request .tru [1])) 5)
#guard ok (RequestJson.produceJson (toJson (request .fls [2])) 5)
#guard ok (RequestJson.produceJson (toJson (request .tru [1,2])) 5)
#guard !ok (RequestJson.produceJson (toJson (request .tru [2])) 5)
#guard !ok (RequestJson.produceJson (toJson (request .fls [1])) 5)

#guard PositiveCertificates.checkClause SourceTypes.graph [] [] (.boolLit true) .bool
#guard !PositiveCertificates.checkClause SourceTypes.graph [] [] .bool (.boolLit true)
#guard !PositiveCertificates.checkClause SourceTypes.graph [] [] (.boolLit true) (.boolLit false)

-- Primitive fixture types use the same JSON schema as real source claims.
private def wireTy (t : Core.Ty) : Json := Json.mkObj [("top", toJson t.top),
  ("atoms", toJson (t.atoms.map fun a => match a with
    | .null => Json.mkObj [("a",toJson "null")]
    | .bool => Json.mkObj [("a",toJson "boolean")]
    | .boolLit b => Json.mkObj [("a",toJson "booleanlit"),("v",toJson (if b then "true" else "false"))]
    | _ => Json.mkObj [("a",toJson "unsupported")]))]
-- Name resolution after a second binding must select the older slot.
private def f : SourceInput.Fn := ⟨"f",(0,1),[],(wireTy ⟨false,[.boolLit true]⟩),
  [.cst (2,3) "x" none (.lit (4,5) (.vbool true)),
   .cst (6,7) "y" none (.lit (8,9) (.vbool false)),
   .ret (10,11) (.var (12,13) "x")]⟩
private def t : Json := (wireTy ⟨false,[.boolLit true]⟩)
private def b : Json := (wireTy ⟨false,[.boolLit false]⟩)
private def fc : SourceInput.Claims := ⟨"f",(0,1),[],t,
  [(2,[]),(6,[("x",t)]),(10,[("x",t),("y",b)])],
  [((4,5),t),((8,9),b),((12,13),t)]⟩
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

private def branchFn (q : Bool) : SourceInput.Fn :=
  ⟨"branch",(0,1),[],t,
    [.cst (2,3) "outer" none (.lit (4,5) (.vbool true)),
     .ite (6,17) (.lit (8,9) (.vbool q))
       [.cst (10,11) "local" none (.lit (12,13) (.vbool false))]
       (some [.cst (14,15) "local" none (.lit (16,17) .vnull)]),
     .ret (18,21) (.var (20,21) "outer")]⟩
private def branchClaims (q : Bool) : SourceInput.Claims :=
  ⟨"branch",(0,1),[],t,
    [(2,[]),(6,[("outer",t)]),(10,[("outer",t)]),
     (14,[("outer",t)]),(18,[("outer",t)])],
    [((4,5),t),((8,9),(wireTy ⟨false,[.boolLit q]⟩)),
     ((12,13),b),((16,17),(wireTy ⟨false,[.null]⟩)),((20,21),t)]⟩

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

private def choiceFn (q : Bool) : SourceInput.Fn :=
  ⟨"choice",(0,1),[],(wireTy ⟨false,[.bool]⟩),
    [.ite (2,11) (.lit (4,5) (.vbool q))
      [.ret (6,9) (.lit (8,9) (.vbool true))]
      (some [.ret (10,13) (.lit (12,13) (.vbool false))])]⟩
private def choiceClaims (q : Bool) : SourceInput.Claims :=
  ⟨"choice",(0,1),[],(wireTy ⟨false,[.bool]⟩),[(2,[]),(6,[]),(10,[])],
    [((4,5),(wireTy ⟨false,[.boolLit q]⟩)),((8,9),t),((12,13),b)]⟩
#guard is ((extractFn (choiceFn true) (choiceClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (choiceFn false) (choiceClaims false)).map runRequest) (some .fls)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (choiceFn true) (choiceClaims true))) 8)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (choiceFn false) (choiceClaims false))) 8)

-- The tested binding is older than another local, so the refinement map must
-- select its copied value rather than refine whichever slot happens to be first.
private def variableFn (q : Bool) : SourceInput.Fn :=
  ⟨"variable",(0,1),[],(wireTy ⟨false,[.bool]⟩),
    [.cst (2,3) "tested" (some (wireTy ⟨false,[.bool]⟩)) (.lit (4,5) (.vbool q)),
     .cst (6,7) "other" (some (wireTy ⟨false,[.bool]⟩)) (.lit (8,9) (.vbool false)),
     .ite (10,21) (.var (12,13) "tested")
       [.ret (14,17) (.var (16,17) "tested")]
       (some [.ret (18,21) (.var (20,21) "tested")])]⟩
private def variableClaims (q : Bool) : SourceInput.Claims :=
  let bool : Json := (wireTy ⟨false,[.bool]⟩)
  ⟨"variable",(0,1),[],bool,
    [(2,[]),(6,[("tested",bool)]),
     (10,[("tested",bool),("other",bool)]),
     (14,[("tested",t),("other",bool)]),
     (18,[("tested",b),("other",bool)])],
    [((4,5),(wireTy ⟨false,[.boolLit q]⟩)),((8,9),b),
     ((12,13),bool),((16,17),t),((20,21),b)]⟩
#guard is ((extractFn (variableFn true) (variableClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (variableFn false) (variableClaims false)).map runRequest) (some .fls)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (variableFn true) (variableClaims true))) 8)
#guard ok (do RequestJson.produceJson (toJson (← extractFn (variableFn false) (variableClaims false))) 8)

-- Source input slots follow declaration order, independently of export order
-- inside each environment. Newly declared locals still push ahead of them.
private def parameterFn : SourceInput.Fn :=
  ⟨"parameters",(0,1),[⟨"first",(wireTy ⟨false,[.null]⟩)⟩,⟨"second",(wireTy ⟨false,[.bool]⟩)⟩],
    (wireTy ⟨false,[.bool]⟩),[.ret (2,5) (.var (4,5) "second")]⟩
private def parameterClaims : SourceInput.Claims :=
  ⟨"parameters",(0,1),[("first",(wireTy ⟨false,[.null]⟩)),("second",(wireTy ⟨false,[.bool]⟩))],
    (wireTy ⟨false,[.bool]⟩),
    [(2,[("second",(wireTy ⟨false,[.bool]⟩)),("first",(wireTy ⟨false,[.null]⟩))])],
    [((4,5),(wireTy ⟨false,[.bool]⟩))]⟩
private def runArguments (r : Request) (vs : List Tm) :=
  runPrimitive 100 r.program r.start (fun i => vs[i]?.getD .nul)
#guard is ((extractFn parameterFn parameterClaims).map (·.inputs)) [[0],[1,2]]
#guard is ((extractFn parameterFn parameterClaims).map (fun r => runArguments r [.nul,.tru])) (some .tru)
#guard is ((extractFn parameterFn parameterClaims).map (fun r => runArguments r [.nul,.fls])) (some .fls)
#guard ok (do RequestJson.produceJson (toJson (← extractFn parameterFn parameterClaims)) 8)

-- Even if all internal claims consistently narrow the parameter to true,
-- the separate source-signature entry edge must reject that narrowing.
private def narrowedEntry : SourceInput.Claims := { parameterClaims with
  envs := [(2,[("first",(wireTy ⟨false,[.null]⟩)),("second",t)])]
  exprs := [((4,5),t)] }
#guard !ok (do RequestJson.produceJson (toJson (← extractFn parameterFn narrowedEntry)) 8)

private def cellWire : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "record"),("fields",toJson [Json.mkObj [("name",toJson "value"),
    ("optional",toJson false),("read",wireTy ⟨false,[.bool]⟩),("write",wireTy ⟨false,[.bool]⟩)]]),
   ("indexes",Json.mkObj [("string",toJson "absent"),("number",toJson "absent"),("symbol",toJson "absent")]),
   ("call",toJson "unknown"),("construct",toJson "unknown"),("array",toJson "unknown")]])]

-- Trace the actual extracted graph: allocate, alias, assign through the alias.
-- Check both the assignment's value and the mutated heap using the existing
-- calculus transitions, without introducing a second evaluator.
private def cellFn : SourceInput.Fn :=
  ⟨"cell",(0,1),[],wireTy ⟨false,[.bool]⟩,
    [.cst (2,3) "cell" (some cellWire) (.alloc (4,7) (.lit (5,6) (.vbool true))),
     .cst (8,9) "alias" (some cellWire) (.var (10,11) "cell"),
     .ret (12,19) (.write (14,19) (.var (14,15) "alias") (.lit (18,19) (.vbool false))) ]⟩
private def cellClaims : SourceInput.Claims :=
  ⟨"cell",(0,1),[],wireTy ⟨false,[.bool]⟩,
   [(2,[]),(8,[("cell",cellWire)]),(12,[("cell",cellWire),("alias",cellWire)])],
   [((4,7),cellWire),((5,6),t),((10,11),cellWire),
    ((14,19),b),((14,15),cellWire),((18,19),b)]⟩
private def cellRequest : Request :=
  (SourceExtraction.extractFn cellFn cellClaims).toOption.getD (request .nul [0])
#guard ok (SourceExtraction.extractFn cellFn cellClaims)
#guard ok (RequestJson.produceJson (toJson cellRequest) 8)

private def cellProgram : ControlFlow.Program :=
  [⟨.var 0,.ret⟩,
   ⟨.var 0,.bind ⟨0,some [0,3,4]⟩⟩,
   ⟨.write (.var 1) (.var 0),.effect 1⟩,
   ⟨.fls,.bind 2⟩, ⟨.var 0,.bind 3⟩,
   ⟨.var 0,.effect 4⟩, ⟨.var 0,.bind 5⟩,
   ⟨.var 0,.effect 6⟩, ⟨.alloc (.var 0),.bind ⟨7,some [0]⟩⟩,
   ⟨.tru,.bind 8⟩, ⟨.nul,.effect 9⟩]
#guard cellRequest.program == cellProgram
#guard cellRequest.start == 10

theorem cell_assignment_trace : ControlFlow.Execution cellProgram 24 []
    (.at 10 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.allocV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms cell_assignment_trace

end Verification.ExperimentState.SourceExtractionTests
