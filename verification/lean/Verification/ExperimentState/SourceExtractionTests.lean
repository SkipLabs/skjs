import Verification.ExperimentState.SourceExtraction

namespace Verification.ExperimentState.SourceExtractionTests
open Lean PositiveNormalization ProgramTyping RequestJson SourceExtraction

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

private def is [BEq α] (r : Except String α) (expected : α) : Bool :=
  match r with | .ok a => a == expected | .error _ => false

-- Exercise the source-specific vocabulary, not every unrelated signature in
-- the whole type table. The independent checker still receives the full graph.
private def produceSourceJson (j : Json) (fuel : Nat)
    (suggestions : List (ProgramCertificates.Sequent Nat) := [])
    (known : List (ProgramCertificates.Evidence Nat) := []) : Except String Json := do
  let r ← decodeRequest j
  let source : SourceRequest := ⟨r,[],[],[],[]⟩
  RequestJson.produceJson j fuel suggestions known [] (some source.searchLabels)

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

private def G0 := SourceTypes.graph SourceTypes.initial
private def request (t : Tm) (A : Ty Nat) : Request :=
  ⟨SourceTypes.initial, [⟨t,.ret⟩], [⟨[],A⟩], A, 0, []⟩
#guard ok (produceSourceJson (toJson (request .tru [1])) 5)
#guard ok (produceSourceJson (toJson (request .fls [2])) 5)
#guard ok (produceSourceJson (toJson (request .tru [1,2])) 5)
#guard !ok (produceSourceJson (toJson (request .tru [2])) 5)
#guard !ok (produceSourceJson (toJson (request .fls [1])) 5)

#guard PositiveCertificates.checkClause G0 [] [] (.boolLit true) .bool
#guard !PositiveCertificates.checkClause G0 [] [] .bool (.boolLit true)
#guard !PositiveCertificates.checkClause G0 [] [] (.boolLit true) (.boolLit false)

-- Primitive fixture types use the same JSON schema as real source claims.
private def wireTy (t : Wire.Ty) : Json := Json.mkObj [("top", toJson t.top),
  ("atoms", toJson (t.atoms.map fun a => match a with
    | .null => Json.mkObj [("a",toJson "null")]
    | .bool => Json.mkObj [("a",toJson "boolean")]
    | .boolLit b => Json.mkObj [("a",toJson "booleanlit"),("v",toJson (if b then "true" else "false"))]
    | _ => Json.mkObj [("a",toJson "unsupported")]))]
-- Name resolution after a second binding must select the older slot.
-- Complete producer-neutral claims for literal negation. SKJS may constant-fold
-- these literals without exporting their operand claims; that is an export gap.
private def checkLiteralNegation (q : Bool) : Except String Unit := do
  let result := wireTy ⟨false,[.boolLit (!q)]⟩
  let fn : SourceInput.Fn := ⟨"negate",(0,1),[],result,
    [.ret (2,6) (.not (3,6) (.lit (4,6) (.vbool q)))]⟩
  let claims : SourceInput.Claims := ⟨"negate",(0,1),[],result,[(2,[])],
    [((3,6),result),((4,6),wireTy ⟨false,[.boolLit q]⟩)]⟩
  let r ← extractFn fn claims
  let j := toJson r.toRequest
  verifyJson j (← produceSourceJson j 10)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 10 r.obligations
  pure ()
#guard ok (checkLiteralNegation true)
#guard ok (checkLiteralNegation false)

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
#guard ok (do produceSourceJson (toJson (← extractFn f fc).toRequest) 6)
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
      | .tagBind tag yes no =>
        let target := if tagHolds tag v then yes else no
        runPrimitive fuel P target.label (PointClaims.mapEnv target.mapping (push v ρ))

private def runRequest (r : SourceRequest) : Option Tm := runPrimitive 100 r.program r.start (fun _ => .nul)

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
#guard ok (do produceSourceJson (toJson (← extractFn (branchFn true) (branchClaims true)).toRequest) 8)
#guard ok (do produceSourceJson (toJson (← extractFn (branchFn false) (branchClaims false)).toRequest) 8)

-- A shared continuation has exactly one return node, with two predecessors
-- reaching its source-expression node. Continuation duplication fails this test.
private def targets : ControlFlow.Continuation → List Nat
  | .ret => []
  | .bind t | .effect t => [t.label]
  | .branch y n | .branchBind y n | .tagBind _ y n => [y.label,n.label]
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
#guard ok (do produceSourceJson (toJson (← extractFn (choiceFn true) (choiceClaims true)).toRequest) 8)
#guard ok (do produceSourceJson (toJson (← extractFn (choiceFn false) (choiceClaims false)).toRequest) 8)

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
#guard ok (do produceSourceJson (toJson (← extractFn (variableFn true) (variableClaims true)).toRequest) 8)
#guard ok (do produceSourceJson (toJson (← extractFn (variableFn false) (variableClaims false)).toRequest) 8)

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
private def runArguments (r : SourceRequest) (vs : List Tm) :=
  runPrimitive 100 r.program r.start (fun i => vs[i]?.getD .nul)
#guard is ((extractFn parameterFn parameterClaims).map (·.inputs)) [[0],[1,2]]
#guard is ((extractFn parameterFn parameterClaims).map (fun r => runArguments r [.nul,.tru])) (some .tru)
#guard is ((extractFn parameterFn parameterClaims).map (fun r => runArguments r [.nul,.fls])) (some .fls)
#guard ok (do produceSourceJson (toJson (← extractFn parameterFn parameterClaims).toRequest) 8)

-- Even if all internal claims consistently narrow the parameter to true,
-- the separate source-signature entry edge must reject that narrowing.
private def narrowedEntry : SourceInput.Claims := { parameterClaims with
  envs := [(2,[("first",(wireTy ⟨false,[.null]⟩)),("second",t)])]
  exprs := [((4,5),t)] }
#guard !ok (do produceSourceJson (toJson (← extractFn parameterFn narrowedEntry).toRequest) 8)

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
  (SourceExtraction.extractFn cellFn cellClaims).map (·.toRequest) |>.toOption.getD (request .nul [0])
#guard ok (SourceExtraction.extractFn cellFn cellClaims)
#guard ok (produceSourceJson (toJson cellRequest) 8)

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

private def functionWire : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "function"),("params",toJson [wireTy ⟨false,[.null]⟩]),
   ("result",wireTy ⟨false,[.bool]⟩),("construct",toJson "unknown"),("array",toJson "unknown")]])]
private def captureFn : SourceInput.Fn :=
  ⟨"capture",(0,1),[],wireTy ⟨false,[.bool]⟩,
    [.cst (2,3) "cell" (some cellWire) (.alloc (4,7) (.lit (5,6) (.vbool true))),
     .cst (8,9) "reader" (some functionWire)
       (.lam (10,15) "unit" (wireTy ⟨false,[.null]⟩) (wireTy ⟨false,[.bool]⟩)
         (.read (12,15) (.var (12,13) "cell"))),
     .cst (16,17) "alias" (some cellWire) (.var (18,19) "cell"),
     .effect (20,25) (.write (20,25) (.var (20,21) "alias") (.lit (24,25) (.vbool false))),
     .ret (26,33) (.app (28,33) (.var (28,29) "reader") (.lit (32,33) .vnull))]⟩
private def captureClaims : SourceInput.Claims :=
  let B := wireTy ⟨false,[.bool]⟩
  ⟨"capture",(0,1),[],B,
   [(2,[]),(8,[("cell",cellWire)]),(16,[("cell",cellWire),("reader",functionWire)]),
    (20,[("cell",cellWire),("reader",functionWire),("alias",cellWire)]),
    (26,[("cell",cellWire),("reader",functionWire),("alias",cellWire)])],
   [((4,7),cellWire),((5,6),t),((10,15),functionWire),((12,15),B),((12,13),cellWire),
    ((18,19),cellWire),((20,25),b),((20,21),cellWire),((24,25),b),
    ((28,33),B),((28,29),functionWire),((32,33),wireTy ⟨false,[.null]⟩)]⟩
private def captureRequest : Request :=
  (SourceExtraction.extractFn captureFn captureClaims).map (·.toRequest) |>.toOption.getD (request .nul [0])
#guard ok (SourceExtraction.extractFn captureFn captureClaims)
#guard ok (produceSourceJson (toJson captureRequest) 10)
private def captureProgram : ControlFlow.Program :=
  [⟨.var 0,.ret⟩, ⟨.app (.var 1) (.var 0),.bind ⟨0,some [0,3,4,5]⟩⟩,
   ⟨.nul,.bind 1⟩, ⟨.var 1,.bind 2⟩,
   ⟨.var 0,.bind ⟨3,some [3,4,5]⟩⟩, ⟨.write (.var 1) (.var 0),.effect 4⟩,
   ⟨.fls,.bind 5⟩, ⟨.var 0,.bind 6⟩, ⟨.var 0,.effect 7⟩, ⟨.var 1,.bind 8⟩,
   ⟨.var 0,.effect 9⟩, ⟨.lam (.read (.var 1)),.bind 10⟩,
   ⟨.var 0,.effect 11⟩, ⟨.alloc (.var 0),.bind ⟨12,some [0]⟩⟩,
   ⟨.tru,.bind 13⟩, ⟨.nul,.effect 14⟩]
#guard captureRequest.program == captureProgram
#guard captureRequest.start == 15

/-- The extracted closure reads after the alias write and returns false.
The graph-equality guards above tie this trace to the source compiler regression. -/
theorem captured_alias_trace : ControlFlow.Execution captureProgram 36 []
    (.at 15 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.allocV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms captured_alias_trace

-- A terminal closure branch adds one conditional step, with each arm occurring
-- once. The condition reads the heap at call time, after the alias write.
private def branchCaptureFn : SourceInput.Fn :=
  { captureFn with body := captureFn.body.map fun st => match st with
    | .cst pos name annot (.lam lp param arg ret body) =>
      .cst pos name annot (.lam lp param arg ret
        (.ifBody (40,49) (some ret) body
          (.atEnv (41,44) (.lit (42,43) (.vbool true)))
          (.atEnv (45,48) (.lit (46,47) (.vbool false)))))
    | st => st }
private def branchCaptureClaims : SourceInput.Claims :=
  let H := [("unit",wireTy ⟨false,[.null]⟩),("cell",cellWire)]
  { captureClaims with
    envs := captureClaims.envs ++ [(40,H),(41,H),(45,H)]
    exprs := captureClaims.exprs ++ [((42,43),t),((46,47),b)] }
private def branchCaptureProgram : ControlFlow.Program :=
  captureProgram.set 11 ⟨.lam (.ite (.read (.var 1)) .tru .fls),.bind 10⟩
#guard is ((extractFn branchCaptureFn branchCaptureClaims).map (·.program)) branchCaptureProgram
#guard ok (do
  let r ← extractFn branchCaptureFn branchCaptureClaims
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

theorem terminal_branch_trace : ControlFlow.Execution branchCaptureProgram 37 []
    (.at 15 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.allocV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.iteC (.readV rfl)))
    | apply ControlFlow.Execution.next (.expr .iteF)
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms terminal_branch_trace

-- Both arms complete before the shared read; the false arm changes the cell
-- to true. Branch-local administrative slots cannot shift the continuation.
private def joinedCaptureFn : SourceInput.Fn :=
  let N := wireTy ⟨false,[.null]⟩
  { captureFn with body := captureFn.body.map fun st => match st with
    | .cst pos name annot (.lam lp param arg ret body) =>
      .cst pos name annot (.lam lp param arg ret
        (.seqBody (40,49)
          (.ifBody (40,49) (some N) body (.done (41,42))
            (.letBody (43,48) "" none
              (.write (44,47) (.var (44,45) "cell") (.lit (46,47) (.vbool true)))
              (.done (48,49))))
          (.atEnv (50,53) (.read (51,53) (.var (51,52) "cell")))))
    | st => st }
private def joinedCaptureClaims : SourceInput.Claims :=
  let H := [("unit",wireTy ⟨false,[.null]⟩),("cell",cellWire)]
  { captureClaims with
    envs := captureClaims.envs ++ [(40,H),(43,H),(50,H)]
    exprs := captureClaims.exprs ++ [((44,47),t),((44,45),cellWire),((46,47),t),
      ((51,53),wireTy ⟨false,[.bool]⟩),((51,52),cellWire)] }
private def joinedCaptureProgram : ControlFlow.Program :=
  let assignment := Tm.app (.lam (.app (.lam (.app (.lam (.var 1))
    (.write (.var 1) (.var 0)))) .tru)) (.var 1)
  captureProgram.set 11 ⟨.lam (.app (.lam (.read (.var 2)))
    (.ite (.read (.var 1)) .nul (.app (.lam .nul) assignment))),.bind 10⟩
#guard is ((extractFn joinedCaptureFn joinedCaptureClaims).map (·.program)) joinedCaptureProgram
#guard ok (do
  let r ← extractFn joinedCaptureFn joinedCaptureClaims
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

theorem shared_continuation_trace : ControlFlow.Execution joinedCaptureProgram 44 []
    (.at 15 (fun _ => .nul)) [.tru] (.done .tru) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.allocV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.iteC (.readV rfl))))
    | apply ControlFlow.Execution.next (.expr (.appR rfl .iteF))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.appR rfl (.beta rfl))))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.appR rfl (.appR rfl (.writeV rfl (by decide))))))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.beta rfl)))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms shared_continuation_trace

-- The same extracted conditional must skip its continuation on early return.
private def earlyCaptureFn (q : Bool) : SourceInput.Fn :=
  { captureFn with body := captureFn.body.map fun st => match st with
    | .cst pos name annot (.lam lp param arg ret body) =>
      .cst pos name annot (.lam lp param arg ret
        (.ifBody (40,59) (some ret) body
          (.atEnv (41,44) (.lit (42,43) (.vbool true)))
          (.seqBody (45,59)
            (.letBody (45,50) "" none
              (.write (46,49) (.var (46,47) "cell") (.lit (48,49) (.vbool false)))
              (.done (50,51)))
            (.atEnv (52,55) (.read (53,55) (.var (53,54) "cell"))))))
    | .effect pos (.write wp receiver (.lit lp _)) =>
      .effect pos (.write wp receiver (.lit lp (.vbool q)))
    | st => st }
private def earlyCaptureClaims (q : Bool) : SourceInput.Claims :=
  let H := [("unit",wireTy ⟨false,[.null]⟩),("cell",cellWire)]
  { captureClaims with
    envs := captureClaims.envs ++ [(40,H),(41,H),(45,H),(52,H)]
    exprs := (captureClaims.exprs.map fun (pos,A) =>
      (pos,if pos == (24,25) || pos == (20,25) then (if q then t else b) else A)) ++
      [((42,43),t),((46,49),b),((46,47),cellWire),((48,49),b),
       ((53,55),wireTy ⟨false,[.bool]⟩),((53,54),cellWire)] }
private def earlyCaptureProgram (q : Bool) : ControlFlow.Program :=
  let assignment := Tm.app (.lam (.app (.lam (.app (.lam (.var 1))
    (.write (.var 1) (.var 0)))) .fls)) (.var 1)
  (captureProgram.set 6 ⟨if q then .tru else .fls,.bind 5⟩).set 11
    ⟨.lam (.ite (.read (.var 1)) .tru
      (.app (.lam (.read (.var 2))) (.app (.lam .nul) assignment))),.bind 10⟩
#guard [true,false].all fun q =>
  is ((extractFn (earlyCaptureFn q) (earlyCaptureClaims q)).map (·.program)) (earlyCaptureProgram q)
#guard [true,false].all fun q => ok (do
  let r ← extractFn (earlyCaptureFn q) (earlyCaptureClaims q)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

theorem early_return_trace (q : Bool) : ControlFlow.Execution (earlyCaptureProgram q)
    (if q then 37 else 44) [] (.at 15 (fun _ => .nul))
    [if q then .tru else .fls] (.done (if q then .tru else .fls)) := by
  cases q <;> repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.allocV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.iteC (.readV rfl)))
    | apply ControlFlow.Execution.next (.expr .iteT)
    | apply ControlFlow.Execution.next (.expr .iteF)
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.appR rfl (.beta rfl))))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.appR rfl (.appR rfl (.writeV rfl (by decide))))))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.beta rfl)))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms early_return_trace

-- Supplemental proofs are necessary even when the whole lambda is typable.
private def captureRequired := (extractFn captureFn captureClaims).toOption.getD ⟨captureRequest,[],[],[],[]⟩
#guard captureRequired.obligations.length == 4
#guard ok (ExpressionClaims.produce (RequestJson.graph captureRequest)
  captureRequired.searchLabels captureRequest.types.length 10 captureRequired.obligations)
private def narrowedCapture : SourceInput.Claims :=
  { captureClaims with exprs := captureClaims.exprs.map fun (pos,ty) =>
    (pos, if pos == (12,15) then t else ty) }
#guard ok (do produceSourceJson (toJson (← extractFn captureFn narrowedCapture).toRequest) 10)
#guard !ok (do
  let r ← extractFn captureFn narrowedCapture
  ExpressionClaims.produce (RequestJson.graph r.toRequest) r.searchLabels r.types.length 10 r.obligations)

private def writerFn : SourceInput.Fn :=
  ⟨"writer",(0,1),[],wireTy ⟨false,[.bool]⟩,
    [.cst (2,3) "cell" (some cellWire) (.alloc (4,7) (.lit (5,6) (.vbool true))),
     .cst (8,9) "writer" (some functionWire)
       (.lam (10,19) "unit" (wireTy ⟨false,[.null]⟩) (wireTy ⟨false,[.bool]⟩)
         (.write (12,19) (.var (12,13) "cell") (.lit (18,19) (.vbool false)))),
     .ret (20,27) (.app (22,27) (.var (22,23) "writer") (.lit (26,27) .vnull))]⟩
private def writerClaims : SourceInput.Claims :=
  ⟨"writer",(0,1),[],wireTy ⟨false,[.bool]⟩,
   [(2,[]),(8,[("cell",cellWire)]),(20,[("cell",cellWire),("writer",functionWire)])],
   [((4,7),cellWire),((5,6),t),((10,19),functionWire),((12,19),b),
    ((12,13),cellWire),((18,19),b),((22,27),wireTy ⟨false,[.bool]⟩),
    ((22,23),functionWire),((26,27),wireTy ⟨false,[.null]⟩)]⟩
private def writerProgram : ControlFlow.Program :=
  [⟨.var 0,.ret⟩, ⟨.app (.var 1) (.var 0),.bind ⟨0,some [0,3,4]⟩⟩,
   ⟨.nul,.bind 1⟩, ⟨.var 0,.bind 2⟩, ⟨.var 0,.effect 3⟩,
   ⟨.lam (.app (.lam (.app (.lam (.app (.lam (.var 1))
       (.write (.var 1) (.var 0)))) .fls)) (.var 1)),.bind 4⟩,
   ⟨.var 0,.effect 5⟩, ⟨.alloc (.var 0),.bind ⟨6,some [0]⟩⟩,
   ⟨.tru,.bind 7⟩, ⟨.nul,.effect 8⟩]
#guard is ((extractFn writerFn writerClaims).map (·.program)) writerProgram
#guard is ((extractFn writerFn writerClaims).map (·.start)) 9
#guard ok (do
  let r ← extractFn writerFn writerClaims
  let _ ← produceSourceJson (toJson r.toRequest) 10
  ExpressionClaims.produce (RequestJson.graph r.toRequest) r.searchLabels r.types.length 10 r.obligations)

/-- Calling the extracted writer changes the heap and returns its RHS, not null. -/
theorem closure_write_trace : ControlFlow.Execution writerProgram 26 []
    (.at 9 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.allocV rfl))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.writeV rfl (by decide))))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms closure_write_trace

-- A single-return block has the same execution as its expression body, but
-- adds proof obligations for the supplied statement environment.
private def blockCaptureFn : SourceInput.Fn :=
  { captureFn with body := captureFn.body.map fun st => match st with
    | .cst pos name annot (.lam lp param arg ret body) =>
      .cst pos name annot (.lam lp param arg ret (.atEnv (11,16) body))
    | st => st }
private def blockCaptureClaims (unitTy : Json) : SourceInput.Claims :=
  { captureClaims with envs := captureClaims.envs ++
    [(11,[("unit",unitTy),("cell",cellWire)])] }
#guard is ((extractFn blockCaptureFn (blockCaptureClaims (wireTy ⟨false,[.null]⟩))).map
  (·.program)) captureProgram
private def blockObligations (unitTy : Json) : Except String Unit := do
  let r ← extractFn blockCaptureFn (blockCaptureClaims unitTy)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 10 r.obligations
  pure ()
#guard ok (blockObligations (wireTy ⟨false,[.null]⟩))
-- Forgetting parameter precision is allowed; inventing an unused type is not.
#guard ok (blockObligations (wireTy ⟨false,[.null,.bool]⟩))
#guard !ok (blockObligations t)
#guard !ok (extractFn blockCaptureFn captureClaims)

private def localWriterFn : SourceInput.Fn :=
  { writerFn with body := writerFn.body.map fun st => match st with
    | .cst pos name annot (.lam lp param arg ret _) =>
      .cst pos name annot (.lam lp param arg ret
        (.letBody (30,31) "saved" (some (wireTy ⟨false,[.bool]⟩))
          (.lit (32,33) (.vbool false))
          (.letBody (34,35) "" none
            (.write (36,39) (.var (36,37) "cell") (.var (38,39) "saved"))
            (.atEnv (40,43) (.read (41,43) (.var (41,42) "cell"))))))
    | st => st }
private def localWriterClaims : SourceInput.Claims :=
  let N := wireTy ⟨false,[.null]⟩
  let B := wireTy ⟨false,[.bool]⟩
  { writerClaims with
    envs := writerClaims.envs ++
      [(30,[("unit",N),("cell",cellWire)]),
       (34,[("unit",N),("cell",cellWire),("saved",B)]),
       (40,[("unit",N),("cell",cellWire),("saved",B)])]
    exprs := writerClaims.exprs ++
      [((32,33),b),((36,39),B),((36,37),cellWire),((38,39),B),
       ((41,43),B),((41,42),cellWire)] }
private def localWriterProgram : ControlFlow.Program :=
  let write : Tm := .app (.lam (.app (.lam (.app (.lam (.var 1))
    (.write (.var 1) (.var 0)))) (.var 1))) (.var 2)
  writerProgram.set 5
    ⟨.lam (.app (.lam (.app (.lam (.read (.var 3))) write)) .fls),.bind 4⟩
#guard is ((extractFn localWriterFn localWriterClaims).map (·.program)) localWriterProgram

/-- A saved local is used by the write and survives the anonymous effect slot. -/
theorem local_writer_trace : ControlFlow.Execution localWriterProgram 29 []
    (.at 9 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.allocV rfl))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.beta rfl)))
    | apply ControlFlow.Execution.next (.expr (.appR rfl (.appR rfl (.writeV rfl (by decide)))))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms local_writer_trace

-- A suggested intermediate type cannot turn false into true.
#guard !(CertificateProducer.expressionWith G0 [[1],[2],[1,2]]
  [⟨[],.fls,[1]⟩] 4 [] (.app (.lam (.var 0)) .fls) [1]).isSome

-- Direct recipes preserve supplied types while rebuilding proofs in the actual context.
private def widenedVariable := DirectProof.var [[1,2]] 0 [1,2]
#guard ((DirectProof.render G0 [[1],[2],[1,2]] [[2]] widenedVariable).map
  (fun e => ProgramCertificates.checkTree G0 e)) == some true
#guard !(DirectProof.render G0 [[1],[2],[1,2]] [[2]]
  (DirectProof.var [[1]] 0 [1])).isSome

-- All supported closure obligations now have recipes and require no expression-search fuel.
#guard ok (do
  let r ← extractFn localWriterFn localWriterClaims
  if r.obligations.any (fun q => q.plan.isNone) then throw "missing recipe"
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

-- A forged recipe or reused certificate is still rejected by the ordinary checker.
private def forged : ProgramCertificates.Evidence Nat :=
  .node ⟨[],.fls,[1]⟩ .truLit []
#guard !ok (produceSourceJson (toJson (request .fls [1])) 4 [] [forged])
#guard !ok (ExpressionClaims.produce G0 [0,1,2,3] SourceTypes.initial.length 4
  [⟨(0,1),⟨[],.fls,[1]⟩,some (DirectProof.node [] .fls [1] .truLit),"expression-claim",[]⟩])

-- Source unions compose already-supported atoms, preserving every arm's checks.
-- Each compound arm is interned once, at the first free label.
private def joined (types : List Json) : Json := Json.mkObj [
  ("top",toJson false), ("atoms",toJson (types.flatMap fun j =>
    ((jArr j "atoms").toOption.getD [])))]
private def lowered (j : Json) : Except String (Ty Nat) :=
  (SourceInput.translate j).run' SourceTypes.initial
#guard is (lowered (joined [wireTy ⟨false,[.null]⟩,cellWire])) [0,4]
#guard is (lowered (joined [cellWire,wireTy ⟨false,[.null]⟩,cellWire])) [0,4]
#guard is (lowered (joined [wireTy ⟨false,[.null]⟩,functionWire])) [0,4]
#guard is (lowered (joined [cellWire,functionWire])) [4,5]
#guard !ok (lowered (joined [cellWire,wireTy ⟨false,[.str]⟩]))
#guard !ok (lowered (Json.mkObj [("top",toJson true),("atoms",toJson ([] : List Json))]))

-- Mixed unions do not bypass the external-object/callable origin boundary.
#guard (match extractFn
    { branchFn true with params := [⟨"external",joined [wireTy ⟨false,[.null]⟩,cellWire]⟩] }
    { branchClaims true with params := [("external",joined [wireTy ⟨false,[.null]⟩,cellWire])] } with
  | .error e => e == "cell parameters need an external-value boundary, which is outside the source slice"
  | .ok _ => false)
#guard !ok (lowered (joined [wireTy ⟨false,[.str]⟩,cellWire]))

-- A graph-safe certificate can still violate the source's local interfaces.
-- This specifically tests the consumer, independently of producer scheduling.
private def localFn : SourceInput.Fn :=
  ⟨"local",(0,1),[],wireTy ⟨false,[.boolLit true]⟩,
    [.cst (2,3) "x" (some (wireTy ⟨false,[.bool]⟩)) (.lit (4,5) (.vbool true)),
     .ret (6,9) (.var (8,9) "x")]⟩
private def localClaims : SourceClaims.Function := {
  name := "local", namePos := (0,1), params := [], ret := .ok [1]
  envs := [(2,[]),(6,[("x",.ok [1,2])])]
  exprs := [((4,5),.ok [1]),((8,9),.ok [1,2])] }
private def localRequest := (extractNormalizedFn SourceTypes.initial localFn localClaims).toOption.getD ⟨request .nul [0],[],[],[],[]⟩
private def localCertificate (cuts : List Nat) :=
  CertificateProducer.produce (RequestJson.graph localRequest.toRequest)
    localRequest.searchLabels 8 localRequest.result localRequest.program localRequest.claims
    localRequest.start [] localRequest.inputs [] [] localRequest.assertions cuts
private def globalCertificate := (localCertificate []).toOption.get!
#guard RequestJson.verify localRequest.toRequest ⟨globalCertificate⟩
#guard !checkAssertions localRequest ⟨globalCertificate⟩
#guard (localCertificate localRequest.cuts).toOption.isNone
private def repairedLocal := (extractNormalizedFn SourceTypes.initial localFn
  {localClaims with envs := [(2,[]),(6,[("x",.ok [1])])]}).toOption.getD ⟨request .nul [0],[],[],[],[]⟩
#guard ok (RequestJson.produceJson (toJson repairedLocal.toRequest) 8 [] []
  repairedLocal.sourceMap (some repairedLocal.searchLabels) repairedLocal.assertions repairedLocal.cuts)

-- Conjunction is one row whatever its arity. Reference operands are sorted and
-- deduplicated, so a repeated contract is the plain cell; overload order is
-- kept, so the two spellings of an arrow pair are two rows.
private def conjoined (j : Json) (others : List Json) : Json :=
  let atom := ((jArr j "atoms").toOption.getD []).headD .null
  let more := others.map fun o => ((jArr o "atoms").toOption.getD []).headD .null
  Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
    (((atom.getObj?).toOption.map (·.toList)).getD [] ++ [("and",toJson more)])])]
private def cellOf (A : Wire.Ty) : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "record"),("fields",toJson [Json.mkObj [("name",toJson "value"),
    ("optional",toJson false),("read",wireTy A),("write",wireTy A)]]),
   ("indexes",Json.mkObj [("string",toJson "absent"),("number",toJson "absent"),("symbol",toJson "absent")]),
   ("call",toJson "unknown"),("construct",toJson "unknown"),("array",toJson "unknown")]])]
private def arrowOf (D R : Wire.Ty) : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "function"),("params",toJson [wireTy D]),
   ("result",wireTy R),("construct",toJson "unknown"),("array",toJson "unknown")]])]
private def rowOf (j : Json) : Option (List (Clause (List Nat))) :=
  ((SourceInput.translate j).run SourceTypes.initial).toOption.bind fun (A,T) => A.head?.bind (T[·]?)
#guard rowOf (conjoined cellWire [cellWire,cellWire]) == some [.refs [1,2] []]
#guard rowOf (conjoined (cellOf ⟨false,[.boolLit true]⟩) [cellOf ⟨false,[.null]⟩,cellOf ⟨false,[.bool]⟩])
  == some [.refs [0] [[1],[1,2]]]
#guard rowOf (conjoined (cellOf ⟨false,[.bool]⟩) [cellOf ⟨false,[.null]⟩,cellOf ⟨false,[.boolLit true]⟩])
  == some [.refs [0] [[1],[1,2]]]
private def trueToNull := arrowOf ⟨false,[.boolLit true]⟩ ⟨false,[.null]⟩
private def falseToNull := arrowOf ⟨false,[.boolLit false]⟩ ⟨false,[.null]⟩
#guard rowOf (conjoined trueToNull [falseToNull]) == some [.arrs [([1],[0]),([2],[0])]]
#guard rowOf (conjoined falseToNull [trueToNull]) == some [.arrs [([2],[0]),([1],[0])]]
#guard rowOf (conjoined trueToNull [trueToNull]) == some [.arrs [([1],[0])]]

-- A lambda claimed at two signatures is proved once per signature; the call
-- resolves to the first signature admitting its argument.
private def overloadWire := conjoined trueToNull [falseToNull]
private def overloadFn : SourceInput.Fn :=
  ⟨"overload",(0,1),[],wireTy ⟨false,[.null]⟩,
    [.cst (2,3) "f" (some overloadWire)
      (.lam (4,9) "x" (wireTy ⟨false,[.bool]⟩) (wireTy ⟨false,[.null]⟩) (.lit (8,9) .vnull)),
     .ret (10,17) (.app (12,17) (.var (12,13) "f") (.lit (14,15) (.vbool true)))]⟩
private def overloadClaims : SourceInput.Claims :=
  ⟨"overload",(0,1),[],wireTy ⟨false,[.null]⟩,[(2,[]),(10,[("f",overloadWire)])],
   [((4,9),overloadWire),((8,9),wireTy ⟨false,[.null]⟩),((12,17),wireTy ⟨false,[.null]⟩),
    ((12,13),overloadWire),((14,15),t)]⟩
#guard ok (extractFn overloadFn overloadClaims)
#guard ok (do
  let r ← extractFn overloadFn overloadClaims
  let j := toJson r.toRequest
  verifyJson j (← produceSourceJson j 10)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest) r.searchLabels r.types.length 0 r.obligations
  pure ())
-- A claimed signature outside the annotated parameter is refused.
#guard (match extractFn
    { overloadFn with body := [.cst (2,3) "f" (some overloadWire)
      (.lam (4,9) "x" (wireTy ⟨false,[.boolLit true]⟩) (wireTy ⟨false,[.null]⟩) (.lit (8,9) .vnull)),
      .ret (10,17) (.app (12,17) (.var (12,13) "f") (.lit (14,15) (.vbool true)))] } overloadClaims with
  | .error e => e == "closure signature claim is outside the source annotation"
  | .ok _ => false)
-- An argument no signature admits fails the call's claim, not silently.
#guard !ok (do
  let r ← extractFn { overloadFn with body := [.cst (2,3) "f" (some overloadWire)
      (.lam (4,9) "x" (wireTy ⟨false,[.bool]⟩) (wireTy ⟨false,[.null]⟩) (.lit (8,9) .vnull)),
      .ret (10,17) (.app (12,17) (.var (12,13) "f") (.lit (14,15) .vnull))] }
    { overloadClaims with exprs := overloadClaims.exprs.map fun (pos,ty) =>
      (pos, if pos == (14,15) then wireTy ⟨false,[.null]⟩ else ty) }
  produceSourceJson (toJson r.toRequest) 8)

-- An arrow parameter is assumed at its annotation and may be called; a claim
-- that contradicts the annotation is refused by name, and a cell parameter is
-- still outside the slice.
private def callerFn : SourceInput.Fn :=
  ⟨"caller",(0,1),[⟨"a",trueToNull⟩],wireTy ⟨false,[.null]⟩,
    [.ret (2,9) (.app (4,9) (.var (4,5) "a") (.lit (6,7) (.vbool true)))]⟩
private def callerClaims : SourceInput.Claims :=
  ⟨"caller",(0,1),[("a",trueToNull)],wireTy ⟨false,[.null]⟩,[(2,[("a",trueToNull)])],
   [((4,9),wireTy ⟨false,[.null]⟩),((4,5),trueToNull),((6,7),t)]⟩
#guard is ((extractFn callerFn callerClaims).map (·.inputs.length)) 1
#guard ok (do
  let r ← extractFn callerFn callerClaims
  let j := toJson r.toRequest
  verifyJson j (← produceSourceJson j 8))
#guard (match extractFn callerFn { callerClaims with params := [("a",wireTy ⟨false,[]⟩)] } with
  | .error e => e == "claimed parameter type differs from the source annotation for 'a'"
  | .ok _ => false)
#guard !ok (extractFn { callerFn with params := [⟨"a",cellWire⟩] } { callerClaims with params := [("a",cellWire)] })

end Verification.ExperimentState.SourceExtractionTests
