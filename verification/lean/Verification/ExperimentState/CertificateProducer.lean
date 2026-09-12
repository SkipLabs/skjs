import Verification.ExperimentState.ControlFlow

/-! Bounded, untrusted evidence search. Supplied point claims are immutable.
Search fuel and the finite type vocabulary affect success, never acceptance.
The final consumer checks the actual program and exact supplied claims again. -/
namespace Verification.ExperimentState.CertificateProducer
open ProgramTyping PositiveGraphs PositiveNormalization PositiveRules
open ProgramCertificates PointClaims ControlFlow

structure PointClaim (ι : Type) where
  context : List (Ty ι)
  type : Ty ι
  deriving DecidableEq, Repr

def signature (c : NodeEvidence ι) : PointClaim ι := ⟨entry c, result c⟩

/-- Claims are part of the request, not facts the producer may replace. -/
def accept [DecidableEq ι] (G : NormalGraph ι) (R : Ty ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι) := []) : Bool :=
  decide (C.map signature = claims) && checkEntry G R P C start inputs

theorem accept_claims [DecidableEq ι] {G : NormalGraph ι} {R P claims C start inputs}
    (hc : accept G R P claims C start inputs = true) : C.map signature = claims :=
  by
    simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {R P claims C start}
    (hc : accept G R P claims C start = true) (n : Nat) :
    SafeGraph P (meaning G R) n (ofList []) [] (.at start (fun _ => .nul)) :=
  by
    simp only [accept, Bool.and_eq_true] at hc
    exact accepted_closed_safe hc.2 n

theorem accepted_from_inputs [DecidableEq ι] {G : NormalGraph ι} {R P claims C start inputs}
    (hc : accept G R P claims C start inputs = true) (n W h ρ)
    (he : EnvOk G inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph P (meaning G R) n W h (.at start ρ) := by
  simp only [accept, Bool.and_eq_true] at hc
  exact ControlFlow.accepted_inputs_safe hc.2 n W h ρ he hw hh

/-- Small arrow search: source, domain union, and pairwise compatible codomain
combination. The checker, not this search strategy, defines the rules. -/
def arrowSearch [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (L : Ops ι)
    (c d : Ty ι) : Nat → Option (PositiveCertificates.ArrowCert ι)
  | 0 => none
  | fuel+1 => Id.run do
    let basic := PositiveCertificates.ArrowCert.empty :: L.map (.source ·)
    if let some p := basic.find? (fun p => PositiveCertificates.checkArrow G table L c d p) then
      return some p
    if let a :: rest := c then
      if !rest.isEmpty then
        if let some left := arrowSearch G table L [a] d fuel then
          if let some right := arrowSearch G table L rest d fuel then
            let p := PositiveCertificates.ArrowCert.union [a] rest left right
            if PositiveCertificates.checkArrow G table L c d p then return some p
    return (L.flatMap fun p => L.map fun q =>
      PositiveCertificates.ArrowCert.combine p.2 q.2 (.source p) (.source q)).find?
        (fun p => PositiveCertificates.checkArrow G table L c d p)

def arrowEvidence [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (pool : List (Ty ι)) : PositiveCertificates.Evidence ι :=
  let clauses := pool.flatMap (expand G)
  clauses.flatMap fun a => match a with
    | .arrs L | .callable _ _ L => clauses.flatMap fun b => match b with
      | .arrs M | .callable _ _ M => M.filterMap fun p =>
          (arrowSearch G table L p.1 p.2 (p.1.length+1)).map (fun proof => (L,(p,proof)))
      | _ => []
    | _ => []

/-- Delete unsupported rows of a finite candidate relation. A surviving cyclic
relation is only proposed evidence; checkCore validates every row. -/
def prune [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι)) :
    Nat → Table ι → Table ι
  | 0, table => table
  | fuel+1, table =>
    let es := arrowEvidence G table pool
    let next := table.filter fun p => (sourceClauses G p.1).all fun a =>
      (expand G p.2).any fun b => PositiveCertificates.checkClause G table es a b
    if next = table then table else prune G pool fuel next

def subtype [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (A B : Ty ι) : Option (PositiveCertificates.Proof ι) :=
  if PositiveCertificates.check G A B .subset then some .subset else
    let types := (A :: B :: pool).eraseDups
    let initial := types.flatMap fun a => types.map (a, ·)
    let table := prune G types initial.length initial
    let p := PositiveCertificates.Proof.core ⟨table, arrowEvidence G table types⟩
    if PositiveCertificates.check G A B p then some p else none

def coerce [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (e : ProgramCertificates.Evidence ι) (A : Ty ι) : Option (ProgramCertificates.Evidence ι) := do
  if (claim e).type = A then return e
  let p ← subtype G pool (claim e).type A
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

instance [DecidableEq ι] (G : NormalGraph ι) (B : Ty ι) (tag : Tag) (q : Bool) :
    Decidable (Answers G B tag q) := by unfold Answers; infer_instance

/-- Search ordinary typing rules. Every recursive expression request decreases
search fuel, including implicit let typing. Suggestions only prioritize candidate
types; every premise is proved in the actual context, even when the suggestion
came from a different context. No execution budget is inspected. -/
def expressionWith [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (suggestions : List (Sequent ι)) :
    Nat → List (Ty ι) → Tm → Ty ι → Option (ProgramCertificates.Evidence ι)
  | 0, _, _, _ => none
  | fuel+1, Γ, t, A => Id.run do
    let leaf := fun B r => ProgramCertificates.Evidence.node ⟨Γ,t,B⟩ r []
    let recur := expressionWith G pool suggestions fuel
    -- Union elimination refines an immutable receiver slot in each premise;
    -- it neither evaluates the operation twice nor inserts a runtime tag test.
    let splitReceiver := fun receiver => do
      let .var i := receiver | none
      let B ← Γ[i]?
      if B.length ≤ 1 then none else do
        let ps ← B.mapM fun b => recur (Γ.set i [b]) t A
        pure (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    match t with
    | .var i => return (Γ[i]?).bind fun B => coerce G pool (leaf B .var) A
    | .nul | .undef | .tru | .fls =>
      let r := match t with | .nul => Rule.nul | .undef => .undef | .tru => .tru | _ => .fls
      return (A :: pool).findSome? fun B =>
        let r := if expand G B = [.boolLit true] && t == .tru then Rule.truLit
          else if expand G B = [.boolLit false] && t == .fls then Rule.flsLit else r
        if checkTree G (leaf B r) then coerce G pool (leaf B r) A else none
    | .funE b =>
      return (A :: pool).findSome? fun F => do
        match expand G F with
        | [.arrs L] =>
          let ps ← L.mapM fun p => recur (p.1 :: Γ) b p.2
          coerce G pool (.node ⟨Γ,t,F⟩ .funE ps) A
        | [.callable P [] L] =>
          let ea ← recur Γ .nul P
          let ps ← L.mapM fun p => recur (p.1 :: Γ) b p.2
          coerce G pool (.node ⟨Γ,t,F⟩ .makeCallable (ea :: ps)) A
        | _ => none
    | .attach b a =>
      return (A :: pool).findSome? fun F => do
        let [.callable P [] L] := expand G F | none
        let ea ← recur Γ a P
        let ps ← L.mapM fun p => recur (p.1 :: Γ) b p.2
        coerce G pool (.node ⟨Γ,t,F⟩ .makeCallable (ea :: ps)) A
    | .letE a b =>
      let exactTypes := suggestions.reverse.filterMap fun j =>
        if j.context == Γ && j.term == a then some j.type else none
      let termTypes := suggestions.reverse.filterMap fun j =>
        if j.term == a then some j.type else none
      let variableType := match a with | .var i => (Γ[i]?).toList | _ => []
      let preferred := variableType ++ exactTypes ++ termTypes
      return (preferred ++ pool).eraseDups.findSome? (fun B => do
        let ea ← recur Γ a B
        let eb ← recur (B :: Γ) b A
        return ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ .letE [ea,eb])
    | .app f a =>
      return pool.findSome? fun F => do
        let (L,r) ← match expand G F with
          | [.arrs L] => some (L,Rule.app)
          | [.callable _ _ L] => some (L,Rule.callCallable)
          | _ => none
        L.findSome? fun p => do
          -- Check the result relation before searching both premises.
          let _ ← subtype G pool p.2 A
          let ef ← recur Γ f F
          let ea ← recur Γ a p.1
          coerce G pool (.node ⟨Γ,t,p.2⟩ r [ef,ea]) A
    | .alloc a =>
      return (A :: pool).findSome? fun R => do
        let [.refs B []] := expand G R | none
        let ea ← recur Γ a B
        coerce G pool (.node ⟨Γ,t,R⟩ .alloc [ea]) A
    | .read a =>
      let direct := pool.findSome? fun R => do
        let (B,r) ← match expand G R with
          | [.refs B []] => some (B,Rule.read)
          | [.callable B _ _] => some (B,Rule.readCallable)
          | _ => none
        let _ ← subtype G pool B A
        let ea ← recur Γ a R
        coerce G pool (.node ⟨Γ,t,B⟩ r [ea]) A
      if let some e := direct then return some e
      return splitReceiver a
    | .write a b =>
      let direct := pool.findSome? fun R => do
        let (B,r) ← match expand G R with
          | [.refs B []] => some (B,Rule.write)
          | [.callable B _ _] => some (B,Rule.writeCallable)
          | _ => none
        let ea ← recur Γ a R
        let eb ← recur Γ b B
        (A :: pool).findSome? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ r [ea,eb]
          if checkTree G e then coerce G pool e A else none
      if let some e := direct then return some e
      return splitReceiver a
    | .ite (.test tag (.var i)) u e =>
      let some B := Γ[i]? | return none
      if decide (Answers G B tag true) then
        return (recur Γ u A).map fun p => .node ⟨Γ,t,A⟩ .ifTrue [p]
      if decide (Answers G B tag false) then
        return (recur Γ e A).map fun p => .node ⟨Γ,t,A⟩ .ifFalse [p]
      -- Split only an explicit union. A singleton whose graph clause itself
      -- mixes shapes is not made smaller by repeating this rule.
      if B.length ≤ 1 then return none
      return do
        let ps ← B.mapM fun a => recur (Γ.set i [a]) t A
        pure (.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    | .ite c t e =>
      let known := pool.findSome? fun C => do
        let [.boolLit q] := expand G C | none
        let pc ← recur Γ c C
        let pb ← recur Γ (if q then t else e) A
        pure (.node ⟨Γ,.ite c t e,A⟩ (.ifKnown q) [pc,pb])
      if let some p := known then return some p
      let refined := do
        let .var i := c | none
        let C ← Γ[i]?
        if !decide (Answers G C .isBool true) then none else do
          let T ← pool.find? fun T => decide (expand G T = [.boolLit true])
          let F ← pool.find? fun F => decide (expand G F = [.boolLit false])
          let pt ← recur (Γ.set i T) t A
          let pe ← recur (Γ.set i F) e A
          pure (.node ⟨Γ,.ite c t e,A⟩ (.ifBoolVar T F) [pt,pe])
      if let some p := refined then return some p
      return pool.findSome? fun C => do
        if !decide (Answers G C .isBool true) then none else do
          let pc ← recur Γ c C
          let pt ← recur Γ t A
          let pe ← recur Γ e A
          pure (.node ⟨Γ,.ite c t e,A⟩ .ifBool [pc,pt,pe])
    | _ => return none

/-- Raw calculus callers need not supply source-derived search suggestions. -/
def expression [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι)) :=
  expressionWith G pool []

/-- Gather graph labels, recursive operands and supplied union types. Hints may
add intermediate types; they cannot change claims or bypass evidence checking. -/
def vocabulary [DecidableEq ι] (G : NormalGraph ι) (labels : List ι)
    (claims : List (PointClaim ι)) (hints : List (Ty ι)) : List (Ty ι) :=
  ([] :: (labels.map fun i => [i]) ++ hints ++
    claims.flatMap (fun c => c.type :: c.context) ++
    labels.flatMap (fun i => (G i).flatMap fun c => match c with
      | .refs A bs => A :: bs
      | .arrs L => L.flatMap fun p => [p.1,p.2]
      | .callable A bs L => A :: bs ++ L.flatMap (fun p => [p.1,p.2])
      | _ => [])).eraseDups

inductive Failure where
  | claimCount
  | expression (label : Nat)
  | edge (source : Nat) (destination : Nat) (edgeIndex : Nat)
  | rejected
  deriving DecidableEq, Repr

/-- Ordinary and observed edges share slot selection and coverage search. The
observation comes from graph dispatch, never from supplied point annotations. -/
def edge [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (claims : List (PointClaim ι)) (Γ : List (Ty ι)) (target : Target)
    (observed : Option (Nat × BranchRefinement.Observation) := none) :
    Option (EdgeEvidence ι) := do
  let c ← claims[target.label]?
  if let some (tested, _) := observed then
    if Γ[tested]?.isNone then failure
  if let some slots := target.mapping then
    if slots.length != c.context.length then failure
  (List.range c.context.length).mapM fun i => do
    let A ← Γ[slot target.mapping i]?
    let B ← c.context[i]?
    match observed with
    | some (tested, o) =>
      if slot target.mapping i == tested then
        match o with
        | .boolean q =>
          if BranchRefinement.booleanMember G B q then pure .subset else failure
        | .tag t q => subtype G pool (BranchRefinement.tagSlice G A t q) B
      else subtype G pool A B
    | none => subtype G pool A B


/-- Select effect evidence without changing the requested sequent. A precise
read/value rule may succeed when ordinary derivation search cannot. -/
def expressionEffect [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (fuel : Nat) (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (suggestions : List (Sequent ι)) (known : List (Evidence ι)) :
    Option (Evidence ι × HeapExpressionRules.StepEvidence ι × HeapKnowledge.Knowledge) := Id.run do
  let ordinary := (known.find? fun e => claim e == j).orElse fun _ =>
    expressionWith G pool suggestions fuel j.context j.term j.type
  let mut choices : List (HeapExpressionRules.StepEvidence ι) := []
  match j.term with
  | .var i =>
    if let some R := HeapExpressionRules.valuesAt G j.context k i then
      choices := [.knownValue i R]
  | .read (.var i) =>
    choices := (k.cells.filter fun f => f.slot == i).map fun f => .observedRead i f.contents
  | _ => pure ()
  if let some e := ordinary then
    match j.term with
    | .read (.var i) =>
      if let some Ref := j.context[i]? then
        if let some B := HeapExpressionRules.bagOperand (expand G Ref) then
          choices := choices ++ [.typedRead i B e]
    | .make _ (.var i) =>
      if let some R := HeapExpressionRules.valuesAt G j.context k i then
        choices := choices ++ [.allocated i R e]
    | .write (.var i) (.var v) =>
      if let some R := HeapExpressionRules.valuesAt G j.context k v then
        choices := choices ++ [.written i v R e]
    | _ => pure ()
    choices := choices ++ [.created e,.pure e,.ordinary e]
  for effect in choices do
    if let some out := HeapExpressionRules.checkStep G j k effect then
      -- Effect evidence validates this header itself; an ordinary derivation
      -- is not required for the precise read/value alternatives.
      return some (ordinary.getD (.node j .var []),effect,out)
  return none

/-- All predecessor edges come from executable continuations. -/
def successors : Continuation → List Target
  | .ret => []
  | .bind t | .effect t => [t]
  | .branch y n | .branchBind y n | .tagBind _ y n => [y,n]

def edgeKnowledge (k : HeapKnowledge.Knowledge) (cont : Continuation) (index : Nat) :
    HeapKnowledge.Knowledge :=
  match cont with
  | .effect _ | .branch _ _ => HeapKnowledge.dropResult k
  | .branchBind _ _ => HeapKnowledge.observe k 0 (.boolean (index == 0))
  | .tagBind t _ _ => HeapKnowledge.observe k 0 (.tag t (index == 0))
  | _ => k

private def produceNode [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (fuel l : Nat) (node : Node) (claims : List (PointClaim ι))
    (k : HeapKnowledge.Knowledge) (suggestions : List (Sequent ι)) (known : List (Evidence ι)) :
    Except Failure (NodeEvidence ι) := do
  let some c := claims[l]? | throw .claimCount
  let some (e,effect,out) := expressionEffect G pool fuel ⟨c.context,node.expression,c.type⟩ k suggestions known
    | throw (.expression l)
  let target := fun Γ t index => match edge G pool claims Γ t with
    | some p => Except.ok p
    | none => Except.error (Failure.edge l t.label index)
  let branchTarget := fun Γ o t index => match edge G pool claims Γ t (some (0, o)) with
    | some p => Except.ok p
    | none => Except.error (Failure.edge l t.label index)
  let ps ← (match node.continuation with
    | .ret => pure []
    | .bind t => (target (c.type :: c.context) t 0).map (fun p => [p])
    | .effect t => (target c.context t 0).map (fun p => [p])
    | .branch y n => (target c.context y 0).bind (fun py =>
        (target c.context n 1).map (fun pn => [py,pn]))
    | .branchBind y n => (branchTarget (c.type :: c.context) (.boolean true) y 0).bind (fun py =>
        (branchTarget (c.type :: c.context) (.boolean false) n 1).map (fun pn => [py,pn]))
    | .tagBind t y n => (branchTarget (c.type :: c.context) (.tag t true) y 0).bind (fun py =>
        (branchTarget (c.type :: c.context) (.tag t false) n 1).map (fun pn => [py,pn])) : Except Failure (List (EdgeEvidence ι)))
  return {expression := e, edges := ps, knowledge := k, effect := some effect, output := out}

/-- Propagate established postconditions along single-predecessor paths. Entry
starts empty; source cuts use exactly their supplied requirements, even when
empty. Other merge points use supplied requirements. A node is checked once
when its unique predecessor is available; this is dependency scheduling, not invariant iteration.
Every edge is still checked by the independent consumer. -/
def produceRaw [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (fuel : Nat) (P : Program) (claims : List (PointClaim ι))
    (suggestions : List (Sequent ι) := []) (known : List (Evidence ι) := []) (start : Nat := 0)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := []) :
    Except Failure (ControlFlow.Certificate ι) := do
  if P.length != claims.length then throw .claimCount
  let incoming := (List.range P.length).map fun target =>
    P.zipIdx.flatMap fun (node,l) =>
      (successors node.continuation).zipIdx.filterMap fun (t,index) =>
        if t.label == target then some (l,index,t) else none
  let mut table : List (Option (NodeEvidence ι)) := List.replicate P.length none
  for _ in List.range (P.length + 1) do
    let mut progress := false
    for l in List.range P.length do
      if ((table[l]?).getD none).isSome then continue
      let some node := P[l]? | throw .claimCount
      let some c := claims[l]? | throw .claimCount
      let required := (requirements.lookup l).getD ⟨[],[],[]⟩
      let mut k := required
      if l != start && !cuts.contains l then
        if let some [(pred,index,target)] := incoming[l]? then
          let some previous := (table[pred]?).getD none | continue
          let some source := P[pred]? | throw .claimCount
          k := HeapKnowledge.project (edgeKnowledge previous.output source.continuation index)
            target.mapping c.context.length
      k := ⟨(k.cells ++ required.cells).eraseDups,(k.values ++ required.values).eraseDups,
        (k.links ++ required.links).eraseDups⟩
      let evidence ← produceNode G pool fuel l node claims k suggestions known
      table := table.set l (some evidence)
      progress := true
    if !progress then break
  table.mapM fun c => match c with
    | some e => pure e
    | none => throw .rejected

/-- Recover a located failed edge from the completed candidate. This includes
heap entailment; it is not limited to ordinary subtype proof construction. -/
private def failedEdge (P : Program)
    (C : ControlFlow.Certificate ι) : Option Failure := Id.run do
  for (node,l) in P.zipIdx do
    let some c := C[l]? | return some .claimCount
    for (target,index) in (successors node.continuation).zipIdx do
      let facts := edgeKnowledge c.output node.continuation index
      let some destination := C[target.label]? | return some .claimCount
      if !HeapKnowledge.check facts destination.knowledge target.mapping then
        return some (.edge l target.label index)
  return none

def produce [DecidableEq ι] (G : NormalGraph ι) (labels : List ι)
    (fuel : Nat) (R : Ty ι) (P : Program) (claims : List (PointClaim ι))
    (start : Nat) (hints : List (Ty ι) := []) (inputs : List (Ty ι) := [])
    (suggestions : List (Sequent ι) := []) (known : List (ProgramCertificates.Evidence ι) := [])
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := []) : Except Failure (ControlFlow.Certificate ι) :=
  match produceRaw G (vocabulary G labels claims (inputs ++ hints)) fuel P claims suggestions known start requirements cuts with
  | .error e => .error e
  | .ok C => if accept G R P claims C start inputs then .ok C
    else .error ((failedEdge P C).getD .rejected)

theorem produce_checked [DecidableEq ι] {G : NormalGraph ι} {labels fuel R P claims start hints inputs suggestions known requirements cuts C}
    (h : produce G labels fuel R P claims start hints inputs suggestions known requirements cuts = .ok C) :
    accept G R P claims C start inputs = true := by
  unfold produce at h
  split at h
  · contradiction
  · split at h
    · cases h; assumption
    · contradiction

#print axioms accepted_from_inputs
#print axioms accepted_safe
#print axioms produce_checked
end Verification.ExperimentState.CertificateProducer
