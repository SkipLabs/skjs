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
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat) : Bool :=
  decide (C.map signature = claims) && checkClosed G R P C start

theorem accept_claims [DecidableEq ι] {G : NormalGraph ι} {R P claims C start}
    (hc : accept G R P claims C start = true) : C.map signature = claims :=
  by
    simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {R P claims C start}
    (hc : accept G R P claims C start = true) (n : Nat) :
    SafeGraph P (meaning G R) n (ofList []) [] (.at start (fun _ => .nul)) :=
  by
    simp only [accept, Bool.and_eq_true] at hc
    exact accepted_closed_safe hc.2 n

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
    | .arrs L => clauses.flatMap fun b => match b with
      | .arrs M => M.filterMap fun p =>
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
    let next := table.filter fun p => (expand G p.1).all fun a =>
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
search fuel, including implicit let typing. No execution budget is inspected. -/
def expression [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι)) :
    Nat → List (Ty ι) → Tm → Ty ι → Option (ProgramCertificates.Evidence ι)
  | 0, _, _, _ => none
  | fuel+1, Γ, t, A => Id.run do
    let leaf := fun B r => ProgramCertificates.Evidence.node ⟨Γ,t,B⟩ r []
    let recur := expression G pool fuel
    match t with
    | .var i => return (Γ[i]?).bind fun B => coerce G pool (leaf B .var) A
    | .nul | .tru | .fls =>
      let r := match t with | .nul => Rule.nul | .tru => .tru | _ => .fls
      return (A :: pool).findSome? fun B =>
        let r := if expand G B = [.boolLit true] && t == .tru then Rule.truLit
          else if expand G B = [.boolLit false] && t == .fls then Rule.flsLit else r
        if checkTree G (leaf B r) then coerce G pool (leaf B r) A else none
    | .lam b =>
      return (A :: pool).findSome? fun F => do
        let [.arrs L] := expand G F | none
        let ps ← L.mapM fun p => recur (p.1 :: Γ) b p.2
        coerce G pool (.node ⟨Γ,t,F⟩ .lam ps) A
    | .app f a =>
      if let .lam b := f then
        if let some e := pool.findSome? (fun B => do
          let ea ← recur Γ a B
          let eb ← recur (B :: Γ) b A
          return ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ .letE [ea,eb]) then return some e
      return pool.findSome? fun F => do
        let [.arrs L] := expand G F | none
        L.findSome? fun p => do
          -- Check the result relation before searching both premises.
          let _ ← subtype G pool p.2 A
          let ef ← recur Γ f F
          let ea ← recur Γ a p.1
          coerce G pool (.node ⟨Γ,t,p.2⟩ .app [ef,ea]) A
    | .alloc a =>
      return (A :: pool).findSome? fun R => do
        let [.refs B []] := expand G R | none
        let ea ← recur Γ a B
        coerce G pool (.node ⟨Γ,t,R⟩ .alloc [ea]) A
    | .read a =>
      return pool.findSome? fun R => do
        let [.refs B []] := expand G R | none
        let _ ← subtype G pool B A
        let ea ← recur Γ a R
        coerce G pool (.node ⟨Γ,t,B⟩ .read [ea]) A
    | .write a b =>
      return pool.findSome? fun R => do
        let [.refs B []] := expand G R | none
        let ea ← recur Γ a R
        let eb ← recur Γ b B
        (A :: pool).findSome? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .write [ea,eb]
          if checkTree G e then coerce G pool e A else none
    | .ite (.test tag (.var i)) u e =>
      let some B := Γ[i]? | return none
      if decide (Answers G B tag true) then
        return (recur Γ u A).map fun p => .node ⟨Γ,t,A⟩ .ifTrue [p]
      if decide (Answers G B tag false) then
        return (recur Γ e A).map fun p => .node ⟨Γ,t,A⟩ .ifFalse [p]
      return none
    | _ => return none

/-- Gather graph labels, recursive operands and supplied union types. Hints may
add intermediate types; they cannot change claims or bypass evidence checking. -/
def vocabulary [DecidableEq ι] (G : NormalGraph ι) (labels : List ι)
    (claims : List (PointClaim ι)) (hints : List (Ty ι)) : List (Ty ι) :=
  ([] :: (labels.map fun i => [i]) ++ hints ++
    claims.flatMap (fun c => c.type :: c.context) ++
    labels.flatMap (fun i => (G i).flatMap fun c => match c with
      | .refs A bs => A :: bs
      | .arrs L => L.flatMap fun p => [p.1,p.2]
      | _ => [])).eraseDups

inductive Failure where
  | claimCount
  | expression (label : Nat)
  | edge (source : Nat) (destination : Nat)
  | rejected
  deriving DecidableEq, Repr

def edge [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (claims : List (PointClaim ι)) (Γ : List (Ty ι)) (target : Target) : Option (EdgeEvidence ι) := do
  let c ← claims[target.label]?
  if let some slots := target.mapping then
    if slots.length != c.context.length then failure
  (List.range c.context.length).mapM fun i => do
    let A ← Γ[slot target.mapping i]?
    let B ← c.context[i]?
    subtype G pool A B

def branchEdge [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (claims : List (PointClaim ι)) (Γ : List (Ty ι)) (q : Bool) (target : Target) :
    Option (EdgeEvidence ι) := do
  let c ← claims[target.label]?
  if let some slots := target.mapping then
    if slots.length != c.context.length then failure
  (List.range c.context.length).mapM fun i => do
    let A ← Γ[slot target.mapping i]?
    let B ← c.context[i]?
    if slot target.mapping i == 0 then
      if BranchRefinement.booleanMember G B q then pure .subset else failure
    else subtype G pool A B


def produceRaw [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (fuel : Nat) (P : Program) (claims : List (PointClaim ι)) :
    Except Failure (ControlFlow.Certificate ι) := do
  if P.length != claims.length then throw .claimCount
  P.zipIdx |>.mapM fun (node, l) => do
    let some c := claims[l]? | throw .claimCount
    let some e := expression G pool fuel c.context node.expression c.type | throw (.expression l)
    let target := fun Γ t => match edge G pool claims Γ t with
      | some p => Except.ok p
      | none => Except.error (Failure.edge l t.label)
    let branchTarget := fun Γ q t => match branchEdge G pool claims Γ q t with
      | some p => Except.ok p
      | none => Except.error (Failure.edge l t.label)
    let ps ← (match node.continuation with
      | .ret => pure []
      | .bind t => (target (c.type :: c.context) t).map (fun p => [p])
      | .effect t => (target c.context t).map (fun p => [p])
      | .branch y n => (target c.context y).bind (fun py =>
          (target c.context n).map (fun pn => [py,pn]))
      | .branchBind y n => (branchTarget (c.type :: c.context) true y).bind (fun py =>
          (branchTarget (c.type :: c.context) false n).map (fun pn => [py,pn])) : Except Failure (List (EdgeEvidence ι)))
    return ⟨e,ps⟩

def produce [DecidableEq ι] (G : NormalGraph ι) (labels : List ι)
    (fuel : Nat) (R : Ty ι) (P : Program) (claims : List (PointClaim ι))
    (start : Nat) (hints : List (Ty ι) := []) : Except Failure (ControlFlow.Certificate ι) :=
  match produceRaw G (vocabulary G labels claims hints) fuel P claims with
  | .error e => .error e
  | .ok C => if accept G R P claims C start then .ok C else .error .rejected

theorem produce_checked [DecidableEq ι] {G : NormalGraph ι} {labels fuel R P claims start hints C}
    (h : produce G labels fuel R P claims start hints = .ok C) :
    accept G R P claims C start = true := by
  unfold produce at h
  split at h
  · contradiction
  · split at h
    · cases h; assumption
    · contradiction

#print axioms accepted_safe
#print axioms produce_checked
end Verification.ExperimentState.CertificateProducer
