import Verification.Model.Programs.CertificateProducer

/-! Untrusted recipes for the source closure fragment. Recipes fix rule structure
and intermediate types; only coercions invoke subtype search. The ordinary
certificate consumer remains responsible for acceptance. -/
namespace Verification.Model.DirectProof
open PositiveGraphs ProgramTyping ProgramCertificates PositiveNormalization PositiveRules CertificateProducer

inductive Plan where
  | rule (goal : Sequent Nat) (rule : Rule Nat) (children : List Plan)
  | cast (goal : Sequent Nat) (child : Plan)

def Plan.goal : Plan → Sequent Nat
  | .rule j _ _ | .cast j _ => j

def Plan.term (p : Plan) : Tm := p.goal.term
def Plan.type (p : Plan) : Ty Nat := p.goal.type

def cast (Γ : List (Ty Nat)) (A : Ty Nat) (p : Plan) : Plan :=
  .cast ⟨Γ,p.term,A⟩ p

def node (Γ : List (Ty Nat)) (t : Tm) (A : Ty Nat) (r : Rule Nat)
    (ps : List Plan := []) : Plan := .rule ⟨Γ,t,A⟩ r ps

def var (Γ : List (Ty Nat)) (i : Nat) (A : Ty Nat) : Plan := node Γ (.var i) A .var

def letE (Γ : List (Ty Nat)) (a b : Plan) : Plan :=
  node Γ (.letE a.term b.term) b.type .letE [a,b]

/-- A known Boolean still evaluates its condition; only its reachable arm
needs the requested result type. The consumer checks the singleton premise. -/
def ifE (G : NormalGraph Nat) (Γ : List (Ty Nat)) (A : Ty Nat) (c t e : Plan) : Plan :=
  match expand G c.type with
  | [.boolLit q] => node Γ (.ite c.term t.term e.term) A (.ifKnown q)
      [c, cast Γ A (if q then t else e)]
  | _ => node Γ (.ite c.term t.term e.term) A .ifBool [c,cast Γ A t,cast Γ A e]

/-- Subtype search results already found, by source and target type. The graph
and the pool are fixed for one cache's life, so the two types are the key. -/
abbrev SubtypeCache := Std.HashMap (Ty Nat × Ty Nat) (Option (PositiveCertificates.Proof Nat))

/-- Rendering fails, or rebuilds evidence, with the searches done so far. -/
abbrev RenderM := OptionT (StateM SubtypeCache)

/-- `coerce`, each search done once per cache: the same search again returns
what it did the first time. -/
def coerceM (G : NormalGraph Nat) (pool : List (Ty Nat)) (e : Evidence Nat) (A : Ty Nat) :
    RenderM (Evidence Nat) := do
  if (claim e).type = A then return e
  let key := ((claim e).type, A)
  let found ← match (← get).get? key with
    | some found => pure found
    | none =>
      let found := subtype G pool (claim e).type A
      modify (·.insert key found)
      pure found
  let some p := found | failure
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

/-- Rebuild the recipe in the actual context. Variable leaves explicitly coerce
from that context to the planned type. This handles justified changes of supplied
statement environments without assuming the planned context holds. -/
def renderAt (G : NormalGraph Nat) (pool : List (Ty Nat)) :
    Nat → List (Ty Nat) → Plan → RenderM (Evidence Nat)
  | 0, _, _ => failure
  | depth+1, Γ, p => do
   match p with
   | .cast j child => coerceM G pool (← renderAt G pool depth Γ child) j.type
   | .rule j r children =>
    match r, j.term, children with
    | .var, .var i, [] =>
      let some A := Γ[i]? | failure
      coerceM G pool (.node ⟨Γ,.var i,A⟩ .var []) j.type
    | .letE, .letE _ _, [a,b] =>
      let ea ← renderAt G pool depth Γ a
      let eb ← renderAt G pool depth ((claim ea).type :: Γ) b
      pure (.node ⟨Γ,j.term,j.type⟩ .letE [ea,eb])
    | .funE, .make (.closure arity _) .nul, bs =>
      -- One body plan per signature, in the signature order the checker expects.
      let [.arrs L S] := expand G j.type | failure
      let L := ProgramTyping.offerRows L S
      if L.length != bs.length || !ProgramTyping.offersArity arity L then failure else do
        let es ← (L.zip bs).attach.mapM fun q =>
          renderAt G pool depth (ProgramTyping.bodyFrame arity q.val.1 Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ .funE es)
    | .ctorE U, .make (.closure arity _ .construct) .nul, bs =>
      -- One body per construct signature, with `undefined` in the receiver slot.
      let [.ctors L] := expand G j.type | failure
      let L := L.map fun p => (U, p.1, p.2)
      if L.length != bs.length || !ProgramTyping.offersArity arity L then failure else do
        let es ← (L.zip bs).attach.mapM fun q =>
          renderAt G pool depth (ProgramTyping.bodyFrame arity q.val.1 Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ (.ctorE U) es)
    | .funRest As, .make (.variadic arity _) .nul, bs =>
      -- One body plan per signature, with that signature's rest store in slot 0.
      let [.arrs [] L] := expand G j.type | failure
      if L.length != bs.length || As.length != L.length ||
          !L.all (fun p => p.2.1.length == arity) then failure else do
        let es ← ((L.zip As).zip bs).attach.mapM fun q =>
          renderAt G pool depth (q.val.1.2 :: q.val.1.1.1 :: q.val.1.1.2.1 ++ Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ (.funRest As) es)
    | .makeCallableRest As, .makeAt (.variadic arity _) _ _, ps =>
      let [.callable P [] [] L] := expand G j.type | failure
      let as := ps.take P.length
      let bs := ps.drop P.length
      if as.length != P.length then failure else do
      if L.length != bs.length || As.length != L.length ||
          !L.all (fun p => p.2.1.length == arity) then failure else do
        let eas ← (as.zip (P.map Prod.snd)).attach.mapM fun q => do
          coerceM G pool (← renderAt G pool depth Γ q.val.1) q.val.2
        let es ← ((L.zip As).zip bs).attach.mapM fun q =>
          renderAt G pool depth (q.val.1.2 :: q.val.1.1.1 :: q.val.1.1.2.1 ++ Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ (.makeCallableRest As) (eas ++ es))
    | .makeCallable, .makeAt (.closure arity _) _ _, ps =>
      let [.callable P [] L []] := expand G j.type | failure
      let as := ps.take P.length
      let bs := ps.drop P.length
      if as.length != P.length then failure else do
      if L.length != bs.length || !ProgramTyping.offersArity arity L then failure else do
        let eas ← (as.zip (P.map Prod.snd)).attach.mapM fun q => do
          coerceM G pool (← renderAt G pool depth Γ q.val.1) q.val.2
        let es ← (L.zip bs).attach.mapM fun q =>
          renderAt G pool depth (ProgramTyping.bodyFrame arity q.val.1 Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ .makeCallable (eas ++ es))
    -- The member's covering proofs are searched in the actual context.
    | .bindMember _, .letE (.readAt k (.var i)) _, [] =>
      let some O := Γ[i]? | failure
      let some ps := memberProofs G pool O k j.type | failure
      pure (.node ⟨Γ,j.term,j.type⟩ (.bindMember ps) [])
    | .ifBoolVar T F, .ite (.var i) _ _, [t,e] =>
      let pt ← renderAt G pool depth (Γ.set i T) t
      let pe ← renderAt G pool depth (Γ.set i F) e
      pure (.node ⟨Γ,j.term,j.type⟩ (.ifBoolVar T F) [pt,pe])
    | .unionVar i, _, children =>
      let some C := Γ[i]? | failure
      if C.length != children.length then failure else do
        let ps ← (C.zip children).mapM fun (a,p) => renderAt G pool depth (Γ.set i [a]) p
        pure (.node ⟨Γ,j.term,j.type⟩ (.unionVar i) ps)
    | _, _, _ =>
      let es ← children.attach.mapM fun q => renderAt G pool depth Γ q.val
      pure (.node ⟨Γ,j.term,j.type⟩ r es)

def Plan.depth : Plan → Nat
  | .cast _ p => 1 + p.depth
  | .rule _ _ ps => 1 + (ps.map Plan.depth).foldl max 0

/-- Render with the searches of earlier renders over the same graph and pool. -/
def renderWith (G : NormalGraph Nat) (pool : List (Ty Nat)) (Γ : List (Ty Nat)) (p : Plan)
    (cache : SubtypeCache) : Option (Evidence Nat) × SubtypeCache :=
  (renderAt G pool p.depth Γ p).run.run cache

def render (G : NormalGraph Nat) (pool : List (Ty Nat)) (Γ : List (Ty Nat)) (p : Plan) :
    Option (Evidence Nat) :=
  (renderWith G pool Γ p {}).1
end Verification.Model.DirectProof
