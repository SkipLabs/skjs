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

/-- Rebuild the recipe in the actual context. Variable leaves explicitly coerce
from that context to the planned type. This handles justified changes of supplied
statement environments without assuming the planned context holds. -/
def renderAt (G : NormalGraph Nat) (pool : List (Ty Nat)) :
    Nat → List (Ty Nat) → Plan → Option (Evidence Nat)
  | 0, _, _ => none
  | depth+1, Γ, p => do
   match p with
   | .cast j child => coerce G pool (← renderAt G pool depth Γ child) j.type
   | .rule j r children =>
    match r, j.term, children with
    | .var, .var i, [] =>
      let A ← Γ[i]?
      coerce G pool (.node ⟨Γ,.var i,A⟩ .var []) j.type
    | .letE, .letE _ _, [a,b] =>
      let ea ← renderAt G pool depth Γ a
      let eb ← renderAt G pool depth ((claim ea).type :: Γ) b
      pure (.node ⟨Γ,j.term,j.type⟩ .letE [ea,eb])
    | .funE, .make (.closure arity _) .nul, bs =>
      -- One body plan per signature, in the signature order the checker expects.
      let [.arrs L []] := expand G j.type | none
      if L.length != bs.length || !L.all (fun p => p.2.1.length == arity) then none else do
        let es ← (L.zip bs).attach.mapM fun q =>
          renderAt G pool depth (q.val.1.1 :: q.val.1.2.1 ++ Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ .funE es)
    | .ctorE U, .make (.closure arity _ .construct) .nul, bs =>
      -- One body per construct signature, with `undefined` in the receiver slot.
      let [.ctors L] := expand G j.type | none
      if L.length != bs.length || !L.all (fun p => p.1.length == arity) then none else do
        let es ← (L.zip bs).attach.mapM fun q =>
          renderAt G pool depth (U :: q.val.1.1 ++ Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ (.ctorE U) es)
    | .funRest As, .make (.variadic arity _) .nul, bs =>
      -- One body plan per signature, with that signature's rest store in slot 0.
      let [.arrs [] L] := expand G j.type | none
      if L.length != bs.length || As.length != L.length ||
          !L.all (fun p => p.2.1.length == arity) then none else do
        let es ← ((L.zip As).zip bs).attach.mapM fun q =>
          renderAt G pool depth (q.val.1.2 :: q.val.1.1.1 :: q.val.1.1.2.1 ++ Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ (.funRest As) es)
    | .makeCallableRest As, .makeAt (.variadic arity _) _ _, ps =>
      let [.callable P [] [] L] := expand G j.type | none
      let as := ps.take P.length
      let bs := ps.drop P.length
      if as.length != P.length then none else do
      if L.length != bs.length || As.length != L.length ||
          !L.all (fun p => p.2.1.length == arity) then none else do
        let eas ← (as.zip (P.map Prod.snd)).attach.mapM fun q => do
          coerce G pool (← renderAt G pool depth Γ q.val.1) q.val.2
        let es ← ((L.zip As).zip bs).attach.mapM fun q =>
          renderAt G pool depth (q.val.1.2 :: q.val.1.1.1 :: q.val.1.1.2.1 ++ Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ (.makeCallableRest As) (eas ++ es))
    | .makeCallable, .makeAt (.closure arity _) _ _, ps =>
      let [.callable P [] L []] := expand G j.type | none
      let as := ps.take P.length
      let bs := ps.drop P.length
      if as.length != P.length then none else do
      if L.length != bs.length || !L.all (fun p => p.2.1.length == arity) then none else do
        let eas ← (as.zip (P.map Prod.snd)).attach.mapM fun q => do
          coerce G pool (← renderAt G pool depth Γ q.val.1) q.val.2
        let es ← (L.zip bs).attach.mapM fun q =>
          renderAt G pool depth (q.val.1.1 :: q.val.1.2.1 ++ Γ) q.val.2
        pure (.node ⟨Γ,j.term,j.type⟩ .makeCallable (eas ++ es))
    | .ifBoolVar T F, .ite (.var i) _ _, [t,e] =>
      let pt ← renderAt G pool depth (Γ.set i T) t
      let pe ← renderAt G pool depth (Γ.set i F) e
      pure (.node ⟨Γ,j.term,j.type⟩ (.ifBoolVar T F) [pt,pe])
    | .unionVar i, _, children =>
      let C ← Γ[i]?
      if C.length != children.length then none else do
        let ps ← (C.zip children).mapM fun (a,p) => renderAt G pool depth (Γ.set i [a]) p
        pure (.node ⟨Γ,j.term,j.type⟩ (.unionVar i) ps)
    | _, _, _ =>
      let es ← children.attach.mapM fun q => renderAt G pool depth Γ q.val
      pure (.node ⟨Γ,j.term,j.type⟩ r es)

def Plan.depth : Plan → Nat
  | .cast _ p => 1 + p.depth
  | .rule _ _ ps => 1 + (ps.map Plan.depth).foldl max 0

def render (G : NormalGraph Nat) (pool : List (Ty Nat)) (Γ : List (Ty Nat)) (p : Plan) :=
  renderAt G pool p.depth Γ p
end Verification.Model.DirectProof
