import Verification.Model.Programs.CertificateProducer

/-! Untrusted recipes for the source closure fragment. Recipes fix rule structure
and intermediate types; only coercions invoke subtype search. The ordinary
certificate consumer remains responsible for acceptance. -/
namespace Verification.Model.DirectProof
open PositiveGraphs ProgramTyping ProgramCertificates PositiveNormalization PositiveRules CertificateProducer
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

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

/-- Subtype search results already found, by source and target type. The graph,
its image checker and the pool are fixed for one cache's life, so the two
types are the key. -/
abbrev SubtypeCache := Std.HashMap (Ty Nat × Ty Nat) (Option (PositiveCertificates.Proof Nat))

/-- Rendering fails, or rebuilds evidence, with the searches done so far. -/
abbrev RenderM := OptionT (StateM SubtypeCache)

/-- `coerce`, each search done once per cache: the same search again returns
what it did the first time. -/
def coerceM (G : NormalGraph Nat) (images : InstanceImageCheck G) (pool : List (Ty Nat)) (e : Evidence Nat) (A : Ty Nat) :
    RenderM (Evidence Nat) := do
  if (claim e).type = A then return e
  let key := ((claim e).type, A)
  let found ← match (← get).get? key with
    | some found => pure found
    | none =>
      let found := subtypeUsing G images pool (claim e).type A
      modify (·.insert key found)
      pure found
  let some p := found | failure
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

/-- Rebuild the recipe in the actual context. Variable leaves explicitly coerce
from that context to the planned type. This handles justified changes of supplied
statement environments without assuming the planned context holds. -/
def renderAt (G : NormalGraph Nat) (images : InstanceImageCheck G) (pool : List (Ty Nat)) :
    Nat → List (Ty Nat) → Plan → RenderM (Evidence Nat)
  | 0, _, _ => failure
  | depth+1, Γ, p => do
   match p with
   | .cast j child => coerceM G images pool (← renderAt G images pool depth Γ child) j.type
   | .rule j r children =>
    match r, j.term, children with
    | .var, .var i, [] =>
      let some A := Γ[i]? | failure
      coerceM G images pool (.node ⟨Γ,.var i,A⟩ .var []) j.type
    | .letE, .letE _ _, [a,b] =>
      let ea ← renderAt G images pool depth Γ a
      let eb ← renderAt G images pool depth ((claim ea).type :: Γ) b
      pure (.node ⟨Γ,j.term,j.type⟩ .letE [ea,eb])
    -- The member's covering proofs are searched in the actual context.
    | .bindMember _, .letE (.readAt k (.var i)) _, [] =>
      let some O := Γ[i]? | failure
      let some ps := memberProofsUsing G images pool O k j.type | failure
      pure (.node ⟨Γ,j.term,j.type⟩ (.bindMember ps) [])
    | .ifBoolVar T F, .ite (.var i) _ _, [t,e] =>
      let pt ← renderAt G images pool depth (Γ.set i T) t
      let pe ← renderAt G images pool depth (Γ.set i F) e
      pure (.node ⟨Γ,j.term,j.type⟩ (.ifBoolVar T F) [pt,pe])
    | .unionVar i, _, children =>
      -- One child per label the slot holds in the actual context: the
      -- planned label's child. An enclosing split may have left the slot
      -- fewer labels than the recipe planned for (a variable tested twice).
      let some C := Γ[i]? | failure
      let some P := j.context[i]? | failure
      if P.length != children.length then failure else do
        let ps ← C.mapM fun a => do
          let some k := P.idxOf? a | failure
          let some p := children[k]? | failure
          renderAt G images pool depth (Γ.set i [a]) p
        pure (.node ⟨Γ,j.term,j.type⟩ (.unionVar i) ps)
    | _, _, _ =>
      let es ← children.attach.mapM fun q => renderAt G images pool depth Γ q.val
      pure (.node ⟨Γ,j.term,j.type⟩ r es)

def Plan.depth : Plan → Nat
  | .cast _ p => 1 + p.depth
  | .rule _ _ ps => 1 + (ps.map Plan.depth).foldl max 0

/-- Render with the searches of earlier renders over the same graph and pool. -/
def renderWith (G : NormalGraph Nat) (images : InstanceImageCheck G) (pool : List (Ty Nat)) (Γ : List (Ty Nat)) (p : Plan)
    (cache : SubtypeCache) : Option (Evidence Nat) × SubtypeCache :=
  (renderAt G images pool p.depth Γ p).run.run cache

def renderUsing (G : NormalGraph Nat) (images : InstanceImageCheck G) (pool : List (Ty Nat)) (Γ : List (Ty Nat)) (p : Plan) :
    Option (Evidence Nat) :=
  (renderWith G images pool Γ p {}).1

/-- The finite image checker, the default. -/
abbrev render (G : NormalGraph Nat) := @renderUsing G (finiteInstanceImages G)
end Verification.Model.DirectProof
