import Verification.ExperimentState.CertificateProducer

/-! Untrusted recipes for the source closure fragment. Recipes fix rule structure
and intermediate types; only coercions invoke subtype search. The ordinary
certificate consumer remains responsible for acceptance. -/
namespace Verification.ExperimentState.DirectProof
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
  node Γ (.app (.lam b.term) a.term) b.type .letE [a,b]

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
    | .letE, .app (.lam _) _, [a,b] =>
      let ea ← renderAt G pool depth Γ a
      let eb ← renderAt G pool depth ((claim ea).type :: Γ) b
      pure (.node ⟨Γ,j.term,j.type⟩ .letE [ea,eb])
    | .lam, .lam _, [b] =>
      let [.arrs [arrow]] := expand G j.type | none
      let eb ← renderAt G pool depth (arrow.1 :: Γ) b
      pure (.node ⟨Γ,j.term,j.type⟩ .lam [eb])
    | .ifBoolVar T F, .ite (.var i) _ _, [t,e] =>
      let pt ← renderAt G pool depth (Γ.set i T) t
      let pe ← renderAt G pool depth (Γ.set i F) e
      pure (.node ⟨Γ,j.term,j.type⟩ (.ifBoolVar T F) [pt,pe])
    | _, _, _ =>
      let es ← children.attach.mapM fun q => renderAt G pool depth Γ q.val
      pure (.node ⟨Γ,j.term,j.type⟩ r es)

def Plan.depth : Plan → Nat
  | .cast _ p => 1 + p.depth
  | .rule _ _ ps => 1 + (ps.map Plan.depth).foldl max 0

def render (G : NormalGraph Nat) (pool : List (Ty Nat)) (Γ : List (Ty Nat)) (p : Plan) :=
  renderAt G pool p.depth Γ p
end Verification.ExperimentState.DirectProof
