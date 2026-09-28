import Verification.Model.Source.RequestJson
import Verification.Model.Programs.DirectProof

/-! Exact, independently checked expression sequents. These supplement the
whole-program certificate when source expressions occur inside lambda bodies.
The consumer uses existing declarative rules, never producer success alone. -/
namespace Verification.Model.ExpressionClaims
open Lean ProgramTyping ProgramCertificates PositiveRules PositiveGraphs PositiveNormalization RequestJson
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

structure Required where
  pos : Nat × Nat
  sequent : Sequent Nat
  plan : Option DirectProof.Plan := none
  role : String := "expression-claim"
  /-- This obligation's source map: one descriptor per context binding. -/
  context : List Descriptor := []

def checkUsing (G : NormalGraph Nat) (images : InstanceImageCheck G) (bound : Nat) (j : Sequent Nat) (e : Evidence Nat)
    (codes : CodeEntry Nat → Bool := fun _ => false) : Bool :=
  validEvidence bound e && decide (claim e = j) &&
    checkScope j.context.length j.term && checkTreeUsing G images e codes

theorem check_sound {G : NormalGraph Nat} {images : InstanceImageCheck G} {bound j e} {codes : CodeEntry Nat → Bool} (h : checkUsing G images bound j e codes = true)
    (hcodes : CodesSound G codes := by exact Verification.Model.ProgramCertificates.codesSound_none _) :
    HasTyUsing G images j.context j.term j.type := by
  simp only [checkUsing, Bool.and_eq_true, decide_eq_true_eq] at h
  have ht := checkTreeUsing_sound e h.2 hcodes
  rw [h.1.1.2] at ht
  exact ht

def checkAllUsing (G : NormalGraph Nat) (images : InstanceImageCheck G) (bound : Nat) (rs : List Required) (es : List (Evidence Nat))
    (codes : CodeEntry Nat → Bool := fun _ => false) : Bool :=
  rs.length == es.length && (rs.zip es).all (fun (r,e) => checkUsing G images bound r.sequent e codes)

theorem checkAll_sound {G : NormalGraph Nat} {images : InstanceImageCheck G} {bound rs es} {codes : CodeEntry Nat → Bool}
    (h : checkAllUsing G images bound rs es codes = true)
    (hcodes : CodesSound G codes := by exact Verification.Model.ProgramCertificates.codesSound_none _)
    {r e} (hm : (r,e) ∈ rs.zip es) :
    HasTyUsing G images r.sequent.context r.sequent.term r.sequent.type := by
  simp only [checkAllUsing, Bool.and_eq_true, List.all_eq_true] at h
  exact check_sound (h.2 _ hm) hcodes

def produceUsing (G : NormalGraph Nat) (images : InstanceImageCheck G) (labels : List Nat) (bound fuel : Nat)
    (rs : List Required) : Except String (List (Evidence Nat)) := do
  let pool := CertificateProducer.vocabulary G labels []
    (rs.flatMap (fun r => r.sequent.type :: r.sequent.context))
  -- Nested obligations render the same coercions again: one search cache
  -- serves them all, the graph and the pool being fixed here.
  let mut cache : DirectProof.SubtypeCache := {}
  let mut es := #[]
  for (r,index) in rs.zipIdx do
    let j := r.sequent
    let candidate : Option (Evidence Nat) ← match r.plan with
      | some plan => do
        let (e, next) := DirectProof.renderWith G images pool j.context plan cache
        cache := next
        pure e
      | none => pure (CertificateProducer.expressionWithUsing G images pool (rs.map Required.sequent) fuel j.context j.term j.type)
    -- Attribute an invalid suggested proof to its own obligation, rather than
    -- losing the source location in the final aggregate check.
    -- The graph code a unit creates is checked after its obligations are
    -- rendered: here every code is admitted, and acceptance checks the
    -- obligation again against the table its certificate checked.
    let some e := candidate.filter (fun e => checkUsing G images bound j e (fun _ => true))
      | throw (withDiagnostic s!"closure expression claim at [{r.pos.1},{r.pos.2}): evidence search failed"
          [("kind",toJson "expression-claim"),("phase",toJson "proof-search"),
           ("outcome",toJson "not-established"),("id",toJson s!"expression:{index}"),
           ("sourceMap",toJson (SourceMapEntry.mk r.pos r.role none r.context)),
           ("sequent",toJson j),("fuel",toJson fuel),
           ("types",toJson ((List.range bound).map G))])
    es := es.push e
  -- Each item passed `check` against its own obligation above, so no final
  -- aggregate check is repeated here; acceptance (`checkRequests`) checks
  -- the evidence independently.
  return es.toList

/-- Node plans rendered where they can be: search hints, never obligations.
A plan that does not render is dropped; its node is searched as any other. -/
def renderKnownUsing (G : NormalGraph Nat) (images : InstanceImageCheck G) (labels : List Nat) (bound : Nat)
    (plans : List DirectProof.Plan) : List (Evidence Nat) := Id.run do
  let pool := CertificateProducer.vocabulary G labels [] (plans.flatMap fun p => p.goal.type :: p.goal.context)
  let mut cache : DirectProof.SubtypeCache := {}
  let mut es := #[]
  for plan in plans do
    let (e, next) := DirectProof.renderWith G images pool plan.goal.context plan cache
    cache := next
    if let some e := e.filter (fun e => checkUsing G images bound plan.goal e (fun _ => true)) then es := es.push e
  return es.toList

/-- The finite image checker, the default of the source path. -/
abbrev check (G : NormalGraph Nat) := @checkUsing G (finiteInstanceImages G)
abbrev checkAll (G : NormalGraph Nat) := @checkAllUsing G (finiteInstanceImages G)
abbrev produce (G : NormalGraph Nat) := @produceUsing G (finiteInstanceImages G)
abbrev renderKnown (G : NormalGraph Nat) := @renderKnownUsing G (finiteInstanceImages G)

#print axioms checkAll_sound
end Verification.Model.ExpressionClaims
