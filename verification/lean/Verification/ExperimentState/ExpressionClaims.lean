import Verification.ExperimentState.RequestJson
import Verification.ExperimentState.DirectProof

/-! Exact, independently checked expression sequents. These supplement the
whole-program certificate when source expressions occur inside lambda bodies.
The consumer uses existing declarative rules, never producer success alone. -/
namespace Verification.ExperimentState.ExpressionClaims
open Lean ProgramTyping ProgramCertificates PositiveRules PositiveGraphs PositiveNormalization RequestJson

structure Required where
  pos : Nat × Nat
  sequent : Sequent Nat
  plan : Option DirectProof.Plan := none
  role : String := "expression-claim"

def check (G : NormalGraph Nat) (bound : Nat) (j : Sequent Nat) (e : Evidence Nat) : Bool :=
  validEvidence bound e && decide (claim e = j) &&
    checkScope j.context.length j.term && checkTree G e

theorem check_sound {G bound j e} (h : check G bound j e = true) :
    HasTy G j.context j.term j.type := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have ht := checkTree_sound e h.2
  rw [h.1.1.2] at ht
  exact ht

def checkAll (G : NormalGraph Nat) (bound : Nat) (rs : List Required) (es : List (Evidence Nat)) : Bool :=
  rs.length == es.length && (rs.zip es).all (fun (r,e) => check G bound r.sequent e)

theorem checkAll_sound {G bound rs es} (h : checkAll G bound rs es = true)
    {r e} (hm : (r,e) ∈ rs.zip es) :
    HasTy G r.sequent.context r.sequent.term r.sequent.type := by
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true] at h
  exact check_sound (h.2 _ hm)

def produce (G : NormalGraph Nat) (labels : List Nat) (bound fuel : Nat)
    (rs : List Required) : Except String (List (Evidence Nat)) := do
  let pool := CertificateProducer.vocabulary G labels []
    (rs.flatMap (fun r => r.sequent.type :: r.sequent.context))
  let es ← rs.zipIdx.mapM fun (r,index) => do
    let j := r.sequent
    let candidate := match r.plan with
      | some plan => DirectProof.render G pool j.context plan
      | none => CertificateProducer.expressionWith G pool (rs.map (·.sequent)) fuel j.context j.term j.type
    let some e := candidate
      | throw (withDiagnostic s!"closure expression claim at [{r.pos.1},{r.pos.2}): evidence search failed"
          [("kind",toJson "expression-claim"),("phase",toJson "proof-search"),
           ("outcome",toJson "not-established"),("id",toJson s!"expression:{index}"),
           ("origin",toJson (DiagnosticOrigin.mk r.pos r.role none)),
           ("sequent",toJson j),("fuel",toJson fuel),
           ("types",toJson ((List.range bound).map G))])
    return e
  if checkAll G bound rs es then return es
  throw (withDiagnostic "closure expression evidence failed independent checking"
    [("kind",toJson "production-failure"),("phase",toJson "certificate-check"),
     ("outcome",toJson "not-established"),("fuel",toJson fuel),
     ("types",toJson ((List.range bound).map G))])

#print axioms checkAll_sound
end Verification.ExperimentState.ExpressionClaims
