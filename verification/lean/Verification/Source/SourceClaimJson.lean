-- SourceClaimWire.lean defines the strict claim document wire and decoder.
import Verification.Source.SourceClaimWire
-- SourceClaimDiagnostics.lean writes located source and quantified-call diagnostics.
import Verification.Source.SourceClaimDiagnostics
-- SourceClaimSchemes.lean prepares schemes, generic instances and binder rows.
import Verification.Source.SourceClaimSchemes
-- SourceClaimSites.lean checks claim sites and module initialization order.
import Verification.Source.SourceClaimSites
-- SourceClaimPreparation.lean lowers source annotations and claims into their equations.
import Verification.Source.SourceClaimPreparation
-- SourceClaimPlans.lean owns the exhaustive certification boundary and frozen plans.
import Verification.Source.SourceClaimPlans
-- SourceClaimExtraction.lean coordinates source units and reconstructs graph requests.
import Verification.Source.SourceClaimExtraction

/-! Source claim validation, evidence production and the theorem relating
exact accepted plans to modeled graph safety. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open EquationGraphs (Tree)

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json)
    (only : Option (String × Span) := none)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String Unit := do
  let (T, plans) ← extractPlans ast claims fileKey only budget
  let ⟨F, frozen⟩ ← freezePlans T plans
  let certified ← certifyPlans frozen
  let rs := CertifiedPlan.requests certified
  let b : Bundle (EquationStore.CheckedLabel F.equations F.primitive) ← decodeStrict evidence
  let checked := checkRequestsResult rs b
  if checked.accepted then return ()
  throw (validationFailure rs checked "source evidence does not justify the extracted program and exact claims")

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (only : Option (String × Span) := none)
    (budget : PositiveCertificates.SearchBudget := {}) : Except String Json := do
  let (T, plans) ← extractPlans ast claims fileKey only budget
  let ⟨F, frozen⟩ ← freezePlans T plans
  let rs := FunctionPlan.requests frozen
  let es ← rs.mapM fun r => ExpressionClaims.produceUsing (RequestJson.graph r.toRequest)
    (StoreView.images r.types) r.searchLabels (StoreView.valid r.types)
    (StoreView.projection r.types) fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let known := proofs ++ ExpressionClaims.renderKnownUsing (RequestJson.graph r.toRequest)
      (StoreView.images r.types) r.searchLabels (StoreView.valid r.types) r.nodePlans
    RequestJson.produceResponse r.toRequest fuel [] known r.sourceMap (some r.searchLabels) r.assertions
      r.cuts r.codeHints
  let evidence := toJson (Bundle.mk cs es)
  let b : Bundle (EquationStore.CheckedLabel F.equations F.primitive) ← decodeStrict evidence
  let checked := checkRequestsResult rs b
  if !checked.accepted then
    throw (validationFailure rs checked "source evidence does not justify the extracted graph requests")
  return evidence

/-- Every extracted plan crosses the exhaustive certification boundary, and its
graph request proves the enclosing execution safe at every assignment of the
parameter rows, so a generic unit or closure at every instantiation. The
graph is `Equations.graph` of the equations the extracted store presents,
validated by `Equations.ofRaw` (`freezePlans`). -/
theorem checkJson_safe {ast claims evidence : Json} {fileKey : String}
    {only : Option (String × Span)} {budget : PositiveCertificates.SearchBudget}
    (h : checkJson ast claims fileKey evidence only budget = .ok ()) :
    ∃ T plans, extractPlans ast claims fileKey only budget = .ok (T, plans) ∧
      ∃ F : EquationStore.Frozen, ∃ frozen certified b,
      freezePlans T plans = .ok ⟨F, frozen⟩ ∧
      certifyPlans frozen = .ok certified ∧
      decodeStrict evidence = .ok b ∧
      checkRequests (CertifiedPlan.requests certified) b = true ∧
      (∀ r c, (r,c) ∈ (CertifiedPlan.requests certified).zip b.functions →
        ∀ η n W heap ρ, EnvOk (reassign F.equations.graph η) r.inputs ρ n W →
          WorldAdm W → HeapOk n W heap →
          SafeGraph r.program (meaning (reassign F.equations.graph η) r.result)
            n W heap (.at r.start ρ)) := by
  unfold checkJson at h
  cases he : extractPlans ast claims fileKey only budget with
  | error e => rw [he] at h; contradiction
  | ok tp =>
    obtain ⟨T, plans⟩ := tp
    rw [he] at h
    simp only [Bind.bind, Except.bind] at h
    cases hf : freezePlans T plans with
    | error e => rw [hf] at h; contradiction
    | ok Ff =>
      obtain ⟨F, frozen⟩ := Ff
      rw [hf] at h
      simp only at h
      cases hc : certifyPlans frozen with
      | error e => rw [hc] at h; contradiction
      | ok certified =>
        rw [hc] at h
        cases hb : (decodeStrict evidence : Except String
            (Bundle (EquationStore.CheckedLabel F.equations F.primitive))) with
        | error e => rw [hb] at h; contradiction
        | ok b =>
          rw [hb] at h
          by_cases hx : checkRequests (CertifiedPlan.requests certified) b = true
          · refine ⟨T, plans, rfl, F, frozen, certified, b, hf, hc, hb, hx, ?_⟩
            intro r c hm η n W heap ρ he hw hh
            exact checkRequests_safe_at hx hm η n W heap ρ he hw hh
          · simp only [checkRequests] at hx
            simp [hx] at h

#print axioms checkJson_safe
end Verification.SourceClaimJson
