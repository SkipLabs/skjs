import Verification.Model.Source.RequestJson
import Verification.Model.Programs.DirectProof

/-! Exact, independently checked expression sequents. These supplement the
whole-program certificate when source expressions occur inside lambda bodies.
The consumer uses existing declarative rules, never producer success alone. -/
namespace Verification.Model.ExpressionClaims
open Lean ProgramTyping ProgramCertificates PositiveRules PositiveGraphs PositiveNormalization RequestJson
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

variable {ι : Type}

structure Required (ι : Type) where
  pos : Nat × Nat
  sequent : Sequent ι
  plan : Option (DirectProof.Plan ι) := none
  role : String := "expression-claim"
  /-- This obligation's source map: one descriptor per context binding. -/
  context : List Descriptor := []

section
variable [DecidableEq ι]

/-- `valid` says which labels the graph's store holds. -/
def checkUsing (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool) (j : Sequent ι) (e : Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  validEvidence valid e && decide (claim e = j) &&
    checkScope j.context.length j.term && checkTreeUsing G images e codes

theorem check_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {valid j e} {codes : CodeEntry ι → Bool} (h : checkUsing G images valid j e codes = true)
    (hcodes : CodesSound G codes := by exact Verification.Model.ProgramCertificates.codesSound_none _) :
    HasTyUsing G images j.context j.term j.type := by
  simp only [checkUsing, Bool.and_eq_true, decide_eq_true_eq] at h
  have ht := checkTreeUsing_sound e h.2 hcodes
  rw [h.1.1.2] at ht
  exact ht

def checkAllUsing (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool) (rs : List (Required ι)) (es : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  rs.length == es.length && (rs.zip es).all (fun (r,e) => checkUsing G images valid r.sequent e codes)

theorem checkAll_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {valid rs es} {codes : CodeEntry ι → Bool}
    (h : checkAllUsing G images valid rs es codes = true)
    (hcodes : CodesSound G codes := by exact Verification.Model.ProgramCertificates.codesSound_none _)
    {r e} (hm : (r,e) ∈ rs.zip es) :
    HasTyUsing G images r.sequent.context r.sequent.term r.sequent.type := by
  simp only [checkAllUsing, Bool.and_eq_true, List.all_eq_true] at h
  exact check_sound (h.2 _ hm) hcodes

/-- `valid` says which labels the graph's store holds, `project` what a
diagnostic mentioning some of them shows of it (`Store.project`). -/
def produceUsing [Hashable ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι)
    (valid : ι → Bool) (project : List ι → LabelStore.Projection ι) (fuel : Nat)
    (rs : List (Required ι)) : Except String (List (Evidence ι)) := do
  let pool := CertificateProducer.vocabulary G labels []
    (rs.flatMap (fun r => r.sequent.type :: r.sequent.context))
  -- Nested obligations render the same coercions again: one search cache
  -- serves them all, the graph and the pool being fixed here.
  let mut cache : DirectProof.SubtypeCache ι := {}
  let mut es := #[]
  for (r,index) in rs.zipIdx do
    let j := r.sequent
    let candidate : Option (Evidence ι) ← match r.plan with
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
    let some e := candidate.filter (fun e => checkUsing G images valid j e (fun _ => true))
      | let p := project (j.type ++ j.context.flatten).eraseDups
        -- This record's table shows each row's clauses alone: a parameter,
        -- scheme or meet row as no clauses.
        throw (withDiagnostic s!"closure expression claim at [{r.pos.1},{r.pos.2}): evidence search failed"
          ([("kind",toJson "expression-claim"),("phase",toJson "proof-search"),
           ("outcome",toJson "not-established"),("id",toJson s!"expression:{index}"),
           ("sourceMap",toJson (SourceMapEntry.mk r.pos r.role none r.context)),
           ("sequent",toJson (Sequent.mk (j.context.map p.shown) j.term (p.shown j.type))),
           ("fuel",toJson fuel),("types",toJson (p.rows.map GraphRow.union))] ++
           (if p.names.isEmpty then [] else [("names",toJson p.names)])))
    es := es.push e
  -- Each item passed `check` against its own obligation above, so no final
  -- aggregate check is repeated here; acceptance (`checkRequests`) checks
  -- the evidence independently.
  return es.toList

/-- Node plans rendered where they can be: search hints, never obligations.
A plan that does not render is dropped; its node is searched as any other. -/
def renderKnownUsing [Hashable ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι) (valid : ι → Bool)
    (plans : List (DirectProof.Plan ι)) : List (Evidence ι) := Id.run do
  let pool := CertificateProducer.vocabulary G labels [] (plans.flatMap fun p => p.goal.type :: p.goal.context)
  let mut cache : DirectProof.SubtypeCache ι := {}
  let mut es := #[]
  for plan in plans do
    let (e, next) := DirectProof.renderWith G images pool plan.goal.context plan cache
    cache := next
    if let some e := e.filter (fun e => checkUsing G images valid plan.goal e (fun _ => true)) then es := es.push e
  return es.toList

/-- The finite image checker, the default of the source path. -/
abbrev check (G : NormalGraph ι) := @checkUsing ι _ G (finiteInstanceImages G)
abbrev checkAll (G : NormalGraph ι) := @checkAllUsing ι _ G (finiteInstanceImages G)
abbrev produce [Hashable ι] (G : NormalGraph ι) := @produceUsing ι _ _ G (finiteInstanceImages G)
abbrev renderKnown [Hashable ι] (G : NormalGraph ι) := @renderKnownUsing ι _ _ G (finiteInstanceImages G)

end

#print axioms checkAll_sound
end Verification.Model.ExpressionClaims
