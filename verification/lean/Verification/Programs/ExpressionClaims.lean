import Verification.Source.RequestJson
import Verification.Programs.DirectProof

/-! Exact, independently checked expression sequents. These supplement the
whole-program certificate when source expressions occur inside lambda bodies.
The consumer uses existing declarative rules, never producer success alone. -/
namespace Verification.ExpressionClaims
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
variable [DecidableEq ι] [CertificateProducer.Instantiates ι]

/-- `valid` says which labels the graph's store holds. -/
@[nospecialize] def checkResult (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (j : Sequent ι) (e : Evidence ι) (codes : CodeEntry ι → Bool := fun _ => false) : CheckResult ι Unit :=
  (CheckResult.ofBool (validEvidence valid e && decide (claim e = j) &&
    checkScope j.context.length j.term)).bind fun _ => checkTreeResult G images e codes

@[nospecialize] def checkUsing (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (j : Sequent ι) (e : Evidence ι) (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  (checkResult G images valid j e codes).accepted

omit [CertificateProducer.Instantiates ι] in
theorem checkUsing_eq (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (j : Sequent ι) (e : Evidence ι) (codes : CodeEntry ι → Bool) :
    checkUsing G images valid j e codes = (validEvidence valid e && decide (claim e = j) &&
      checkScope j.context.length j.term && checkTreeUsing G images e codes) := by
  rw [checkUsing, checkResult, CheckResult.accepted_bind, CheckResult.accepted_ofBool]
  rfl

omit [CertificateProducer.Instantiates ι] in
theorem check_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {valid j e} {codes : CodeEntry ι → Bool} (h : checkUsing G images valid j e codes = true)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    HasTyUsing G images j.context j.term j.type := by
  simp only [checkUsing_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have ht := checkTreeUsing_sound e h.2 hcodes
  rw [h.1.1.2] at ht
  exact ht

@[nospecialize] def checkAllResult (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (rs : List (Required ι)) (es : List (Evidence ι)) (codes : CodeEntry ι → Bool := fun _ => false) : CheckResult ι Unit :=
  (CheckResult.ofBool (rs.length == es.length)).bind fun _ =>
  CheckResult.allLocated (rs.zip es) .obligation fun (r,e) => checkResult G images valid r.sequent e codes

@[nospecialize] def checkAllUsing (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool) (rs : List (Required ι)) (es : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  (checkAllResult G images valid rs es codes).accepted

omit [CertificateProducer.Instantiates ι] in
theorem checkAllUsing_eq (G : NormalGraph ι) (images : InstanceImageCheck G) (valid : ι → Bool)
    (rs : List (Required ι)) (es : List (Evidence ι)) (codes : CodeEntry ι → Bool) :
    checkAllUsing G images valid rs es codes =
      (rs.length == es.length && (rs.zip es).all (fun (r,e) => checkUsing G images valid r.sequent e codes)) := by
  simp only [checkAllUsing, checkAllResult, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
    CheckResult.accepted_allLocated, checkUsing]


omit [CertificateProducer.Instantiates ι] in
theorem checkAll_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {valid rs es} {codes : CodeEntry ι → Bool}
    (h : checkAllUsing G images valid rs es codes = true)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _)
    {r e} (hm : (r,e) ∈ rs.zip es) :
    HasTyUsing G images r.sequent.context r.sequent.term r.sequent.type := by
  simp only [checkAllUsing_eq, Bool.and_eq_true, List.all_eq_true] at h
  exact check_sound (h.2 _ hm) hcodes

/-- `valid` says which labels the graph's store holds, `project` what a
diagnostic mentioning some of them shows of it (`StoreView.project`). -/
@[nospecialize] def produceUsing [Hashable ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι)
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
    let candidate : ProgramCertificates.CheckResult ι (Evidence ι) ← match r.plan with
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
    let validated := candidate.bind fun e => (checkResult G images valid j e (fun _ => true)).map fun _ => e
    let some e := validated.value
      | if let some stop := validated.exhaustion then
          let p := project (stop.source ++ stop.target ++ j.context.flatten).eraseDups
          throw (withDiagnostic s!"closure expression claim at [{r.pos.1},{r.pos.2}): subtype search exhausted"
            ([("kind",toJson "direct-obligation"),("phase",toJson "proof-search"),
              ("outcome",toJson (DiagnosticOutcome.exhausted stop.limit stop.rounds stop.visited)),
              ("id",toJson s!"expression:{index}"),
              ("sourceMap",toJson (SourceMapEntry.mk r.pos r.role none [])),
              ("judgment",Json.mkObj [("kind",toJson "subtyping"),("subject",toJson r.pos),
                ("actual",toJson (p.shown stop.source)),("expected",toJson (p.shown stop.target))]),
              ("fuel",toJson fuel)] ++ p.fields))
        let p := project (j.type ++ j.context.flatten).eraseDups
        -- This record's table shows each row's clauses alone: a parameter,
        -- scheme or meet row as no clauses.
        throw (withDiagnostic s!"closure expression claim at [{r.pos.1},{r.pos.2}): evidence search failed"
          ([("kind",toJson "expression-claim"),("phase",toJson "proof-search"),
           ("outcome",toJson RequestJson.DiagnosticOutcome.notEstablished),("id",toJson s!"expression:{index}"),
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
@[nospecialize] def renderKnownUsing [Hashable ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι) (valid : ι → Bool)
    (plans : List (DirectProof.Plan ι)) : List (Evidence ι) := Id.run do
  let pool := CertificateProducer.vocabulary G labels [] (plans.flatMap fun p => p.goal.type :: p.goal.context)
  let mut cache : DirectProof.SubtypeCache ι := {}
  let mut es := #[]
  for plan in plans do
    let (e, next) := DirectProof.renderWith G images pool plan.goal.context plan cache
    cache := next
    if let some e := e.value.filter (fun e => checkUsing G images valid plan.goal e (fun _ => true)) then es := es.push e
  return es.toList

/-- The finite image checker, the default of the source path. -/
abbrev check (G : NormalGraph ι) := checkUsing G (finiteInstanceImages G)
abbrev checkAll (G : NormalGraph ι) := checkAllUsing G (finiteInstanceImages G)
abbrev produce [Hashable ι] (G : NormalGraph ι) := produceUsing G (finiteInstanceImages G)
abbrev renderKnown [Hashable ι] (G : NormalGraph ι) := renderKnownUsing G (finiteInstanceImages G)

end

#print axioms checkAll_sound
end Verification.ExpressionClaims
