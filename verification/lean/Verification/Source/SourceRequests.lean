import Verification.Programs.ExpressionClaims
import Verification.Programs.DirectObligation
-- SourceResolution.lean constructs the qualified body checker from the retained
-- source signature and proves the descriptor evidence used by source instances.
import Verification.Source.SourceResolution

namespace Verification.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open LabelStore
open EquationGraphs (Tree)

/-- What the source says of one code request's graph, as of a unit's: its
source map, its statement entries' knowledge and its cuts. -/
structure CodeSource where
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  cuts : List Nat := []

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

structure SourceRequest (σ ι : Type) [Labels ι] [StoreView σ ι] extends Request σ ι where
  /-- The enclosing generic signature, retained through label freezing. -/
  sourceScheme : Option (PositiveGraphs.SchemeRow ι) := none
  /-- Constructed from the frozen descriptor domain and source signature. -/
  qualification : Option (RequestJson.QualifiedBody (RequestJson.graph toRequest)
    (StoreView.images toRequest.types)) := none
  obligations : List (ExpressionClaims.Required ι)
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- Full statement-entry interfaces; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- Labels the program mentions but no claim does: search hints only. -/
  hints : List ι := []
  /-- One per code request, in its order. -/
  codeSources : List CodeSource := []
  /-- Plans for nodes the lowering knows how to derive: search hints only. -/
  nodePlans : List (DirectProof.Plan ι) := []

@[nospecialize] def SourceRequest.codeHints (r : SourceRequest σ ι) : List RequestJson.CodeHints :=
  r.codeSources.map fun c => ⟨c.sourceMap, c.assertions, c.cuts⟩

/-- Search hints only: the primitives and the labels the request mentions, so
a coercion does not consider every unrelated signature in the table. The
consumer still checks against the complete graph and the exact request. -/
@[nospecialize] def SourceRequest.searchLabels (r : SourceRequest σ ι) : List ι :=
  let roots := ([Labels.nul,Labels.tru,Labels.fls,Labels.undef] ++ r.result ++ r.inputs.flatten ++ r.hints ++
    r.claims.flatMap (fun (c : PointClaim ι) => c.type ++ c.context.flatten) ++
    -- A closure's code is searched with the request's vocabulary: what its
    -- claims mention is part of it (a generic closure's binder rows).
    r.codes.flatMap (fun (q : RequestJson.CodeRequest ι) => q.claims.flatMap (fun (c : PointClaim ι) => c.type ++ c.context.flatten)) ++
    r.obligations.flatMap (fun (o : ExpressionClaims.Required ι) => o.sequent.type ++ o.sequent.context.flatten)).eraseDups
  -- Readonly array coercions depend on the store's element unions two levels
  -- below the object. Close the vocabulary over the reachable graph,
  -- stopping at the fixpoint, where a step adds no label, or at the store's
  -- bound on labels: an equation graph's rows reach infinitely many.
  Id.run do
    let mut known := roots
    for _ in List.range (StoreView.bound r.types) do
      if known.length ≥ StoreView.bound r.types then break
      -- A meet row's clauses name a type the store may hold as a row of its
      -- own, a bounded binder's bound: a read through the binder is at it.
      let next := (known ++ known.flatMap (fun i =>
        let row := StoreView.row r.types i
        row.union.flatMap (fun c => (RequestJson.clauseTypes c).flatten) ++
        (match row with
          | .meet _ cs _ => (StoreView.lookup r.types cs).toList
          | _ => []))).eraseDups
      if next.length == known.length then break
      known := next
    return known

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

@[nospecialize] def SourceRequest.checker (r : SourceRequest σ ι) :
    HeapExpressionRules.Checker (RequestJson.graph r.toRequest) (StoreView.images r.types) :=
  match r.qualification with
  | none => HeapExpressionRules.Checker.ordinary _ _
  | some q => q.checker

/-- Unqualified bodies permit every assignment; qualified bodies permit the
instances of their retained source signature. -/
def SourceRequest.Admits (r : SourceRequest σ ι) (η : PositiveGraphs.MixedAssignment ι) : Prop :=
  match r.qualification with
  | none => True
  | some q => q.Admits η

/-- Evidence order is source declaration order, independent of export order. -/
structure Bundle (ι : Type) where
  functions : List (Response ι)
  obligations : List (List (ProgramCertificates.Evidence ι))
  deriving ToJson, FromJson

/-- Statement entries are exact interfaces, in a unit's graph and in each of its
codes'. Expression observation checkpoints inside a statement require
entailment but do not reset its local context. -/
def checkGraphAssertions (cuts : List Nat) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (C : ControlFlow.Certificate ι) : Bool :=
  (cuts.all fun l => match C[l]? with
    | none => false
    | some n => n.knowledge == (assertions.lookup l).getD ⟨[],[],[]⟩) &&
  (assertions.all fun (l,k) => match C[l]? with
    | none => false
    | some n => HeapKnowledge.check n.knowledge k none)

@[nospecialize] def checkAssertions (r : SourceRequest σ ι) (c : Response ι) : Bool :=
  checkGraphAssertions r.cuts r.assertions c.certificate &&
  r.codeSources.length == c.codes.length &&
  (r.codeSources.zip c.codes).all fun (q, C) => checkGraphAssertions q.cuts q.assertions C

/-- Accepted source evidence has exactly the supplied knowledge at every
statement entry, even when that knowledge is empty. -/
theorem checkAssertions_cut {r : (SourceRequest σ ι)} {c : (Response ι)}
    (hc : checkAssertions r c = true) {l node} (hm : l ∈ r.cuts)
    (hn : c.certificate[l]? = some node) :
    node.knowledge = (r.assertions.lookup l).getD ⟨[],[],[]⟩ := by
  simp only [checkAssertions, checkGraphAssertions, Bool.and_eq_true] at hc
  replace hc := hc.1.1
  have h := List.all_eq_true.mp hc.1 l hm
  simpa [hn] using h

theorem checkAssertions_sound {r : (SourceRequest σ ι)} {c : (Response ι)}
    (hc : checkAssertions r c = true) {l k node ρ heap}
    (hm : (l,k) ∈ r.assertions) (hn : c.certificate[l]? = some node)
    (hk : HeapKnowledge.Holds node.knowledge ρ heap) : HeapKnowledge.Holds k ρ heap := by
  simp only [checkAssertions, checkGraphAssertions, Bool.and_eq_true] at hc
  replace hc := hc.1.1
  have h := List.all_eq_true.mp hc.2 (l,k) hm
  simp only [hn] at h
  exact HeapKnowledge.check_sound (m := none) h hk

/-- Validate one unit, sharing its checked code table with supplemental obligations. -/
@[nospecialize] def checkRequestResult (r : SourceRequest σ ι) (c : Response ι)
    (es : List (ProgramCertificates.Evidence ι)) : ProgramCertificates.CheckResult ι Unit :=
  (verifyResult r.toRequest c r.checker).bind fun table =>
    (ProgramCertificates.CheckResult.ofBool (checkAssertions r c)).bind fun _ =>
    ExpressionClaims.checkAllResult (RequestJson.graph r.toRequest) (StoreView.images r.types)
      (StoreView.valid r.types) r.obligations es (GraphCode.admits table)

theorem checkRequestResult_accepted_iff (r : SourceRequest σ ι) (c : Response ι)
    (es : List (ProgramCertificates.Evidence ι)) :
    (checkRequestResult r c es).accepted = true ↔
      verify r.toRequest c r.checker = true ∧ checkAssertions r c = true ∧
      ∃ table, codeTable r.toRequest c = some table ∧
        ExpressionClaims.checkAllUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
          (StoreView.valid r.types) r.obligations es (GraphCode.admits table) = true := by
  rw [checkRequestResult, ProgramCertificates.CheckResult.accepted_bind_value,
    Option.any_eq_true]
  constructor
  · rintro ⟨table, ht, hc⟩
    obtain ⟨hv, htable⟩ := (verifyResult_hasTable _ _ _ r.checker).mp ht
    rw [ProgramCertificates.CheckResult.accepted_bind,
      ProgramCertificates.CheckResult.accepted_ofBool] at hc
    exact ⟨hv, (Bool.and_eq_true_iff.mp hc).1, table, htable, (Bool.and_eq_true_iff.mp hc).2⟩
  · rintro ⟨hv, ha, table, ht, ho⟩
    refine ⟨table, (verifyResult_hasTable _ _ _ r.checker).mpr ⟨hv, ht⟩, ?_⟩
    rw [ProgramCertificates.CheckResult.accepted_bind,
      ProgramCertificates.CheckResult.accepted_ofBool]
    exact Bool.and_eq_true_iff.mpr ⟨ha, ho⟩

@[nospecialize] def checkRequestsResult (rs : List (SourceRequest σ ι)) (b : Bundle ι) :
    ProgramCertificates.CheckResult ι Unit :=
  (ProgramCertificates.CheckResult.ofBool (rs.length == b.functions.length &&
    rs.length == b.obligations.length)).bind fun _ =>
  ProgramCertificates.CheckResult.allLocated ((rs.zip b.functions).zip b.obligations) .request
    fun ((r,c),es) => checkRequestResult r c es

@[nospecialize] def checkRequests (rs : List (SourceRequest σ ι)) (b : Bundle ι) : Bool :=
  (checkRequestsResult rs b).accepted

theorem checkRequests_eq (rs : List (SourceRequest σ ι)) (b : Bundle ι) :
    checkRequests rs b = (rs.length == b.functions.length && rs.length == b.obligations.length &&
      ((rs.zip b.functions).zip b.obligations).all (fun ((r,c),es) => (checkRequestResult r c es).accepted)) := by
  rw [checkRequests, checkRequestsResult, ProgramCertificates.CheckResult.accepted_bind,
    ProgramCertificates.CheckResult.accepted_ofBool, ProgramCertificates.CheckResult.accepted_allLocated]

theorem checkRequests_one {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c es}
    (hm : ((r,c),es) ∈ (rs.zip b.functions).zip b.obligations) :
    (checkRequestResult r c es).accepted = true := by
  rw [checkRequests_eq] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 ((r,c),es) hm

/-- Exact bundle lengths give every requested unit its supplemental evidence. -/
theorem checkRequests_pair {rs : List (SourceRequest σ ι)} {b : Bundle ι}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) :
    ∃ es, ((r,c),es) ∈ (rs.zip b.functions).zip b.obligations ∧
      (checkRequestResult r c es).accepted = true := by
  have counts := h
  rw [checkRequests_eq] at counts
  have lengths := (Bool.and_eq_true_iff.mp counts).1
  simp only [Bool.and_eq_true, beq_iff_eq] at lengths
  have hl : (rs.zip b.functions).length = b.obligations.length := by
    simp only [List.length_zip, ← lengths.1, lengths.2, Nat.min_self]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hib : i < b.obligations.length := hl ▸ (List.getElem?_eq_some_iff.mp hi).1
  let es := b.obligations[i]'hib
  have hz : ((rs.zip b.functions).zip b.obligations)[i]? = some ((r,c),es) :=
    List.getElem?_zip_eq_some.mpr ⟨hi, by simp [es, hib]⟩
  have hm' := List.mem_of_getElem? hz
  exact ⟨es, hm', checkRequests_one h hm'⟩

/-- Source acceptance has the graph, assertion and supplemental premises for every unit. -/
theorem checkRequests_accepted_iff (rs : List (SourceRequest σ ι)) (b : Bundle ι) :
    checkRequests rs b = true ↔
      rs.length = b.functions.length ∧ rs.length = b.obligations.length ∧
      (∀ r c, (r,c) ∈ rs.zip b.functions → verify r.toRequest c r.checker = true ∧ checkAssertions r c = true) ∧
      (∀ r c es, ((r,c),es) ∈ (rs.zip b.functions).zip b.obligations →
        ∃ table, codeTable r.toRequest c = some table ∧
          ExpressionClaims.checkAllUsing (RequestJson.graph r.toRequest) (StoreView.images r.types)
            (StoreView.valid r.types) r.obligations es (GraphCode.admits table) = true) := by
  constructor
  · intro h
    have counts := h
    rw [checkRequests_eq] at counts
    simp only [Bool.and_eq_true, beq_iff_eq] at counts
    refine ⟨counts.1.1, counts.1.2, ?_, ?_⟩
    · intro r c hm
      obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
      have hp := (checkRequestResult_accepted_iff _ _ _).mp hunit
      exact ⟨hp.1, hp.2.1⟩
    · intro r c es hm
      exact ((checkRequestResult_accepted_iff _ _ _).mp (checkRequests_one h hm)).2.2
  · rintro ⟨hf, ho, hu, he⟩
    rw [checkRequests_eq]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨hf, ho⟩, ?_⟩
    intro triple hm
    rcases triple with ⟨⟨r,c⟩,es⟩
    have hp := hu r c (List.of_mem_zip hm).1
    exact (checkRequestResult_accepted_iff _ _ _).mpr ⟨hp.1, hp.2, he r c es hm⟩

/-- At a graph checkpoint, the proved state invariant entails the assertion
reconstructed from source claims, not merely a producer-selected context. -/
theorem checkRequests_assertions {rs : List (SourceRequest σ ι)} {b : (Bundle ι)}
    (hc : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    {l k n W heap ρ} (hr : (l,k) ∈ r.assertions)
    (hs : StateOk (RequestJson.graph r.toRequest) r.result c.certificate n W heap (.at l ρ)) :
    HeapKnowledge.Holds k ρ heap := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair hc hm
  have hc := (checkRequestResult_accepted_iff _ _ _).mp hunit
  obtain ⟨node,hn,_,hk⟩ := hs
  exact checkAssertions_sound hc.2.1 hr hn hk

/-- Every accepted extracted function has the existing all-budget guarantee.
This does not assert semantic preservation of the source compiler. -/
theorem checkRequests_safe {rs : List (SourceRequest σ ι)} {b : (Bundle ι)}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) (n W heap ρ)
    (he : EnvOk (RequestJson.graph r.toRequest) r.inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W heap) :
    SafeGraph r.program (meaning (RequestJson.graph r.toRequest) r.result) n W heap (.at r.start ρ) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  exact verify_safe ((checkRequestResult_accepted_iff _ _ _).mp hunit).1 n W heap ρ he hw hh

/-- A generic body is safe at every assignment admitted by its source signature. -/
theorem checkRequests_safe_at {rs : List (SourceRequest σ ι)} {b : (Bundle ι)}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    (η : PositiveGraphs.MixedAssignment ι) (admitted : r.Admits η) (n W heap ρ)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs ρ n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap) :
    SafeGraph r.program (meaning (reassign (RequestJson.graph r.toRequest) η) r.result) n W heap
      (.at r.start ρ) := by
  obtain ⟨es, _, hunit⟩ := checkRequests_pair h hm
  have checked := ((checkRequestResult_accepted_iff _ _ _).mp hunit).1
  cases hq : r.qualification with
  | none =>
    simp only [SourceRequest.checker, hq] at checked
    exact verify_safe_at checked η n W heap ρ he hw hh
  | some q =>
    simp only [SourceRequest.checker, hq, QualifiedBody.checker] at checked
    simp only [SourceRequest.Admits, hq, QualifiedBody.Admits] at admitted
    obtain ⟨θ, As, length, allowed, bounded, rfl⟩ := admitted
    exact verify_qualified_safe_at q.source q.domain q.body q.check_eq checked
      θ As length allowed bounded n W heap ρ he hw hh

/-- Every supplemental claim is a derivable sequent in the same calculus. -/
theorem checkRequests_obligations {rs : List (SourceRequest σ ι)} {b : (Bundle ι)}
    (h : checkRequests rs b = true) {r c es} (hm : ((r,c),es) ∈ (rs.zip b.functions).zip b.obligations)
    {q e} (hq : (q,e) ∈ r.obligations.zip es) :
    HasTyUsing (RequestJson.graph r.toRequest) (StoreView.images r.types) q.sequent.context q.sequent.term
      q.sequent.type := by
  obtain ⟨_, _, table, ht, ho⟩ := (checkRequestResult_accepted_iff _ _ _).mp (checkRequests_one h hm)
  exact ExpressionClaims.checkAll_sound ho (codeTable_sound ht) hq

/-- The source region represented by a graph, for checks on synthetic nodes. -/
def sourceMapRegion (sourceMap : SourceMap) : Option SourceMapEntry :=
  sourceMap.foldl (fun found next => match found, next with
    | none, next => next
    | found, none => found
    | some a, some b => some (SourceMapEntry.mk
        (min a.pos.1 b.pos.1, max a.pos.2 b.pos.2) "certificate-check" none [])) none

/-- Diagnostic provenance selects an actual source point or its enclosing graph region. -/
@[nospecialize] def validationOrigin (r : SourceRequest σ ι) (frames : List ProgramCertificates.CheckFrame) :
    Option SourceMapEntry :=
  match frames with
  | [.node label] => ((r.sourceMap[label]?).bind id) <|> sourceMapRegion r.sourceMap
  | [.code index, .node label] =>
      ((r.codeSources[index]?).bind fun code =>
        ((code.sourceMap[label]?).bind id) <|> sourceMapRegion code.sourceMap) <|> sourceMapRegion r.sourceMap
  | [.code index] => ((r.codeSources[index]?).bind fun code => sourceMapRegion code.sourceMap) <|>
      sourceMapRegion r.sourceMap
  | [.obligation index] => (r.obligations[index]?).map fun q =>
      SourceMapEntry.mk q.pos q.role none []
  | [] | .node _ :: _ | .code _ :: _ | .obligation _ :: _ | .request _ :: _ => sourceMapRegion r.sourceMap

/-- Report the retained comparison through the source map; validation is not rerun. -/
@[nospecialize] def validationFailure (rs : List (SourceRequest σ ι))
    (checked : ProgramCertificates.CheckResult ι Unit) (fallback : String) : String := Id.run do
  let some stop := checked.exhaustion | return fallback
  let .request index :: frames := stop.frames | return "exhausted certificate check has no enclosing source request"
  let some r := rs[index]? | return "exhausted certificate check names no source request"
  let some origin := validationOrigin r frames | return "exhausted certificate check has no source region"
  let p := StoreView.projection r.types (stop.source ++ stop.target).eraseDups
  return RequestJson.withDiagnostic "subtype search exhausted during certificate validation; result is inconclusive"
    ([("kind",toJson "direct-obligation"),("phase",toJson "certificate-check"),
      ("outcome",toJson (DiagnosticOutcome.exhausted stop.limit stop.rounds stop.visited)),
      ("id",toJson s!"subtype:{origin.pos.1}:{origin.pos.2}"),
      ("sourceMap",toJson { origin with context := [] }),
      ("judgment",(DirectObligation.Judgment.subtyping origin.pos (p.shown stop.source) (p.shown stop.target)).toJson),
      ("fuel",toJson (0 : Nat))] ++ p.fields)

end

section
open EquationStore

/-! ### Requests over the frozen equations -/

deriving instance ToJson, FromJson for DirectProof.Plan

/-- Translate labels through their JSON representation. Strict decoding
refuses a label outside the frozen equations. -/
private def relabel {α β : Type} [ToJson α] [FromJson β] [ToJson β] (a : α) : Except String β :=
  decodeStrict (toJson a)

/-- An extracted unit's request over the frozen equations. The program is
the extracted one; every label is read as `F`'s. -/
def SourceRequest.over (F : Frozen) (r : SourceRequest EquationStore.State Tree) :
    Except String (SourceRequest (Checked F.equations F.primitive)
      (CheckedLabel F.equations F.primitive)) := do
  let sourceScheme ← r.sourceScheme.mapM fun s => do
    return ({
      binders := ← relabel s.binders
      signatures := ← relabel s.signatures
      bounds := ← relabel s.bounds
      variadic := ← relabel s.variadic
      resolution := s.resolution } : PositiveGraphs.SchemeRow (CheckedLabel F.equations F.primitive))
  let obligations ← r.obligations.mapM fun o => do
    return ({ pos := o.pos, sequent := ← relabel o.sequent, plan := ← relabel o.plan,
              role := o.role, context := o.context } : ExpressionClaims.Required _)
  let claims ← relabel r.claims
  let result ← relabel r.result
  let inputs ← relabel r.inputs
  let codes ← relabel r.codes
  let hints ← relabel r.hints
  let nodePlans ← relabel r.nodePlans
  let request : RequestJson.Request (Checked F.equations F.primitive) (CheckedLabel F.equations F.primitive) :=
    { types := F.store, program := r.program, claims := claims, result := result, start := r.start,
      inputs := inputs, codes := codes }
  let qualification ← sourceScheme.mapM fun s => do
    let some context := F.store.resolution
      | throw "qualified source signature requires the native descriptor domain"
    let some body := SourceResolution.bodyChecking context.1 context.2 s (StoreView.images F.store)
      | throw "invalid descriptor groups in the source signature"
    return body
  return { toRequest := request, sourceScheme, qualification, obligations := obligations, sourceMap := r.sourceMap,
           assertions := r.assertions, cuts := r.cuts, hints := hints, codeSources := r.codeSources,
           nodePlans := nodePlans }

end

#print axioms checkRequests_assertions
#print axioms checkAssertions_cut
#print axioms checkAssertions_sound
#print axioms checkRequests_obligations
#print axioms checkRequests_safe
#print axioms checkRequests_safe_at
end Verification.SourceExtraction
