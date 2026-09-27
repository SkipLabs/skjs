import Verification.Model.Programs.Parametricity
import Verification.Model.Programs.ExpressionEffects

/-! # Graph code: a closure whose body is a checked graph

A closure's code may be a control-flow graph (`CallCode.graph`), the body form
a module function has. Invoking it starts a run of that graph at its entry
(`Tm.goto`), which the term machine executes node by node (`Tm.frame`), with
the graph machine's transitions as its steps. This file proves that the two
machines agree: a run of graph code simulates `ControlFlow.Transition`
step for step, so the graph checker's safety theorem (`accepted_inputs_safe`)
is safety of the term that runs the code. -/
namespace Verification.Model.GraphCode
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules

/-- The graph a code's node lists describe. -/
def program (E : List Tm) (K : List (Continuation × Option Target)) : Program :=
  (E.zip K).map fun (e, k, x) => ⟨e, k, x⟩

theorem program_node {E : List Tm} {K : List (Continuation × Option Target)} {l : Nat}
    {node : Node} (h : (program E K)[l]? = some node) :
    E[l]? = some node.expression ∧ K[l]? = some (node.continuation, node.handler) := by
  simp only [program, List.getElem?_map] at h
  obtain ⟨⟨e, k, x⟩, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.getElem?_zip_eq_some.mp hz
  exact ⟨this.1, this.2⟩

theorem push_envOf (v : Tm) (L : List Tm) (d : Tm) : push v (envOf L d) = envOf (v :: L) d := by
  funext i; cases i <;> rfl

theorem mapEnv_envOf (m : Option (List Nat)) (L : List Tm) (d : Tm) :
    mapEnv m (envOf L d) = envOf (envMap m L d).1 (envMap m L d).2 := by
  funext i
  cases m with
  | none => rfl
  | some slots =>
    simp only [mapEnv, slot, envOf, envMap]
    by_cases hi : i < slots.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · have hn : slots[i]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hn]

/-- A term that runs graph code, and the graph machine's state it stands for. -/
inductive Sim (E : List Tm) (K : List (Continuation × Option Target)) : Tm → State → Prop where
  | goto : Sim E K (.goto E K l L d) (.at l (envOf L d))
  | frame : Sim E K (.frame E K t L d k x) (.eval t (envOf L d) k x)
  | done : isVal v = true → Sim E K v (.done v)
  | raised : isVal v = true → Sim E K (.throw v) (.raised v)

theorem sim_goto {E K l m L d} :
    Sim E K (.goto E K l (envMap m L d).1 (envMap m L d).2) (.at l (mapEnv m (envOf L d))) := by
  rw [mapEnv_envOf]; exact .goto

/-- Each transition of the graph is one step of the term that runs it. -/
theorem sim_step {E K ts s h h' s'} (hs : Sim E K ts s)
    (step : Transition (program E K) h s h' s') : ∃ ts', Step h ts h' ts' ∧ Sim E K ts' s' := by
  cases hs with
  | goto =>
    cases step with
    | enter hn =>
      obtain ⟨he, hk⟩ := program_node hn
      exact ⟨_, .gotoEnter he hk, .frame⟩
  | frame =>
    cases step with
    | expr st => exact ⟨_, .frameC st, .frame⟩
    | ret hv => exact ⟨_, .frameRet hv, .done hv⟩
    | bind hv =>
      refine ⟨_, .frameBind hv, ?_⟩
      rw [push_envOf]; exact sim_goto
    | effect hv => exact ⟨_, .frameEffect hv, sim_goto⟩
    | yes => exact ⟨_, .frameYes, sim_goto⟩
    | no => exact ⟨_, .frameNo, sim_goto⟩
    | yesBind =>
      refine ⟨_, .frameYesBind, ?_⟩
      rw [push_envOf]; exact sim_goto
    | noBind =>
      refine ⟨_, .frameNoBind, ?_⟩
      rw [push_envOf]; exact sim_goto
    | tagBind hv =>
      refine ⟨_, .frameTag hv, ?_⟩
      rw [push_envOf]; exact sim_goto
    | handle hr =>
      refine ⟨_, .frameHandle hr, ?_⟩
      rw [push_envOf]; exact sim_goto
    | raise hr => exact ⟨_, .frameRaise hr, .raised (raises_val hr)⟩
  | done hv => cases step
  | raised hv => cases step

/-- **The term running graph code is as safe as the graph.** -/
theorem safe_of_sim {E K T} : ∀ (n : Nat) (W : WorldT n) (h : Heap) {ts s},
    Sim E K ts s → SafeGraph (program E K) T n W h s → Safe T n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s hs hg
    rcases hg with (⟨v, rfl, hv, hT⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, step, hh, hg⟩
    · cases hs; exact Or.inl (Or.inl ⟨hv, hT⟩)
    · cases hs with
      | raised hv => exact Or.inl (Or.inr ⟨v, .throwV hv, hsc⟩)
    · obtain ⟨ts', st, hs'⟩ := sim_step hs step
      exact Or.inr ⟨U, h', ts', hx, hu, st, hh, ih U h' hs' hg⟩

/-- A graph run started at an entry the checker accepted is safe. -/
theorem goto_safe {G : NormalGraph ι} [DecidableEq ι] {Rty : Ty ι}
    {E K C start inputs} {codes : CodeEntry ι → Bool}
    (hc : checkEntry G Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h) :
    Safe (meaning G Rty) n W h (.goto E K start L d) :=
  safe_of_sim n W h .goto (accepted_inputs_safe hc n W h (envOf L d) he hw hh hcodes)

/-- A normal-return postcondition up to the current budget, independent of the
world chosen by a parallel safety derivation. Throws impose no postcondition. -/
def ReturnsPost (Q : HeapObservations.Post) (n : Nat) (h : Heap) (t : Tm) : Prop :=
  ∀ k h' v, k < n → HeapObservations.Steps k h t h' v → isVal v = true → Q h' v

theorem returnsPost_of_safePost {T Q} : ∀ {n W h t},
    HeapObservations.SafePost T Q n W h t → ReturnsPost Q n h t := by
  intro n
  induction n with
  | zero => intro W h t hs k h' v hk; omega
  | succ n ih =>
    intro W h t hs k h' v hk run hv
    cases run with
    | refl =>
      rcases hs with (⟨_, _, hq⟩ | hr) | ⟨_, _, _, _, _, st, _, _⟩
      · exact hq
      · exact absurd hr (val_not_thrown hv)
      · exact False.elim (value_no_step hv st)
    | next st run =>
      rcases hs with (⟨ht, _, _⟩ | hr) | ⟨U, h'', t'', _, _, st', _, hs'⟩
      · exact False.elim (value_no_step ht st)
      · exact absurd st hr.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        exact ih hs' _ _ _ (by omega) run hv

theorem ReturnsPost.step {Q n h t h' t'} (hp : ReturnsPost Q (n+1) h t)
    (st : Step h t h' t') : ReturnsPost Q n h' t' := by
  intro k h'' v hk run hv
  exact hp (k+1) h'' v (by omega) (.next st run) hv

theorem ReturnsPost.value {Q n h v} (hp : ReturnsPost Q (n+1) h v)
    (hv : isVal v = true) : Q h v := hp 0 h v (by omega) .refl hv

/-- An effect annotation on a checked graph node. The precondition is the same
point context and knowledge that ordinary graph checking established. -/
def NodePreserves [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (t : Tm) : Prop :=
  ∀ n W h ρ, EnvOk G (entry c) ρ n W → HeapKnowledge.Holds c.knowledge ρ h →
    WorldAdm W → HeapOk n W h →
    HeapObservations.SafePost (meaning G (result c))
      (CallEffects.Effect.preservesInputHeap.post h) n W h (instantiate 0 ρ t)

/-- While a call is running its entry heap need not be preserved yet. Only the
postcondition on normal return can justify the next graph node. -/
def PreservingState (initial : Heap) (n : Nat) (h : Heap) : State → Prop
  | .at .. | .done _ => initial.IsPrefix h
  | .eval t _ _ handler => handler = none ∧
      ReturnsPost (CallEffects.Effect.preservesInputHeap.post initial) n h t
  | .raised _ => True

theorem preserving_step [DecidableEq ι] {G : NormalGraph ι} {Rty : Ty ι} {P : Program} {C : Certificate ι}
    (hnodes : ∀ (l : Nat) (node : Node) (c : NodeEvidence ι), P[l]? = some node → C[l]? = some c →
      node.handler = none ∧ NodePreserves G c node.expression)
    {initial n W h s h' s'} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : StateOk G Rty C (n+1) W h s) (hp : PreservingState initial (n+1) h s)
    (st : Transition P h s h' s') : PreservingState initial n h' s' := by
  cases st with
  | enter hn =>
    obtain ⟨c, hc, he, hf⟩ := hs
    obtain ⟨hx, ht⟩ := hnodes _ _ c hn hc
    refine ⟨hx, ?_⟩
    apply returnsPost_of_safePost
    apply HeapObservations.weaken (fun _ _ hpost => hp.trans hpost)
    exact ht n _ h _ (he.transfer n (Nat.le_succ n) _ (WExt_refl _)) hf
      (WorldAdm_trunc _ hw) (HeapOk_trunc n W h hh)
  | expr st => exact ⟨hp.1, hp.2.step st⟩
  | ret hv | bind hv | effect hv | tagBind hv => exact hp.2.value hv
  | yes | no | yesBind | noBind => exact hp.2.value rfl
  | handle _ => cases hp.1
  | raise _ => trivial

/-- The effect proof reuses ordinary graph progress and its point assertions.
There is one control-flow checker, including for cycles and branch refinements. -/
theorem preserving_safe_of_sim [DecidableEq ι] {G : NormalGraph ι} {Rty : Ty ι} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι}
    {codes : CodeEntry ι → Bool} (hg : checkGraph G Rty (program E K) C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hnodes : ∀ (l : Nat) (node : Node) (c : NodeEvidence ι), (program E K)[l]? = some node → C[l]? = some c →
      node.handler = none ∧ NodePreserves G c node.expression) :
    ∀ n W h ts s initial, Sim E K ts s → WorldAdm W → HeapOk n W h →
      StateOk G Rty C n W h s → PreservingState initial n h s →
      HeapObservations.SafePost (meaning G Rty)
        (CallEffects.Effect.preservesInputHeap.post initial) n W h ts := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ts s initial sim hw hh hs hp
    rcases state_progress hg hcodes hw hh hs with
      (⟨v, rfl, hv, ht⟩ | ⟨v, rfl, hsc⟩) | ⟨U, h', s', hx, hu, st, hok, hs'⟩
    · cases sim; exact .inl (.inl ⟨hv, ht, hp⟩)
    · cases sim with
      | raised hv => exact .inl (.inr ⟨v, .throwV hv, hsc⟩)
    · obtain ⟨ts', step, sim'⟩ := sim_step sim st
      exact .inr ⟨U, h', ts', hx, hu, step, hok,
        ih U h' ts' s' initial sim' hu hok hs'
          (preserving_step hnodes hw hh hs hp st)⟩

theorem goto_preserving [DecidableEq ι] {G : NormalGraph ι} {Rty : Ty ι} {E : List Tm} {K : List (Continuation × Option Target)}
    {C : Certificate ι} {start inputs}
    {codes : CodeEntry ι → Bool}
    (hc : checkEntry G Rty (program E K) C start inputs codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hnodes : ∀ (l : Nat) (node : Node) (c : NodeEvidence ι), (program E K)[l]? = some node → C[l]? = some c →
      node.handler = none ∧ NodePreserves G c node.expression)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W)
    (hh : HeapOk n W h) :
    HeapObservations.SafePost (meaning G Rty)
      (CallEffects.Effect.preservesInputHeap.post h) n W h (.goto E K start L d) := by
  simp only [checkEntry, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i c hstart
    have hem : entry c = inputs ∧ c.knowledge = ⟨[],[],[]⟩ := of_decide_eq_true hx
    apply preserving_safe_of_sim hc.1 hcodes hnodes n W h _ _ h .goto hw hh
    · refine ⟨c, hstart, ?_, ?_⟩
      · simpa only [hem.1] using he
      · rw [hem.2]; exact HeapKnowledge.empty _ h
    · exact ⟨[], by simp⟩
  · contradiction

/-! ## A unit's table of checked code

Graph code is checked by the graph checker, and its creation is typed by
naming what was checked (`ProgramCertificates.Rule.funGraph`). A unit's
certificate therefore checks its codes in order, each against the table of the
ones before it — a code creates only code nested in it, whose check comes
first — and the unit's own graph against the whole table. -/

/-- A table as the evidence checker reads it. -/
def admits [DecidableEq ι] (table : List (CodeEntry ι)) (c : CodeEntry ι) : Bool :=
  table.contains c

/-- Each executed node must establish preservation on normal return. A handler
could turn a throwing call into a normal return after untracked mutation, so
this composition rule admits only graphs without handlers. Pure graphs retain
the independent operational rule, which also covers their handlers. -/
def compositionalChecked (G : NormalGraph ι) (P : Program) (C : Certificate ι) : Bool :=
  (P.zip C).all fun (node,c) => node.handler.isNone &&
    ProgramCertificates.checkScope (entry c).length node.expression &&
    ExpressionEffects.check G (entry c) node.expression

@[simp] theorem compositionalChecked_reassign (G : NormalGraph ι) (η : MixedAssignment ι)
    (P : Program) (C : Certificate ι) :
    compositionalChecked (reassign G η) P C = compositionalChecked G P C := by
  simp only [compositionalChecked, ExpressionEffects.check, ExpressionEffects.readable,
    Parametricity.expand_reassign]

/-- Definition effects supplement, rather than replace, ordinary safety. -/
def effectChecked (G : NormalGraph ι) (c : CodeEntry ι) (C : Certificate ι) : Bool :=
  match c.row.effect with
  | .unrestricted => true
  | .preservesInputHeap => c.exprs.all Purity.pureTerm ||
      compositionalChecked G (program c.exprs c.conts) C

@[simp] theorem effectChecked_reassign (G : NormalGraph ι) (η : MixedAssignment ι)
    (c : CodeEntry ι) (C : Certificate ι) :
    effectChecked (reassign G η) c C = effectChecked G c C := by
  simp only [effectChecked, compositionalChecked_reassign]

/-- One code entry, checked at its signature from the frame the signature
describes, against an earlier table. -/
def codeChecked [DecidableEq ι] (G : NormalGraph ι) (table : List (CodeEntry ι))
    (c : CodeEntry ι) (C : ControlFlow.Certificate ι) : Bool :=
  decide (c.arity ≤ c.row.arguments.length) && effectChecked G c C &&
    checkEntry G c.row.result (program c.exprs c.conts) C c.start
      (codeFrame c.arity c.row c.captures c.store) (admits table)

/-- A checked entry meets its signature in the graph reassigned at every
assignment: the check reads none (`Parametricity.checkEntry_reassign`). -/
theorem codeChecked_sound [DecidableEq ι] {G : NormalGraph ι} {table c C}
    (htable : ProgramCertificates.CodesSound G (admits table))
    (h : codeChecked G table c C = true) : ∀ η, c.Spec (reassign G η) := by
  intro η
  simp only [codeChecked, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc : checkEntry (reassign G η) c.row.result (program c.exprs c.conts) C c.start
      (codeFrame c.arity c.row c.captures c.store) (admits table) = true := by
    exact (Parametricity.checkEntry_reassign G η _ _ _ _ _ _).trans h.2
  have ht : ProgramCertificates.CodesSound (reassign G η) (admits table) :=
    fun e he η' => htable e he η'
  refine ⟨h.1.1, ?_⟩
  intro n W heap L he hw hh hvalues
  have hs := goto_safe hc ht n W heap L .nul he hw hh
  cases heffect : c.row.effect with
  | unrestricted =>
    simpa [heffect, CallEffects.Effect.post] using HeapObservations.forget hs
  | preservesInputHeap =>
    have hp : c.exprs.all Purity.pureTerm = true ∨
        compositionalChecked (reassign G η) (program c.exprs c.conts) C = true := by
      simpa [effectChecked, heffect, Bool.or_eq_true] using h.1.2
    rcases hp with hp | hp
    · have hp : ∀ e ∈ c.exprs, Purity.pureTerm e = true := List.all_eq_true.mp hp
      simpa [heffect] using CallEffects.pure_safe (.goto hp hvalues rfl) hs
    · apply goto_preserving hc ht _ n W heap L .nul he hw hh
      intro l node point hn hpoint
      have hzip : ((program c.exprs c.conts).zip C)[l]? = some (node,point) :=
        List.getElem?_zip_eq_some.mpr ⟨hn,hpoint⟩
      have hmem := List.mem_of_getElem? hzip
      have hp := List.all_eq_true.mp hp (node,point) hmem
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      refine ⟨hp.1.1, ?_⟩
      intro j V h' ρ henv hknowledge hworld hheap
      have hgraph : checkGraph (reassign G η) c.row.result (program c.exprs c.conts) C
          (admits table) = true := by
        have hchecked := hc
        simp only [checkEntry, Bool.and_eq_true] at hchecked
        exact hchecked.1
      obtain ⟨actual,hactual,hterm,-⟩ := graph_node hgraph ht hpoint
      cases hn.symm.trans hactual
      exact ExpressionEffects.sound hp.2 hp.1.2 henv hheap
        (HeapObservations.erase (hterm j V h' ρ henv hknowledge hworld hheap))

/-- Check codes in order, each against the table of those before it. -/
def extendTable [DecidableEq ι] (G : NormalGraph ι) :
    List (CodeEntry ι) → List (CodeEntry ι × ControlFlow.Certificate ι) → Option (List (CodeEntry ι))
  | table, [] => some table
  | table, (c, C) :: rest =>
    if codeChecked G table c C then extendTable G (table ++ [c]) rest else none

theorem extendTable_sound [DecidableEq ι] {G : NormalGraph ι} :
    ∀ {table checks result}, ProgramCertificates.CodesSound G (admits table) →
      extendTable G table checks = some result →
      ProgramCertificates.CodesSound G (admits result)
  | table, [], result, ht, h => by
    simp only [extendTable, Option.some.injEq] at h; subst h; exact ht
  | table, (c, C) :: rest, result, ht, h => by
    simp only [extendTable] at h
    split at h
    · rename_i hc
      apply extendTable_sound _ h
      intro e he
      simp only [admits, List.contains_append, Bool.or_eq_true, List.contains_cons,
        List.contains_nil, Bool.or_false, beq_iff_eq] at he
      rcases he with he | rfl
      · exact ht e he
      · exact codeChecked_sound ht hc
    · contradiction

/-- A unit's codes, checked from the empty table. -/
def checkCodes [DecidableEq ι] (G : NormalGraph ι) (checks : List (CodeEntry ι × ControlFlow.Certificate ι)) :
    Option (List (CodeEntry ι)) :=
  extendTable G [] checks

theorem checkCodes_sound [DecidableEq ι] {G : NormalGraph ι} {checks table}
    (h : checkCodes G checks = some table) : ProgramCertificates.CodesSound G (admits table) :=
  extendTable_sound (fun c hc => by simp [admits] at hc) h

/-- A table checks as it does at every reassignment of the graph's parameter
rows: no code check reads the assignment (`Parametricity`). -/
theorem extendTable_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι) :
    ∀ table checks, extendTable (reassign G η) table checks = extendTable G table checks
  | table, [] => rfl
  | table, (c, C) :: rest => by
    have hc : codeChecked (reassign G η) table c C = codeChecked G table c C := by
      simp only [codeChecked, effectChecked_reassign, Parametricity.checkEntry_reassign]
    simp only [extendTable, hc, extendTable_reassign G η (table ++ [c]) rest]

theorem checkCodes_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι) (checks) :
    checkCodes (reassign G η) checks = checkCodes G checks :=
  extendTable_reassign G η [] checks

#print axioms safe_of_sim
#print axioms goto_safe
#print axioms checkCodes_sound
end Verification.Model.GraphCode
