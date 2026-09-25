import Verification.Model.Programs.Parametricity

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

/-! ## A unit's table of checked code

Graph code is checked by the graph checker, and its creation is typed by
naming what was checked (`ProgramCertificates.Rule.funGraph`). A unit's
certificate therefore checks its codes in order, each against the table of the
ones before it — a code creates only code nested in it, whose check comes
first — and the unit's own graph against the whole table. -/

/-- A table as the evidence checker reads it. -/
def admits [DecidableEq ι] (table : List (CodeEntry ι)) (c : CodeEntry ι) : Bool :=
  table.contains c

/-- One code entry, checked at its signature from the frame the signature
describes, against an earlier table. -/
def codeChecked [DecidableEq ι] (G : NormalGraph ι) (table : List (CodeEntry ι))
    (c : CodeEntry ι) (C : ControlFlow.Certificate ι) : Bool :=
  decide (c.arity ≤ c.row.2.1.length) &&
    checkEntry G c.row.2.2 (program c.exprs c.conts) C c.start
      (bodyFrame c.arity c.row c.captures) (admits table)

theorem codeChecked_sound [DecidableEq ι] {G : NormalGraph ι} {table c C}
    (htable : ProgramCertificates.CodesSound G (admits table))
    (h : codeChecked G table c C = true) : c.Spec G := by
  simp only [codeChecked, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun n W heap L he hw hh =>
    goto_safe h.2 htable n W heap L .nul he hw hh⟩

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
      simp only [codeChecked, Parametricity.checkEntry_reassign]
    simp only [extendTable, hc, extendTable_reassign G η (table ++ [c]) rest]

theorem checkCodes_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι) (checks) :
    checkCodes (reassign G η) checks = checkCodes G checks :=
  extendTable_reassign G η [] checks

#print axioms safe_of_sim
#print axioms goto_safe
#print axioms checkCodes_sound
end Verification.Model.GraphCode
