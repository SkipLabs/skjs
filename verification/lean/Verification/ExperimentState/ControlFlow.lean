import Verification.ExperimentState.ObjectCoherence
import Verification.ExperimentState.BranchRefinement
import Verification.ExperimentState.HeapExpressionRules

/-! A finite control-flow graph over the existing expression language. Expression
steps use the existing heap machine. Dispatch and transfers are explicit steps,
so cycles consume execution budget without requiring invariant inference. -/
namespace Verification.ExperimentState.ControlFlow
open ProgramTyping PositiveGraphs PositiveRules PointClaims ProgramCertificates BranchRefinement

/-- The destination and its slot map are executable program data, not evidence. -/
structure Target where
  label : Nat
  mapping : Mapping := none
  deriving DecidableEq, Repr

instance (n : Nat) : OfNat Target n := ⟨⟨n, none⟩⟩

inductive Continuation where
  | ret
  | bind (next : Target)
  | effect (next : Target)
  | branch (yes no : Target)
  /-- Dispatch and bind the tested Boolean before applying the destination map. -/
  | branchBind (yes no : Target)
  /-- Test the returned value itself, bind it, then apply the destination map. -/
  | tagBind (test : Tag) (yes no : Target)
  deriving DecidableEq, Repr

structure Node where
  expression : Tm
  continuation : Continuation
  deriving DecidableEq, Repr

abbrev Program := List Node

structure NodeEvidence (ι : Type) where
  expression : Evidence ι
  edges : List (EdgeEvidence ι)
  /-- Supplied precondition; incoming edges must establish it. -/
  knowledge : HeapKnowledge.Knowledge := ⟨[],[],[]⟩
  /-- None uses ordinary evidence; some selects a checked effect rule. -/
  effect : Option (HeapExpressionRules.StepEvidence ι) := none
  output : HeapKnowledge.Knowledge := ⟨[],[],[]⟩

abbrev Certificate (ι : Type) := List (NodeEvidence ι)
def entry (c : NodeEvidence ι) := (claim c.expression).context
def result (c : NodeEvidence ι) := (claim c.expression).type

inductive State where
  | at (label : Nat) (env : Env)
  | eval (term : Tm) (env : Env) (continuation : Continuation)
  | done (value : Tm)

inductive Transition (P : Program) : Heap → State → Heap → State → Prop where
  | enter : P[l]? = some node →
      Transition P h (.at l ρ) h (.eval (instantiate 0 ρ node.expression) ρ node.continuation)
  | expr : Step h t h' t' → Transition P h (.eval t ρ k) h' (.eval t' ρ k)
  | ret : isVal v = true → Transition P h (.eval v ρ .ret) h (.done v)
  | bind : isVal v = true → Transition P h (.eval v ρ (.bind l)) h (.at l.label (mapEnv l.mapping (push v ρ)))
  | effect : isVal v = true → Transition P h (.eval v ρ (.effect l)) h (.at l.label (mapEnv l.mapping ρ))
  | yes : Transition P h (.eval .tru ρ (.branch y n)) h (.at y.label (mapEnv y.mapping ρ))
  | no : Transition P h (.eval .fls ρ (.branch y n)) h (.at n.label (mapEnv n.mapping ρ))

  | yesBind : Transition P h (.eval .tru ρ (.branchBind y n)) h (.at y.label (mapEnv y.mapping (push .tru ρ)))
  | noBind : Transition P h (.eval .fls ρ (.branchBind y n)) h (.at n.label (mapEnv n.mapping (push .fls ρ)))

  | tagBind : isVal v = true →
      Transition P h (.eval v ρ (.tagBind tag y n)) h
        (.at (if tagHolds tag v then y else n).label
          (mapEnv (if tagHolds tag v then y else n).mapping (push v ρ)))

def SafeGraph (P : Program) (T : Fam) : (n : Nat) → WorldT n → Heap → State → Prop
  | 0, _, _, _ => True
  | n+1, W, h, s =>
    (∃ v, s = .done v ∧ isVal v = true ∧ T (n+1) W v) ∨
    ∃ U : WorldT n, ∃ h' s', WExt (trunc n (Nat.le_succ n) W) U ∧
      WorldAdm U ∧ Transition P h s h' s' ∧ HeapOk n U h' ∧ SafeGraph P T n U h' s'

/-- Target existence is checked against both the actual graph and its claims. -/
def checkTarget [DecidableEq ι] (G : NormalGraph ι) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := ⟨[],[],[]⟩) : Bool :=
  match P[target.label]?, C[target.label]? with
  | some _, some c => checkMapped G Γ (entry c) target.mapping p && HeapKnowledge.check facts c.knowledge target.mapping
  | _, _ => false

def checkBranchTarget [DecidableEq ι] (G : NormalGraph ι) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := ⟨[],[],[]⟩) : Bool :=
  match P[target.label]?, C[target.label]? with
  | some _, some c => checkObserved G Γ (entry c) 0 o target.mapping p && HeapKnowledge.check (HeapKnowledge.observe facts 0 o) c.knowledge target.mapping
  | _, _ => false


def checkNode [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι) : Bool :=
  decide ((claim c.expression).term = node.expression) &&
  checkScope (entry c).length node.expression &&
  decide (HeapExpressionRules.checkStep G (claim c.expression) c.knowledge
    (c.effect.getD (.ordinary c.expression)) = some c.output) &&
  match node.continuation, c.edges with
  | .ret, [] => decide (result c = Rty)
  | .bind l, [p] => checkTarget G P C (result c :: entry c) l p c.output
  | .effect l, [p] => checkTarget G P C (entry c) l p (HeapKnowledge.dropResult c.output)
  | .branch y n, [py,pn] => decide (expand G (result c) = [.bool]) &&
      checkTarget G P C (entry c) y py (HeapKnowledge.dropResult c.output) && checkTarget G P C (entry c) n pn (HeapKnowledge.dropResult c.output)
  | .branchBind y n, [py,pn] => onlyBoolean G (result c) &&
      checkBranchTarget G P C (result c :: entry c) (.boolean true) y py c.output &&
      checkBranchTarget G P C (result c :: entry c) (.boolean false) n pn c.output
  | .tagBind t y n, [py,pn] =>
      checkBranchTarget G P C (result c :: entry c) (.tag t true) y py c.output &&
      checkBranchTarget G P C (result c :: entry c) (.tag t false) n pn c.output
  | _, _ => false

/-- Enumeration comes from the program, not a certificate-supplied edge list. -/
def checkGraph [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) : Bool :=
  decide (P.length = C.length) && (List.range P.length).all (fun l =>
    match P[l]?, C[l]? with
    | some node, some c => checkNode G Rty P C node c
    | _, _ => false) && P.all (fun node => ObjectCoherence.sourceTerm node.expression)

def TargetOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι) (Γ : List (Ty ι)) (l : Target) (facts : HeapKnowledge.Knowledge) : Prop :=
  ∃ c, C[l.label]? = some c ∧ MappedCovers G Γ (entry c) l.mapping ∧ HeapKnowledge.check facts c.knowledge l.mapping = true

def BranchTargetOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (l : Target) (facts : HeapKnowledge.Knowledge) : Prop :=
  ∃ c, C[l.label]? = some c ∧ ObservedCovers G Γ (entry c) 0 o l.mapping ∧ HeapKnowledge.check (HeapKnowledge.observe facts 0 o) c.knowledge l.mapping = true


def ContinuationOk [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (A : Ty ι) (facts : HeapKnowledge.Knowledge) : Continuation → Prop
  | .ret => A = Rty
  | .bind l => TargetOk G C (A :: Γ) l facts
  | .effect l => TargetOk G C Γ l (HeapKnowledge.dropResult facts)
  | .branch y n => Represents G A .bool ∧ TargetOk G C Γ y (HeapKnowledge.dropResult facts) ∧ TargetOk G C Γ n (HeapKnowledge.dropResult facts)
  | .branchBind y n => onlyBoolean G A = true ∧
      BranchTargetOk G C (A::Γ) (.boolean true) y facts ∧ BranchTargetOk G C (A::Γ) (.boolean false) n facts
  | .tagBind t y n => BranchTargetOk G C (A::Γ) (.tag t true) y facts ∧
      BranchTargetOk G C (A::Γ) (.tag t false) n facts

theorem target_sound [DecidableEq ι] {G : NormalGraph ι} {P C Γ l p facts}
    (hc : checkTarget G P C Γ l p facts = true) : TargetOk G C Γ l facts := by
  unfold checkTarget at hc
  split at hc
  · rename_i node c hn he
    simp only [Bool.and_eq_true] at hc
    exact ⟨c, he, checkMapped_sound hc.1, hc.2⟩
  · contradiction

theorem branch_target_sound [DecidableEq ι] {G : NormalGraph ι} {P C Γ q l p facts}
    (hc : checkBranchTarget G P C Γ q l p facts = true) : BranchTargetOk G C Γ q l facts := by
  unfold checkBranchTarget at hc
  split at hc
  · simp only [Bool.and_eq_true] at hc
    exact ⟨_, by assumption, checkObserved_sound hc.1, hc.2⟩
  · contradiction


def ExpressionOk [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (t : Tm) : Prop :=
  ∀ n W h ρ, EnvOk G (entry c) ρ n W → HeapKnowledge.Holds c.knowledge ρ h →
    WorldAdm W → HeapOk n W h → HeapObservations.SafePost (meaning G (result c))
      (fun h' v => HeapKnowledge.Holds c.output (push v ρ) h') n W h (instantiate 0 ρ t)

theorem node_sound [DecidableEq ι] {G : NormalGraph ι} {Rty P C node c}
    (hc : checkNode G Rty P C node c = true) :
    ExpressionOk G c node.expression ∧
    ContinuationOk G Rty C (entry c) (result c) c.output node.continuation := by
  simp only [checkNode, Bool.and_eq_true, decide_eq_true_eq] at hc
  refine ⟨?_, ?_⟩
  · intro n W h ρ he hf hw hh
    have ht := HeapExpressionRules.checkStep_sound hc.1.2 he hf hw hh
    simpa only [entry, result, hc.1.1.1] using ht
  · have hk := hc.2
    split at hk <;> (try (rename_i hcont hedges; rw [hcont]))
    · exact (of_decide_eq_true hk : result c = Rty)
    · exact target_sound hk
    · exact target_sound hk
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact ⟨hk.1.1, target_sound hk.1.2, target_sound hk.2⟩
    · simp only [Bool.and_eq_true] at hk
      exact ⟨hk.1.1, branch_target_sound hk.1.2, branch_target_sound hk.2⟩
    · simp only [Bool.and_eq_true] at hk
      exact ⟨branch_target_sound hk.1, branch_target_sound hk.2⟩
    · contradiction

theorem graph_node [DecidableEq ι] {G : NormalGraph ι} {Rty P C c} {l : Nat}
    (hg : checkGraph G Rty P C = true) (hc : C[l]? = some c) :
    ∃ node : Node, P[l]? = some node ∧ ExpressionOk G c node.expression ∧
      ContinuationOk G Rty C (entry c) (result c) c.output node.continuation := by
  simp only [checkGraph, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hg
  have hg := hg.1
  have hl : l < P.length := by
    rw [hg.1]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have hn : P[l]? = some (P[l]'hl) := by simp [hl]
  have h := hg.2 l (List.mem_range.mpr hl)
  rw [hn, hc] at h
  exact ⟨_, hn, node_sound h⟩

/-- A state assertion used only in the global safety proof. -/
def StateOk [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι) (C : Certificate ι)
    (n : Nat) (W : WorldT n) (h : Heap) : State → Prop
  | .at l ρ => ∃ c, C[l]? = some c ∧ EnvOk G (entry c) ρ n W ∧ HeapKnowledge.Holds c.knowledge ρ h
  | .eval t ρ k => ∃ Γ A out, EnvOk G Γ ρ n W ∧
      HeapObservations.SafePost (meaning G A) (fun h' v => HeapKnowledge.Holds out (push v ρ) h') n W h t ∧
      ContinuationOk G Rty C Γ A out k
  | .done v => isVal v = true ∧ meaning G Rty n W v

theorem target_state [DecidableEq ι] {G : NormalGraph ι} {Rty C Γ l ρ n W h facts}
    (ht : TargetOk G C Γ l facts) (he : EnvOk G Γ ρ n W) (hf : HeapKnowledge.Holds facts ρ h) : StateOk G Rty C n W h (.at l.label (mapEnv l.mapping ρ)) := by
  obtain ⟨c, hc, hcov, hfact⟩ := ht
  exact ⟨c, hc, hcov.env he, HeapKnowledge.check_sound hfact hf⟩

theorem branch_target_state [DecidableEq ι] {G : NormalGraph ι} {Rty C Γ q l ρ n W h facts}
    (ht : BranchTargetOk G C Γ q l facts) (he : EnvOk G Γ ρ n W)
    (hq : q.holds (ρ 0)) (hf : HeapKnowledge.Holds facts ρ h) :
    StateOk G Rty C n W h (.at l.label (mapEnv l.mapping ρ)) := by
  obtain ⟨c,hc,hcov,hfact⟩ := ht
  exact ⟨c,hc,hcov.env he hq, HeapKnowledge.check_sound hfact (HeapKnowledge.observe_holds hf hq)⟩

/-- Global safety is by execution budget, not by acyclicity or graph unfolding. -/
theorem state_safe [DecidableEq ι] {G : NormalGraph ι} {Rty P C}
    (hg : checkGraph G Rty P C = true) :
    ∀ n W h s, WorldAdm W → HeapOk n W h → StateOk G Rty C n W h s →
      SafeGraph P (meaning G Rty) n W h s := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h s hw hh hs
    have hw' := WorldAdm_trunc (Nat.le_succ n) hw
    have hh' := HeapOk_trunc n W h hh
    let U := trunc n (Nat.le_succ n) W
    cases s with
    | «at» l ρ =>
      obtain ⟨c, hc, he, hf⟩ := hs
      obtain ⟨node, hn, ht, hk⟩ := graph_node hg hc
      have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
      exact Or.inr ⟨U, h, _, WExt_refl _, hw', .enter hn, hh',
        ih U h _ hw' hh' ⟨entry c, result c, c.output, he', ht n U h ρ he' hf hw' hh', hk⟩⟩
    | done v => exact Or.inl ⟨v, rfl, hs⟩
    | eval t ρ k =>
      obtain ⟨Γ, A, out, he, ht, hk⟩ := hs
      rcases ht with ⟨hv, ha, hf⟩ | ⟨V, h', t', hx, hu, step, hok, hsafe⟩
      · have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
        have ha' := (meaning_adm G A).down n W t ha
        cases k with
        | ret =>
          have heq : A = Rty := hk
          subst A
          exact Or.inr ⟨U, h, .done t, WExt_refl _, hw', .ret hv, hh',
            ih U h _ hw' hh' ⟨hv, ha'⟩⟩
        | bind l =>
          exact Or.inr ⟨U, h, .at l.label (mapEnv l.mapping (push t ρ)), WExt_refl _, hw', .bind hv, hh',
            ih U h _ hw' hh' (target_state hk (he'.push ha') hf)⟩
        | effect l =>
          exact Or.inr ⟨U, h, .at l.label (mapEnv l.mapping ρ), WExt_refl _, hw', .effect hv, hh',
            ih U h _ hw' hh' (target_state hk he' (HeapKnowledge.dropResult_holds hf))⟩
        | branch y no =>
          have hb := (represents_sem hk.1 (n+1) W t).mp ha
          rcases hb with rfl | rfl
          · exact Or.inr ⟨U, h, .at y.label (mapEnv y.mapping ρ), WExt_refl _, hw', .yes, hh',
              ih U h _ hw' hh' (target_state hk.2.1 he' (HeapKnowledge.dropResult_holds hf))⟩
          · exact Or.inr ⟨U, h, .at no.label (mapEnv no.mapping ρ), WExt_refl _, hw', .no, hh',
              ih U h _ hw' hh' (target_state hk.2.2 he' (HeapKnowledge.dropResult_holds hf))⟩
        | branchBind y no =>
          have hb := onlyBoolean_sound hk.1 ha
          rcases hb with rfl | rfl
          · exact Or.inr ⟨U, h, _, WExt_refl _, hw', .yesBind, hh',
              ih U h _ hw' hh' (branch_target_state hk.2.1 (he'.push ha') rfl hf)⟩
          · exact Or.inr ⟨U, h, _, WExt_refl _, hw', .noBind, hh',
              ih U h _ hw' hh' (branch_target_state hk.2.2 (he'.push ha') rfl hf)⟩
        | tagBind tag y no =>
          cases htag : tagHolds tag t with
          | true =>
            exact Or.inr ⟨U, h, _, WExt_refl _, hw', .tagBind hv, hh',
              ih U h _ hw' hh' (by
                simpa [htag] using (branch_target_state hk.1 (he'.push ha') htag hf))⟩
          | false =>
            exact Or.inr ⟨U, h, _, WExt_refl _, hw', .tagBind hv, hh',
              ih U h _ hw' hh' (by
                simpa [htag] using (branch_target_state hk.2 (he'.push ha') htag hf))⟩
      · exact Or.inr ⟨V, h', .eval t' ρ k, hx, hu, .expr step, hok,
          ih V h' _ hu hok ⟨Γ,A,out,he.transfer n (Nat.le_succ n) V hx,hsafe,hk⟩⟩

/-- Safety from any checked entry and concrete environment meeting its claim. -/
theorem accepted_entry_safe [DecidableEq ι] {G : NormalGraph ι} {Rty P C l c}
    (hg : checkGraph G Rty P C = true) (hc : C[l]? = some c)
    (n W h ρ) (he : EnvOk G (entry c) ρ n W) (hf : HeapKnowledge.Holds c.knowledge ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph P (meaning G Rty) n W h (.at l ρ) :=
  state_safe hg n W h _ hw hh ⟨c,hc,he,hf⟩

/-- The external input contract is independent of the supplied point claims. -/
def checkEntry [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι)) : Bool :=
  checkGraph G Rty P C && match C[start]? with
    | some c => decide (entry c = inputs ∧ c.knowledge = ⟨[],[],[]⟩)
    | none => false

theorem accepted_inputs_safe [DecidableEq ι] {G : NormalGraph ι} {Rty P C start inputs}
    (hc : checkEntry G Rty P C start inputs = true) (n W h ρ)
    (he : EnvOk G inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph P (meaning G Rty) n W h (.at start ρ) := by
  simp only [checkEntry, Bool.and_eq_true] at hc
  have hg := hc.1
  have hx := hc.2
  split at hx
  · rename_i c hc
    have hem : entry c = inputs ∧ c.knowledge = ⟨[],[],[]⟩ := of_decide_eq_true hx
    apply accepted_entry_safe hg hc n W h ρ _ _ hw hh
    · simpa only [hem.1] using he
    · rw [hem.2]; exact HeapKnowledge.empty ρ h
  · contradiction

/-- Closed entry is the empty-input instance of the same check. -/
def checkClosed [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (start : Nat) : Bool :=
  checkEntry G Rty P C start []

theorem accepted_closed_safe [DecidableEq ι] {G : NormalGraph ι} {Rty P C start}
    (hc : checkClosed G Rty P C start = true) (n : Nat) :
    SafeGraph P (meaning G Rty) n (ofList []) [] (.at start (fun _ => .nul)) := by
  exact accepted_inputs_safe hc n _ [] _ ⟨fun _ => trivial, by simp⟩ WorldAdm_nil (emptyHeapOk n)

theorem Transition.det {P h s h₁ s₁ h₂ s₂}
    (ha : Transition P h s h₁ s₁) (hb : Transition P h s h₂ s₂) : h₁ = h₂ ∧ s₁ = s₂ := by
  cases ha with
  | enter hn =>
    cases hb with
    | enter hn' =>
      have he := Option.some.inj (hn.symm.trans hn')
      cases he
      exact ⟨rfl,rfl⟩
  | expr hs =>
    cases hb with
    | expr ht => obtain ⟨rfl,rfl⟩ := Step_det hs ht; exact ⟨rfl,rfl⟩
    | ret hv => exact False.elim (value_no_step hv hs)
    | bind hv => exact False.elim (value_no_step hv hs)
    | effect hv => exact False.elim (value_no_step hv hs)
    | yes => exact False.elim (tru_no_step hs)
    | no => exact False.elim (fls_no_step hs)
    | yesBind => exact False.elim (tru_no_step hs)
    | noBind => exact False.elim (fls_no_step hs)
    | tagBind hv => exact False.elim (value_no_step hv hs)
  | ret hv =>
    cases hb with
    | expr hs => exact False.elim (value_no_step hv hs)
    | ret => exact ⟨rfl,rfl⟩
  | bind hv =>
    cases hb with
    | expr hs => exact False.elim (value_no_step hv hs)
    | bind => exact ⟨rfl,rfl⟩
  | effect hv =>
    cases hb with
    | expr hs => exact False.elim (value_no_step hv hs)
    | effect => exact ⟨rfl,rfl⟩
  | yes =>
    cases hb with
    | expr hs => exact False.elim (tru_no_step hs)
    | yes => exact ⟨rfl,rfl⟩
  | no =>
    cases hb with
    | expr hs => exact False.elim (fls_no_step hs)
    | no => exact ⟨rfl,rfl⟩
  | yesBind =>
    cases hb with
    | expr hs => exact False.elim (tru_no_step hs)
    | yesBind => exact ⟨rfl,rfl⟩
  | noBind =>
    cases hb with
    | expr hs => exact False.elim (fls_no_step hs)
    | noBind => exact ⟨rfl,rfl⟩
  | tagBind hv =>
    cases hb with
    | expr hs => exact False.elim (value_no_step hv hs)
    | tagBind => exact ⟨rfl,rfl⟩

/-- Safety follows the actual operational successor, not just a chosen run. -/
theorem SafeGraph.successor {P T n W h s h' s'}
    (hs : SafeGraph P T (n+1) W h s) (step : Transition P h s h' s') :
    ∃ U : WorldT n, WorldAdm U ∧ HeapOk n U h' ∧ SafeGraph P T n U h' s' := by
  rcases hs with ⟨v,rfl,_⟩ | ⟨U,h'',s'',hx,hu,st,hh,ht⟩
  · cases step
  · obtain ⟨rfl,rfl⟩ := Transition.det st step
    exact ⟨U,hu,hh,ht⟩

inductive Execution (P : Program) : Nat → Heap → State → Heap → State → Prop where
  | refl : Execution P 0 h s h s
  | next : Transition P h s h' s' → Execution P n h' s' h'' s'' → Execution P (n+1) h s h'' s''

/-- Every finite prefix retains safety at any requested remaining budget. -/
theorem execution_safe {P T k h s h' s'} (run : Execution P k h s h' s')
    (remaining : Nat) (W : WorldT ((remaining+1) + k))
    (hw : WorldAdm W) (hh : HeapOk ((remaining+1) + k) W h)
    (hs : SafeGraph P T ((remaining+1) + k) W h s) :
    ∃ U : WorldT (remaining+1), WorldAdm U ∧ HeapOk (remaining+1) U h' ∧
      SafeGraph P T (remaining+1) U h' s' := by
  induction run with
  | refl => exact ⟨W,hw,hh,hs⟩
  | next st run ih =>
    obtain ⟨U,hu,hh,hs⟩ := hs.successor st
    exact ih U hu hh hs

/-- At the end of any finite execution, the machine has returned a typed value
or has another operational step. In particular, invalid jumps and stuck
expressions cannot be reached by an accepted closed invocation. -/
theorem accepted_no_stuck [DecidableEq ι] {G : NormalGraph ι} {Rty P C start k h s}
    (hc : checkClosed G Rty P C start = true)
    (run : Execution P k [] (.at start (fun _ => .nul)) h s) :
    (∃ U : WorldT 1, ∃ v, s = .done v ∧ isVal v = true ∧ meaning G Rty 1 U v) ∨
    (∃ h' s', Transition P h s h' s') := by
  obtain ⟨U,hu,hh,hs⟩ := execution_safe run 0 (ofList []) WorldAdm_nil (emptyHeapOk (1+k))
    (accepted_closed_safe hc (1+k))
  rcases hs with ⟨v,hv,hval,ht⟩ | ⟨V,h',s',hx,hv,step,hh,hs⟩
  · exact Or.inl ⟨U,v,hv,hval,ht⟩
  · exact Or.inr ⟨h',s',step⟩

/-- Returned values satisfy the declared result at every positive remaining
budget, in an admissible world satisfied by the final heap. -/
theorem accepted_result [DecidableEq ι] {G : NormalGraph ι} {Rty P C start k h v}
    (hc : checkClosed G Rty P C start = true)
    (run : Execution P k [] (.at start (fun _ => .nul)) h (.done v)) (n : Nat) :
    ∃ U : WorldT (n+1), WorldAdm U ∧ HeapOk (n+1) U h ∧ isVal v = true ∧ meaning G Rty (n+1) U v := by
  obtain ⟨U,hu,hh,hs⟩ := execution_safe run n (ofList []) WorldAdm_nil (emptyHeapOk _)
    (accepted_closed_safe hc ((n+1)+k))
  rcases hs with ⟨w,he,hval,ht⟩ | ⟨V,h',s',hx,hv,step,hh,hs⟩
  · cases he; exact ⟨U,hu,hh,hval,ht⟩
  · cases step

#print axioms accepted_result
#print axioms accepted_no_stuck
#print axioms accepted_entry_safe
#print axioms accepted_inputs_safe
#print axioms accepted_closed_safe
end Verification.ExperimentState.ControlFlow
