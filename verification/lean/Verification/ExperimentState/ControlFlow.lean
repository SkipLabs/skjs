import Verification.ExperimentState.PointClaims

/-! A finite control-flow graph over the existing expression language. Expression
steps use the existing heap machine. Dispatch and transfers are explicit steps,
so cycles consume execution budget without requiring invariant inference. -/
namespace Verification.ExperimentState.ControlFlow
open ProgramTyping PositiveGraphs PositiveRules PointClaims ProgramCertificates

inductive Continuation where
  | ret
  | bind (next : Nat)
  | effect (next : Nat)
  | branch (yes no : Nat)
  deriving DecidableEq, Repr

structure Node where
  expression : Tm
  continuation : Continuation
  deriving DecidableEq, Repr

abbrev Program := List Node

structure NodeEvidence (ι : Type) where
  expression : Evidence ι
  edges : List (EdgeEvidence ι)

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
  | bind : isVal v = true → Transition P h (.eval v ρ (.bind l)) h (.at l (push v ρ))
  | effect : isVal v = true → Transition P h (.eval v ρ (.effect l)) h (.at l ρ)
  | yes : Transition P h (.eval .tru ρ (.branch y n)) h (.at y ρ)
  | no : Transition P h (.eval .fls ρ (.branch y n)) h (.at n ρ)

def SafeGraph (P : Program) (T : Fam) : (n : Nat) → WorldT n → Heap → State → Prop
  | 0, _, _, _ => True
  | n+1, W, h, s =>
    (∃ v, s = .done v ∧ isVal v = true ∧ T (n+1) W v) ∨
    ∃ U : WorldT n, ∃ h' s', WExt (trunc n (Nat.le_succ n) W) U ∧
      WorldAdm U ∧ Transition P h s h' s' ∧ HeapOk n U h' ∧ SafeGraph P T n U h' s'

/-- Target existence is checked against both the actual graph and its claims. -/
def checkTarget [DecidableEq ι] (G : NormalGraph ι) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (label : Nat) (p : EdgeEvidence ι) : Bool :=
  match P[label]?, C[label]? with
  | some _, some c => checkEdge G Γ (entry c) p
  | _, _ => false

def checkNode [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι) : Bool :=
  decide ((claim c.expression).term = node.expression) &&
  checkScope (entry c).length node.expression && checkTree G c.expression &&
  match node.continuation, c.edges with
  | .ret, [] => decide (result c = Rty)
  | .bind l, [p] => checkTarget G P C (result c :: entry c) l p
  | .effect l, [p] => checkTarget G P C (entry c) l p
  | .branch y n, [py,pn] => decide (expand G (result c) = [.bool]) &&
      checkTarget G P C (entry c) y py && checkTarget G P C (entry c) n pn
  | _, _ => false

/-- Enumeration comes from the program, not a certificate-supplied edge list. -/
def checkGraph [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) : Bool :=
  decide (P.length = C.length) && (List.range P.length).all (fun l =>
    match P[l]?, C[l]? with
    | some node, some c => checkNode G Rty P C node c
    | _, _ => false)

def TargetOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι) (Γ : List (Ty ι)) (l : Nat) : Prop :=
  ∃ c, C[l]? = some c ∧ Covers G Γ (entry c)

def ContinuationOk [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (A : Ty ι) : Continuation → Prop
  | .ret => A = Rty
  | .bind l => TargetOk G C (A :: Γ) l
  | .effect l => TargetOk G C Γ l
  | .branch y n => Represents G A .bool ∧ TargetOk G C Γ y ∧ TargetOk G C Γ n

theorem target_sound [DecidableEq ι] {G : NormalGraph ι} {P C Γ l p}
    (hc : checkTarget G P C Γ l p = true) : TargetOk G C Γ l := by
  unfold checkTarget at hc
  split at hc
  · rename_i node c hn he
    exact ⟨c, he, checkEdge_sound hc⟩
  · contradiction

theorem node_sound [DecidableEq ι] {G : NormalGraph ι} {Rty P C node c}
    (hc : checkNode G Rty P C node c = true) :
    HasTy G (entry c) node.expression (result c) ∧
    ContinuationOk G Rty C (entry c) (result c) node.continuation := by
  simp only [checkNode, Bool.and_eq_true, decide_eq_true_eq] at hc
  refine ⟨?_, ?_⟩
  · simpa only [entry, result, hc.1.1.1] using checkTree_sound c.expression hc.1.2
  · have hk := hc.2
    split at hk <;> (try (rename_i hcont hedges; rw [hcont]))
    · exact (of_decide_eq_true hk : result c = Rty)
    · exact target_sound hk
    · exact target_sound hk
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact ⟨hk.1.1, target_sound hk.1.2, target_sound hk.2⟩
    · contradiction

theorem graph_node [DecidableEq ι] {G : NormalGraph ι} {Rty P C c} {l : Nat}
    (hg : checkGraph G Rty P C = true) (hc : C[l]? = some c) :
    ∃ node : Node, P[l]? = some node ∧ HasTy G (entry c) node.expression (result c) ∧
      ContinuationOk G Rty C (entry c) (result c) node.continuation := by
  simp only [checkGraph, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hg
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
  | .at l ρ => ∃ c, C[l]? = some c ∧ EnvOk G (entry c) ρ n W
  | .eval t ρ k => ∃ Γ A, EnvOk G Γ ρ n W ∧ Safe (meaning G A) n W h t ∧ ContinuationOk G Rty C Γ A k
  | .done v => isVal v = true ∧ meaning G Rty n W v

theorem target_state [DecidableEq ι] {G : NormalGraph ι} {Rty C Γ l ρ n W h}
    (ht : TargetOk G C Γ l) (he : EnvOk G Γ ρ n W) : StateOk G Rty C n W h (.at l ρ) := by
  obtain ⟨c, hc, hcov⟩ := ht
  exact ⟨c, hc, hcov.env he⟩

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
      obtain ⟨c, hc, he⟩ := hs
      obtain ⟨node, hn, ht, hk⟩ := graph_node hg hc
      have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
      exact Or.inr ⟨U, h, _, WExt_refl _, hw', .enter hn, hh',
        ih U h _ hw' hh' ⟨entry c, result c, he', ht.sound n U h ρ he' hw' hh', hk⟩⟩
    | done v => exact Or.inl ⟨v, rfl, hs⟩
    | eval t ρ k =>
      obtain ⟨Γ, A, he, ht, hk⟩ := hs
      rcases ht with ⟨hv, ha⟩ | ⟨V, h', t', hx, hu, step, hok, hsafe⟩
      · have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
        have ha' := (meaning_adm G A).down n W t ha
        cases k with
        | ret =>
          have heq : A = Rty := hk
          subst A
          exact Or.inr ⟨U, h, .done t, WExt_refl _, hw', .ret hv, hh',
            ih U h _ hw' hh' ⟨hv, ha'⟩⟩
        | bind l =>
          exact Or.inr ⟨U, h, .at l (push t ρ), WExt_refl _, hw', .bind hv, hh',
            ih U h _ hw' hh' (target_state hk (he'.push ha'))⟩
        | effect l =>
          exact Or.inr ⟨U, h, .at l ρ, WExt_refl _, hw', .effect hv, hh',
            ih U h _ hw' hh' (target_state hk he')⟩
        | branch y no =>
          have hb := (represents_sem hk.1 (n+1) W t).mp ha
          rcases hb with rfl | rfl
          · exact Or.inr ⟨U, h, .at y ρ, WExt_refl _, hw', .yes, hh',
              ih U h _ hw' hh' (target_state hk.2.1 he')⟩
          · exact Or.inr ⟨U, h, .at no ρ, WExt_refl _, hw', .no, hh',
              ih U h _ hw' hh' (target_state hk.2.2 he')⟩
      · exact Or.inr ⟨V, h', .eval t' ρ k, hx, hu, .expr step, hok,
          ih V h' _ hu hok ⟨Γ,A,he.transfer n (Nat.le_succ n) V hx,hsafe,hk⟩⟩

/-- Safety from any checked entry and concrete environment meeting its claim. -/
theorem accepted_entry_safe [DecidableEq ι] {G : NormalGraph ι} {Rty P C l c}
    (hg : checkGraph G Rty P C = true) (hc : C[l]? = some c)
    (n W h ρ) (he : EnvOk G (entry c) ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph P (meaning G Rty) n W h (.at l ρ) :=
  state_safe hg n W h _ hw hh ⟨c,hc,he⟩

/-- A closed invocation must designate an existing entry with an empty context. -/
def checkClosed [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (start : Nat) : Bool :=
  checkGraph G Rty P C && match C[start]? with
    | some c => decide (entry c = [])
    | none => false

theorem accepted_closed_safe [DecidableEq ι] {G : NormalGraph ι} {Rty P C start}
    (hc : checkClosed G Rty P C start = true) (n : Nat) :
    SafeGraph P (meaning G Rty) n (ofList []) [] (.at start (fun _ => .nul)) := by
  simp only [checkClosed, Bool.and_eq_true] at hc
  have hx := hc.2
  split at hx
  · rename_i c he
    have hem : entry c = [] := of_decide_eq_true hx
    apply accepted_entry_safe hc.1 he n _ [] _ _ WorldAdm_nil (emptyHeapOk n)
    rw [hem]
    exact ⟨fun _ => trivial, by simp⟩
  · contradiction

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
#print axioms accepted_closed_safe
end Verification.ExperimentState.ControlFlow
