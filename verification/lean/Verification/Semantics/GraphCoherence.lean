import Verification.Programs.ControlFlow

/-! Identity coherence for the existing certificate consumer and graph machine.
The consumer checks that executable syntax cannot embed runtime identities.
External inputs must already be coherent with their supplied heap; closed
invocations establish the invariant from the empty registry automatically. -/
namespace Verification.GraphCoherence
open ObjectCoherence ControlFlow PointClaims

abbrev EnvCoherent (D : Registry) (ρ : Env) := ∀ i, TermOk D (ρ i)

def StateCoherent (D : Registry) : State → Prop
  | .at _ ρ => EnvCoherent D ρ
  | .eval t ρ _ _ => TermOk D t ∧ EnvCoherent D ρ
  | .done v => TermOk D v
  | .raised v => TermOk D v

theorem env_mono {D E ρ} (h : EnvCoherent D ρ) (hx : Extends D E) : EnvCoherent E ρ :=
  fun i => (h i).mono hx

theorem env_push {D ρ v} (h : EnvCoherent D ρ) (hv : TermOk D v) :
    EnvCoherent D (push v ρ) := by
  intro i; cases i with
  | zero => exact hv
  | succ i => exact h i

theorem env_map {D ρ} (h : EnvCoherent D ρ) (m : Mapping) : EnvCoherent D (mapEnv m ρ) :=
  fun i => h (slot m i)

def SourceGraph (P : Program) : Prop := ∀ node ∈ P, sourceTerm node.expression = true

theorem checked_source [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {R P C}
    (hc : checkGraphUsing G images R P C = true) : SourceGraph P := by
  simp only [checkGraphUsing_eq, Bool.and_eq_true] at hc
  exact List.all_eq_true.mp hc.2

/-- Graph transfers only copy coherent values; expression steps use the core
preservation theorem, extending the same registry used by the saved environment. -/
theorem transition_preserves {P h s h' s'} (hp : SourceGraph P)
    (step : Transition P h s h' s') {D} (hh : ObjectCoherence.HeapOk D h)
    (hs : StateCoherent D s) :
    ∃ E, Extends D E ∧ ObjectCoherence.HeapOk E h' ∧ StateCoherent E s' := by
  cases step with
  | enter hn =>
    refine ⟨D,.refl D,hh,?_,hs⟩
    exact ⟨instantiate_scoped _ (fun i => (hs i).1) _ 0,
      (source_names (hp _ (List.mem_of_getElem? hn)) D).instantiate _ (fun i => (hs i).2) 0⟩
  | expr step =>
    obtain ⟨E,hx,hh',ht⟩ := step_preserves step D hh hs.1
    exact ⟨E,hx,hh',ht,env_mono hs.2 hx⟩
  | ret hv => exact ⟨D,.refl D,hh,hs.1⟩
  | bind hv => exact ⟨D,.refl D,hh,env_map (env_push hs.2 hs.1) _⟩
  | effect hv => exact ⟨D,.refl D,hh,env_map hs.2 _⟩
  | yes => exact ⟨D,.refl D,hh,env_map hs.2 _⟩
  | no => exact ⟨D,.refl D,hh,env_map hs.2 _⟩
  | yesBind => exact ⟨D,.refl D,hh,env_map (env_push hs.2 hs.1) _⟩
  | noBind => exact ⟨D,.refl D,hh,env_map (env_push hs.2 hs.1) _⟩
  | tagBind hv => exact ⟨D,.refl D,hh,env_map (env_push hs.2 hs.1) _⟩
  | handle hr => exact ⟨D,.refl D,hh,env_map (env_push hs.2 (raises_termOk hr hs.1)) _⟩
  | raise hr => exact ⟨D,.refl D,hh,raises_termOk hr hs.1⟩

theorem execution_preserves {P k h s h' s'} (hp : SourceGraph P)
    (run : Execution P k h s h' s') {D} (hh : ObjectCoherence.HeapOk D h)
    (hs : StateCoherent D s) :
    ∃ E, Extends D E ∧ ObjectCoherence.HeapOk E h' ∧ StateCoherent E s' := by
  induction run generalizing D with
  | refl => exact ⟨D,.refl D,hh,hs⟩
  | next step run ih =>
    obtain ⟨E,hx,hh',hs'⟩ := transition_preserves hp step hh hs
    obtain ⟨F,hy,hh'',hs''⟩ := ih hh' hs'
    exact ⟨F,hx.trans hy,hh'',hs''⟩

/-- Every finite run of an accepted invocation preserves input descriptors and
keeps all newly allocated identities coherent throughout the graph state. -/
theorem accepted_inputs_coherent [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {R P C start inputs k h ρ h' s' D}
    (hc : checkEntryUsing G images R P C start inputs = true)
    (hh : ObjectCoherence.HeapOk D h) (he : EnvCoherent D ρ)
    (run : Execution P k h (.at start ρ) h' s') :
    ∃ E, Extends D E ∧ ObjectCoherence.HeapOk E h' ∧ StateCoherent E s' := by
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hc
  exact execution_preserves (checked_source hc.1) run hh he

/-- No coherence assumption is needed for a closed invocation: the empty heap
and initial null environment establish it. -/
theorem accepted_closed_coherent [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G}
    {R P C start k h s}
    (hc : checkClosedUsing G images R P C start = true)
    (run : Execution P k [] (.at start (fun _ => .nul)) h s) :
    ∃ D, ObjectCoherence.HeapOk D h ∧ StateCoherent D s := by
  obtain ⟨D,_,hh,hs⟩ := accepted_inputs_coherent hc
    (D := []) (ρ := fun _ => .nul) (h := []) (by simp [ObjectCoherence.HeapOk]) (fun _ => ⟨trivial,trivial⟩) run
  exact ⟨D,hh,hs⟩

#print axioms checked_source
#print axioms transition_preserves
#print axioms execution_preserves
#print axioms accepted_inputs_coherent
#print axioms accepted_closed_coherent
end Verification.GraphCoherence
