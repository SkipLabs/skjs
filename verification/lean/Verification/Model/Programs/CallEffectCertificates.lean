import Verification.Model.Programs.GraphCode
import Verification.Model.Semantics.CallEffects

/-! Effect introduction is a definition check, not a call-site inspection.
The executable effect check supplements the existing body-safety certificate.
It cannot establish an arrow without that independent safety evidence. -/
namespace Verification.Model.CallEffectCertificates
open ProgramTyping PositiveGraphs PositiveRules CallEffects HeapObservations

/-- The initial effect algorithm is conservative. Allocation and calls with
qualified contracts can be added with their own composition proofs; rejecting
those here does not restrict the semantic meaning of the effect. -/
def check (effect : Effect) (expressions : List Tm) : Bool :=
  match effect with
  | .unrestricted => true
  | .preservesInputHeap => expressions.all Purity.pureTerm

/-- Definition evidence combines ordinary graph safety with the requested
signature's effect. Nothing is inferred from a producer's success flag. -/
def Spec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (row : Arrow (Ty ι)) : Prop :=
  GraphCodeSpec G arity E K start Cs row.plain ∧ check row.effect E = true

/-- Check the ordinary graph certificate and the claimed effect together.
Rest-collecting entries need a proof covering argument allocation before they
can use this fixed-entry checker. The refusal is explicit, not field erasure. -/
def checkDefinition [DecidableEq ι] (G : NormalGraph ι) (table : List (CodeEntry ι))
    (c : CodeEntry ι) (C : ControlFlow.Certificate ι) (signature : Arrow (Ty ι)) : Bool :=
  decide (c.row = signature.plain) && c.store.isNone &&
    GraphCode.codeChecked G table c C && check signature.effect c.exprs

theorem checkDefinition_sound [DecidableEq ι] {G : NormalGraph ι} {table c C signature}
    (ht : ProgramCertificates.CodesSound G (GraphCode.admits table))
    (h : checkDefinition G table c C signature = true) :
    ∀ η, Spec (reassign G η) c.arity c.exprs c.conts c.start c.captures signature := by
  simp only [checkDefinition, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, hstore⟩, hc⟩, he⟩ := h
  have hn : c.store = none := Option.isNone_iff_eq_none.mp hstore
  intro η
  have hs := GraphCode.codeChecked_sound ht hc η
  refine ⟨?_, he⟩
  simpa [CodeEntry.Spec, hn, hr] using hs

/-- The checked graph's invocation has its proposed return type and effect.
The values premise includes captures, so the operational argument cannot
mistake arbitrary substituted terms for already evaluated values. -/
theorem invoke {G : NormalGraph ι} {arity E K start Cs row vs n W}
    (hs : Spec G arity E K start Cs row)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hvalues : CallArguments.Values vs)
    {j : Nat} (hj : j < n) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm}
    (hrv : isVal r = true) (hr : meaning G row.receiver j U r)
    {args : List Tm} (hav : CallArguments.Values args)
    (ha : ArgsShort (row.arguments.map (meaning G)) j U args) :
    SafePost (meaning G row.result) (row.effect.post heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul) := by
  have safe := graph_invoke hs.1 hvs hj hx hu hh hr ha
  cases he : row.effect with
  | unrestricted => simpa [he, Effect.post, Arrow.plain] using forget safe
  | preservesInputHeap =>
    have hp : ∀ e ∈ E, Purity.pureTerm e = true := by
      simpa [check, he, List.all_eq_true] using hs.2
    have hv : CallArguments.Values (r :: CallArguments.parameters arity args ++ vs) := by
      intro v hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hrv
      · rcases List.mem_append.mp hm with hm | hm
        · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl hav v hm
        · exact hvalues v hm
    simpa [he, Arrow.plain] using pure_safe (.goto hp hv rfl) safe

/-- Creation establishes the qualified type once. Later application uses
`CallEffects.call_safe`, which has no premise about this graph's syntax. -/
theorem introduce {G : NormalGraph ι} {arity E K start Cs vs n W}
    {L : List (Arrow (Ty ι))} (fs : List (PropKey × Nat))
    (hs : ∀ row ∈ L, Spec G arity E K start Cs row)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hvalues : CallArguments.Values vs)
    (hsc : ∀ v ∈ vs, Scoped 0 v) :
    CallEffects.callsT (L.map (Arrow.map (meaning G))) n W
      (.objAt fs (.graph arity E K start vs)) := by
  refine ⟨⟨fs, _, rfl, rfl, by simpa [Scoped] using hsc⟩, ?_⟩
  intro q hq j hj U hx hu heap hh r hrv hr args hvals ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact ⟨_, .graph hrv hvals,
    invoke (hs p hp) hvs hvalues hj hx hu hh hrv hr hvals ha⟩

#print axioms checkDefinition_sound
#print axioms introduce
end Verification.Model.CallEffectCertificates
