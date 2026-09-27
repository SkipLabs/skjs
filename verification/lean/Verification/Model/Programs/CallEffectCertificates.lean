import Verification.Model.Programs.GraphCode
import Verification.Model.Semantics.CallEffects

/-! Effect introduction is a definition check, not a call-site inspection.
The executable effect check supplements the existing body-safety certificate.
It cannot establish an arrow without that independent safety evidence. -/
namespace Verification.Model.CallEffectCertificates
open ProgramTyping PositiveGraphs PositiveRules CallEffects HeapObservations

/-- The initial body-effect algorithm is conservative. Rest-entry allocation
is covered separately. Allocations and qualified calls inside the body still
need composition rules; rejecting them does not restrict the semantic effect. -/
def check (effect : Effect) (expressions : List Tm) : Bool :=
  match effect with
  | .unrestricted => true
  | .preservesInputHeap => expressions.all Purity.pureTerm

/-- Definition evidence combines ordinary graph safety with the requested
signature's effect. Nothing is inferred from a producer's success flag.
A rest body is checked with its allocated store in the frame. -/
def Spec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (row : Arrow (Ty ι)) (store : Option (Ty ι) := none) : Prop :=
  GraphCodeSpec G arity E K start Cs row.plain store ∧ check row.effect E = true

/-- Check the ordinary graph certificate and the claimed effect together.
A rest store is retained in the checked frame; introduction also checks that
actuals meeting the rest contract allocate a store of that type. -/
def checkDefinition [DecidableEq ι] (G : NormalGraph ι) (table : List (CodeEntry ι))
    (c : CodeEntry ι) (C : ControlFlow.Certificate ι) (signature : Arrow (Ty ι)) : Bool :=
  decide (c.row = signature.plain) &&
    GraphCode.codeChecked G table c C && check signature.effect c.exprs

theorem checkDefinition_sound [DecidableEq ι] {G : NormalGraph ι} {table c C signature}
    (ht : ProgramCertificates.CodesSound G (GraphCode.admits table))
    (h : checkDefinition G table c C signature = true) :
    ∀ η, Spec (reassign G η) c.arity c.exprs c.conts c.start c.captures signature c.store := by
  simp only [checkDefinition, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, hc⟩, he⟩ := h
  intro η
  have hs := GraphCode.codeChecked_sound ht hc η
  refine ⟨?_, he⟩
  simpa [CodeEntry.Spec, hr] using hs

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

/-- A rest-collecting invocation preserves the input heap even though its
entry allocates fresh locations. The ordinary rest-store proof still checks
the allocated storage contract. -/
theorem invokeRest {G : NormalGraph ι} {arity E K start Cs A vs n W}
    {row : RestArrow (Ty ι)}
    (hs : Spec G arity E K start Cs
      ⟨row.receiver, row.arguments.1, row.result, row.effect⟩ (some A))
    (hk : row.arguments.1.length = arity) (harr : RestStore G A row.arguments.2)
    (hvs : EnvOk G Cs (envOf vs .nul) n W)
    (hvalues : CallArguments.Values vs) (hsc : ∀ v ∈ vs, Scoped 0 v)
    {j : Nat} (hj : j < n) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm}
    (hrv : isVal r = true) (hr : meaning G row.receiver j U r)
    {args : List Tm} (hav : CallArguments.Values args)
    (ha : ArgsRest (row.arguments.1.map (meaning G)) (argMeaning G row.arguments.2) j U args) :
    SafePost (meaning G row.result) (row.effect.post heap) j U heap
      (CallArguments.graphEntry arity E K start vs true r args) := by
  have safe := graphRest_invoke (s := row.plain) hs.1 hk harr hvs hsc hj hx hu hh hr hav ha
  cases he : row.effect with
  | unrestricted => simpa [he, Effect.post, RestArrow.plain] using forget safe
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
    have hframe := frame_envOk (arity := arity) (row := (row.receiver, row.arguments.1, row.result))
      (by simp [hk]) hvs (Nat.le_of_lt hj) hx hr (args := args.take arity)
      (by simpa [hk] using ha.1)
    rw [CallArguments.parameters_take] at hframe
    have hclosed : ∀ v ∈ r :: CallArguments.parameters arity args ++ vs, Scoped 0 v := by
      intro v hm
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
      have h := hframe.1 i
      unfold envOf at h
      rw [List.getD_eq_getElem?_getD, hi] at h
      exact h
    simpa only [he, RestArrow.plain, CallArguments.graphEntry, List.cons_append] using prefix_safe Purity.CollectingRun.step
      (.collect hp hv hclosed (fun v hm => hav v (List.mem_of_mem_drop hm))) safe

/-- Each variadic signature has its own body/effect evidence and rest-store
contract. Mapping its type operands preserves its effect. -/
theorem introduceRest {G : NormalGraph ι} {arity E K start Cs vs n W}
    {S : List (RestArrow (Ty ι))} {As : List (Ty ι)} (fs : List (PropKey × Nat))
    (hs : ∀ q ∈ S.zip As, q.1.arguments.1.length = arity ∧
      RestStore G q.2 q.1.arguments.2 ∧ Spec G arity E K start Cs
        ⟨q.1.receiver, q.1.arguments.1, q.1.result, q.1.effect⟩ (some q.2))
    (hlen : S.length = As.length) (hvs : EnvOk G Cs (envOf vs .nul) n W)
    (hvalues : CallArguments.Values vs) (hsc : ∀ v ∈ vs, Scoped 0 v) :
    CallEffects.restsT (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) n W
      (.objAt fs (.graph arity E K start vs .call true)) := by
  refine ⟨⟨fs, _, rfl, rfl, by simpa [Scoped] using hsc⟩, ?_⟩
  intro q hq j hj U hx hu heap hh r hrv hr args hvals ha
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsm
  have hiA : i < As.length := hlen ▸ hi
  have hz : (S[i], As[i]) ∈ S.zip As :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
      ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiA⟩)
  obtain ⟨hk, harr, hspec⟩ := hs _ hz
  exact ⟨_, .graph hrv hvals,
    invokeRest hspec hk harr hvs hvalues hsc hj hx hu hh hrv hr hvals ha⟩

#print axioms introduceRest
#print axioms checkDefinition_sound
#print axioms introduce
end Verification.Model.CallEffectCertificates
