-- ResolutionDescriptors.lean defines descriptors relating a generic input to its observation and result; without it qualified graphs have no descriptor to interpret.
import Verification.Types.ResolutionDescriptors
import Verification.Types.PositiveCertificates

/- The recursive interpreter quantifies marked schemes over fixed operation
capabilities, retaining input, observation and result as ordinary families. -/
namespace Verification.QualifiedGraphs
open PositiveGraphs PositiveNormalization ResolutionDescriptors Tower
open PositiveCertificates (ComparisonResult)

variable {ι : Type} {C : Capabilities} {N : Fam}

/-- Three ordinary value slots retain the descriptor's associated result. -/
@[nospecialize] def descriptorArgs (d : Descriptor C N) : List MixedFamily :=
  [MixedFamily.ofValue ⟨d.input, d.input_valid⟩,
   MixedFamily.ofValue ⟨d.observation, d.observation_valid⟩,
   MixedFamily.ofValue ⟨d.result, d.result_valid⟩]

open Classical in
/-- The body assignment retains the descriptor at its declared binder nodes. -/
theorem assigned_descriptor (G : NormalGraph ι) (η : MixedAssignment ι)
    (s : SchemeRow ι) (As : List MixedFamily)
    (ha : (descriptorDomain C N).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) (t o r : ι)
    (ht : (s.binders.zip As).lookup t = As[g.input]?)
    (ho : (s.binders.zip As).lookup o = As[g.observation]?)
    (hr : (s.binders.zip As).lookup r = As[g.result]?)
    (kt : G.parameterKinds t = some .value)
    (ko : G.parameterKinds o = some .value)
    (kr : G.parameterKinds r = some .value) :
    ∃ d : Descriptor C N,
      PositiveRules.mixedValues G (assign η s.binders As) [t] = d.input ∧
      PositiveRules.mixedValues G (assign η s.binders As) [o] = d.observation ∧
      PositiveRules.mixedValues G (assign η s.binders As) [r] = d.result := by
  obtain ⟨d, T, O, R, hT, hO, hR, eT, eO, eR⟩ :=
    allowed_descriptor C N s As ha g hg
  have projection (p : ι) (A : MixedFamily)
      (hp : (s.binders.zip As).lookup p = some A)
      (hk : G.parameterKinds p = some .value) :
      PositiveRules.mixedValues G (assign η s.binders As) [p] = A.value.1 := by
    have he := mixedMeaning_parameter G (assign η s.binders As) p .value hk
    funext n W v
    have hv := congrFun (congrFun (congrFun he n) W) (Sum.inl v)
    simpa [mixedMeaning, mixedParameters, PositiveRules.mixedValues,
      selectParameter, assign, hp, MixedFamily.value] using hv
  exact ⟨d, (projection t T (ht.trans hT) kt).trans eT,
    (projection o O (ho.trans hO) ko).trans eO,
    (projection r R (hr.trans hR) kr).trans eR⟩

#print axioms assigned_descriptor

/-- The value binders of a resolution group, checked against the graph. -/
@[nospecialize] def groupBinders [DecidableEq ι] (G : NormalGraph ι)
    (s : SchemeRow ι) (g : ResolutionSlots) : Option (ι × ι × ι) := do
  let t ← s.binders[g.input]?
  let o ← s.binders[g.observation]?
  let r ← s.binders[g.result]?
  if G.parameterKinds t == some .value && G.parameterKinds o == some .value &&
      G.parameterKinds r == some .value then some (t, o, r) else none

/-- A lexical instance retains the three arguments of one enclosing group. -/
@[nospecialize] def groupInstance [DecidableEq ι] (G : NormalGraph ι)
    (source : SchemeRow ι) (g : ResolutionSlots) (args : List (List ι))
    (target : ResolutionSlots) : Bool :=
  match groupBinders G source g with
  | none => false
  | some (t, o, r) => args[target.input]? == some [t] &&
      args[target.observation]? == some [o] && args[target.result]? == some [r]

/-- Check a lexical instance against its enclosing scheme. Each target group
must retain one complete source group. Bounds are checked by the instance rule. -/
@[nospecialize] def lexicalAdmission [DecidableEq ι] (G : NormalGraph ι)
    (source target : SchemeRow ι) (args : List (List ι)) : Bool :=
  decide source.binders.Nodup && target.resolutionValid &&
    target.resolution.all fun h => source.resolution.any fun g => groupInstance G source g args h

theorem groupBinders_some [DecidableEq ι] {G : NormalGraph ι}
    {s : SchemeRow ι} {g : ResolutionSlots} {t o r : ι}
    (h : groupBinders G s g = some (t, o, r)) :
    s.binders[g.input]? = some t ∧ s.binders[g.observation]? = some o ∧
    s.binders[g.result]? = some r ∧ G.parameterKinds t = some .value ∧
    G.parameterKinds o = some .value ∧ G.parameterKinds r = some .value := by
  simp only [groupBinders, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t', ht, o', ho, r', hr, h⟩ := h
  split at h
  · rename_i hk
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    exact ⟨ht, ho, hr, hk.1.1, hk.1.2, hk.2⟩
  · cases h

open Classical in
theorem assignment_position {bs : List ι} {As : List MixedFamily}
    (hn : bs.Nodup) (hl : As.length = bs.length) {p : Nat} {b : ι}
    (hb : bs[p]? = some b) : (bs.zip As).lookup b = As[p]? := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hb
  have hj : p < As.length := by omega
  rw [← he, List.getElem?_eq_getElem hj]
  exact PositiveRules.lookup_zip_getElem hn p hi hj

/-- The checked lexical substitution is admissible at every assignment
permitted by its enclosing scheme. No independent choice of projections is made. -/
theorem lexicalAdmission_sound [DecidableEq ι] (G : NormalGraph ι)
    (source target : SchemeRow ι) (args : List (List ι))
    (checked : lexicalAdmission G source target args = true)
    (η : MixedAssignment ι) (As : List MixedFamily)
    (hl : As.length = source.binders.length)
    (ha : (descriptorDomain C N).allowed source As) :
    (descriptorDomain C N).allowed target
      (args.map fun U => ⟨mixedMeaning G (assign η source.binders As) U,
        mixedMeaning_valid G (assign η source.binders As) U⟩) := by
  simp only [lexicalAdmission, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true] at checked
  refine ⟨PositiveRules.resolutionValid_protected checked.1.2, ?_⟩
  intro h hh
  obtain ⟨g, hg, hm⟩ := checked.2 h hh
  unfold groupInstance at hm
  cases hb : groupBinders G source g with
  | none => simp [hb] at hm
  | some triple =>
    rcases triple with ⟨t, o, r⟩
    rw [hb] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨ht, ho, hr, kt, ko, kr⟩ := groupBinders_some hb
    obtain ⟨d, et, eo, er⟩ := assigned_descriptor G η source As ha g hg t o r
      (assignment_position checked.1.1 hl ht)
      (assignment_position checked.1.1 hl ho)
      (assignment_position checked.1.1 hl hr) kt ko kr
    let F (U : List ι) : MixedFamily :=
      ⟨mixedMeaning G (assign η source.binders As) U,
        mixedMeaning_valid G (assign η source.binders As) U⟩
    have et' : (F [t]).value.1 = d.input := et
    have eo' : (F [o]).value.1 = d.observation := eo
    have er' : (F [r]).value.1 = d.result := er
    refine ⟨F [t], F [o], F [r], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.getElem?_map, hm.1.1, Option.map_some]; rfl
    · simp only [List.getElem?_map, hm.1.2, Option.map_some]; rfl
    · simp only [List.getElem?_map, hm.2, Option.map_some]; rfl
    · rw [er']; exact d.stable
    · rw [et', er']; exact d.resolved
    · rw [et', eo']; exact d.observed
    · rw [eo', er']; exact d.forwarded
    · rw [et', eo', er']; exact d.exactStable

#print axioms lexicalAdmission_sound

/-- The shared instance checker with admission checked against the enclosing
lexical descriptor. Signature images, kinds and bounds use the ordinary checks. -/
@[nospecialize] def compareLexicalInstance [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (compare : List ι → List ι → σ → ComparisonResult α × σ) (empty : α)
    (S : List ι) (L : PositiveRules.Ops ι)
    (M : List (CallEffects.RestArrow (List ι)))
    (c : PositiveCertificates.Instance ι) (state : σ) : ComparisonResult (List α) × σ :=
  PositiveCertificates.compareInstArrsState G images compare empty S L M c state
    (fun target inst => ComparisonResult.fromBool
      (lexicalAdmission G source target inst.instances))

/-- Successful lexical instantiation is sound under the enclosing descriptor,
using the same computational instance rule as unconditional instantiation. -/
theorem compareLexicalInstance_sound [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (source : SchemeRow ι)
    (hd : G.domain = descriptorDomain C N)
    {compare : List ι → List ι → σ → ComparisonResult α × σ}
    {empty S L M c state} (η : MixedAssignment ι) (As : List MixedFamily)
    (hl : As.length = source.binders.length) (ha : G.domain.allowed source As)
    (hc : ∀ U V prior, (compare U V prior).1.accepted = true →
      FamLe (mixedMeaning G (assign η source.binders As) U)
        (mixedMeaning G (assign η source.binders As) V))
    (checked : (compareLexicalInstance G images source compare empty S L M c state).1.accepted = true) :
    FamLe (PositiveRules.mixedValues G (assign η source.binders As) S)
      (PositiveRules.mixedSem G (assign η source.binders As) (.arrs L M)) := by
  apply PositiveCertificates.compareInstArrsState_sound_at
    (assign η source.binders As) ?_ hc checked
  intro target inst h
  simp only [ComparisonResult.accepted_fromBool] at h
  rw [hd] at ha ⊢
  exact lexicalAdmission_sound G source target inst.instances h η As hl ha

#print axioms compareLexicalInstance_sound

/-- Metadata linking input, observation and result binders of an existing SchemeRow. Ordinary
   SchemeRow alone has no relation between independently quantified binders. -/
structure ResolvingRow (ι : Type) where
  input : ι
  observation : ι
  result : ι
  distinct : [input,observation,result].Nodup
  bound : List ι
  scheme : SchemeRow ι
  binders : scheme.binders = [input,observation,result]
  bounds : scheme.bounds = [(input,bound)]

@[nospecialize] noncomputable def graphBound (X : MixedAssignment ι × ι → Fam)
    (η : MixedAssignment ι) (r : ResolvingRow ι) : Fam :=
  setSem (fun i => X (η,i)) r.bound

@[nospecialize] noncomputable def graphBody (I : ParameterInterpretation ι .mixed)
    (X : MixedAssignment ι × ι → Fam) (η : MixedAssignment ι)
    (r : ResolvingRow ι) (d : Descriptor C N) : Fam :=
  instanceTWithArgs (fun θ S => setSem (fun i => X (θ,i)) S)
    η r.scheme (descriptorArgs d) I.arguments

@[nospecialize] noncomputable def graphScheme (I : ParameterInterpretation ι .mixed)
    (X : MixedAssignment ι × ι → Fam) (η : MixedAssignment ι)
    (r : ResolvingRow ι) : Fam :=
  quantified (graphBound X η r)
    (graphBody (C := C) (N := N) I X η r)

theorem graphScheme_layer_congr (I : ParameterInterpretation ι .mixed)
    (X Y : MixedAssignment ι × ι → Fam) (n : Nat)
    (h : ∀ z, Agree (X z) (Y z) n)
    (η : MixedAssignment ι) (r : ResolvingRow ι) (W : WorldT n) (v : Val) :
    graphScheme (C := C) (N := N) I X η r n W v ↔
      graphScheme (C := C) (N := N) I Y η r n W v := by
  unfold graphScheme quantified
  refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun d => imp_congr ?_ ?_)
  · unfold InputBounded
    refine forall_congr' fun j => forall_congr' fun hj =>
      forall_congr' fun U => forall_congr' fun u => imp_congr Iff.rfl ?_
    exact setSem_congr n (fun i => h (η,i)) r.bound j (by omega) U u
  · exact instanceT_congrWithArgs I.arguments I.arguments_nonexp
      (fun _ _ _ _ _ => Iff.rfl)
      (fun S => Agree.mono (setSem_congr n (fun i => h (_,i)) S) hq) (trunc q hq W) v

/-- A rigid intersection part uses the same qualification as its standalone
   row. Ordinary parameter and scheme parts retain production meaning. -/
@[nospecialize] noncomputable def part (G : NormalGraph ι) (I : ParameterInterpretation ι .mixed)
    (qualified : ι → Option (ResolvingRow ι))
    (X : MixedAssignment ι × ι → Fam) (η : MixedAssignment ι) (i : ι) : Fam :=
  if G.params i then I.value i (η.1 i) else
    match qualified i with
    | some r => graphScheme (C := C) (N := N) I X η r
    | none => partSemWithArgs G I X η i

theorem part_congr (G : NormalGraph ι) (I : ParameterInterpretation ι .mixed)
    (qualified : ι → Option (ResolvingRow ι))
    {X Y : MixedAssignment ι × ι → Fam} {n : Nat}
    (h : ∀ z, Agree (X z) (Y z) n) (η : MixedAssignment ι) (i : ι)
    (W : WorldT n) (v : Val) :
    part (C := C) (N := N) G I qualified X η i n W v ↔
      part (C := C) (N := N) G I qualified Y η i n W v := by
  unfold part
  split
  · exact Iff.rfl
  · cases hq : qualified i with
    | none => exact partSem_congrWithArgs G I h η i W v
    | some r => exact graphScheme_layer_congr I X Y n h η r W v

@[nospecialize] def usesPart (G : NormalGraph ι) (qualified : ι → Option (ResolvingRow ι)) (i : ι) : Bool :=
  G.params i || (G.schemes i).isSome || (qualified i).isSome || (G.meets i).isNone

/-- All rigid parts retain their qualified domain. Only the signatures and
   bounds of a qualified part read recursive approximations; capabilities are fixed. -/
@[nospecialize] noncomputable def layer (G : NormalGraph ι) (I : ParameterInterpretation ι .mixed)
    (qualified : ι → Option (ResolvingRow ι))
    (X : MixedAssignment ι × ι → Fam) : MixedAssignment ι × ι → Fam := fun z =>
  if usesPart G qualified z.2 then part (C := C) (N := N) G I qualified X z.1 z.2 else
    match G.meets z.2 with
    | none => part (C := C) (N := N) G I qualified X z.1 z.2
    | some (p,cs) => fun n W v =>
        (part (C := C) (N := N) G I qualified X z.1 p n W v ∧
          ∀ q ∈ G.meetParams z.2, part (C := C) (N := N) G I qualified X z.1 q n W v) ∧
        setSem (rowSem G (setSem fun l => X (I.realmAt,l))
          (setSem fun l => X (z.1,l)) (I.arguments z.1 (setSem fun l => X (z.1,l)))) cs n W v

theorem layer_congr (G : NormalGraph ι) (I : ParameterInterpretation ι .mixed)
    (qualified : ι → Option (ResolvingRow ι)) :
    LayerCongr (layer (C := C) (N := N) G I qualified) := by
  intro X Y n h z W v
  unfold layer
  split
  · exact part_congr G I qualified h z.1 z.2 W v
  · cases hm : G.meets z.2 with
    | none => exact part_congr G I qualified h z.1 z.2 W v
    | some pc =>
      refine and_congr (and_congr (part_congr G I qualified h z.1 pc.1 W v)
        (forall_congr' fun q => imp_congr_right fun _ => part_congr G I qualified h z.1 q W v)) ?_
      have hs := fun S => setSem_congr n (fun i => h (z.1,i)) S
      have hz := fun S => setSem_congr n (fun i => h (I.realmAt,i)) S
      constructor <;> rintro ⟨c,hc,hv⟩ <;> refine ⟨c,hc,?_⟩
      · exact (rowSem_congr G _ _ _ _ _ _ n hz hs
          (I.arguments_nonexp _ _ _ _ n (fun _ _ _ _ _ => Iff.rfl) hs) c W v).mp hv
      · exact (rowSem_congr G _ _ _ _ _ _ n hz hs
          (I.arguments_nonexp _ _ _ _ n (fun _ _ _ _ _ => Iff.rfl) hs) c W v).mpr hv

@[nospecialize] noncomputable def denote (G : NormalGraph ι) (I : ParameterInterpretation ι .mixed)
    (qualified : ι → Option (ResolvingRow ι)) : MixedAssignment ι × ι → Fam :=
  Tower.denote (layer (C := C) (N := N) G I qualified)

/-- Values and packs share the qualified recursive interpretation. -/
@[nospecialize] noncomputable def values (G : NormalGraph ι)
    (qualified : ι → Option (ResolvingRow ι)) (η : MixedAssignment ι) (S : List ι) : Fam :=
  setSem (fun i => denote (C := C) (N := N) G (mixedParameters G) qualified (η,i)) S

@[nospecialize] noncomputable def meaning (G : NormalGraph ι)
    (qualified : ι → Option (ResolvingRow ι)) (η : MixedAssignment ι) (S : List ι) :
    WorldFamily ParameterSpace.mixed.Carrier :=
  (mixedParameters G).bound η (values (C := C) (N := N) G qualified η) S

theorem denote_unfold (G : NormalGraph ι) (I : ParameterInterpretation ι .mixed)
    (qualified : ι → Option (ResolvingRow ι))
    (z : MixedAssignment ι × ι) (n : Nat) (W : WorldT n) (v : Val) :
    denote (C := C) (N := N) G I qualified z n W v ↔
      layer (C := C) (N := N) G I qualified
        (denote (C := C) (N := N) G I qualified) z n W v :=
  Tower.denote_unfold (layer_congr G I qualified) z n W v

theorem part_denote (G : NormalGraph ι) (I : ParameterInterpretation ι .mixed)
    (qualified : ι → Option (ResolvingRow ι)) (η : MixedAssignment ι) (i : ι)
    (hi : usesPart G qualified i = true) :
    part (C := C) (N := N) G I qualified (denote (C := C) (N := N) G I qualified) η i =
      denote (C := C) (N := N) G I qualified (η,i) := by
  funext n W v
  apply propext
  rw [denote_unfold]
  simp [layer, hi]

#print axioms graphScheme_layer_congr
#print axioms layer_congr
#print axioms denote_unfold
#print axioms part_congr
end Verification.QualifiedGraphs
