import Verification.Types.PositiveGraphs

/- Qualified generic parameters carry input, literal observation and stable
associated-result families. The operation relations and stable family are
fixed independently of recursive graph approximations. -/
namespace Verification.ResolutionDescriptors
open PositiveGraphs

structure Qualification where
  holds : Fam → Fam → Prop
  narrow : ∀ {S S' R}, FamLe S' S → holds S R → holds S' R

/-- Fresh settlement and observation retain independent operation contracts. -/
structure Capabilities where
  resolve : Qualification
  observe : Qualification

structure Descriptor (C : Capabilities) (N : Fam) where
  input : Fam
  observation : Fam
  result : Fam
  input_valid : ValueFam input
  observation_valid : ValueFam observation
  result_valid : ValueFam result
  stable : FamLe result N
  resolved : C.resolve.holds input result
  observed : C.observe.holds input observation
  forwarded : C.resolve.holds observation result

abbrev ProtectedSlots (s : SchemeRow ι) := s.protectedSlots

/-- One allowed tuple retains all three operation contracts. The value
projection permits ordinary argument-list binders alongside resolution groups. -/
def SlotCoherent (C : Capabilities) (N : Fam) (As : List MixedFamily)
    (g : ResolutionSlots) : Prop :=
  ∃ T O R : MixedFamily,
    As[g.input]? = some T ∧ As[g.observation]? = some O ∧ As[g.result]? = some R ∧
    FamLe R.value.1 N ∧ C.resolve.holds T.value.1 R.value.1 ∧
    C.observe.holds T.value.1 O.value.1 ∧ C.resolve.holds O.value.1 R.value.1

/-- Restricting declared bounds narrows each input while retaining its paired
observation and result. This is the production domain's formation law. -/
theorem slotCoherent_restrict (C : Capabilities) (N : Fam)
    (D : MixedAssignment ι → List ι → WorldFamily ParameterSpace.mixed.Carrier)
    (η : MixedAssignment ι) (s : SchemeRow ι) (hD : ∀ S, Adm (D η S))
    (As : List MixedFamily) (hl : As.length = s.binders.length)
    (hp : ProtectedSlots s) (g : ResolutionSlots) (hg : g ∈ s.resolution)
    (hc : SlotCoherent C N As g) :
    SlotCoherent C N (restrictArgs D η s.bounds hD s.binders As) g := by
  obtain ⟨T, O, R, hT, hO, hR, hs, hr, ho, hf⟩ := hc
  obtain ⟨bT, hbT, hT'⟩ := restrictArgs_lookup D η s.bounds hD s.binders As g.input T hl hT
  obtain ⟨bO, hbO, hO'⟩ := restrictArgs_lookup D η s.bounds hD s.binders As g.observation O hl hO
  obtain ⟨bR, hbR, hR'⟩ := restrictArgs_lookup D η s.bounds hD s.binders As g.result R hl hR
  have heO := restrictArg_eq_of_noBounds D η s.bounds hD bO O
    (hp g hg g.observation (by simp) bO hbO)
  have heR := restrictArg_eq_of_noBounds D η s.bounds hD bR R
    (hp g hg g.result (by simp) bR hbR)
  rw [heO] at hO'
  rw [heR] at hR'
  refine ⟨restrictArg D η s.bounds hD bT T, O, R, hT', hO', hR', hs, ?_, ?_, hf⟩
  · exact C.resolve.narrow (fun n W v h => h.1) hr
  · exact C.observe.narrow (fun n W v h => h.1) ho

/-- The fixed descriptor universe is shared by all schemes in the graph.
Ordinary schemes retain their unrestricted substitutions. -/
def descriptorDomain (C : Capabilities) (N : Fam) : SchemeDomain ι .mixed :=
  .ofRestrict (fun s As => ProtectedSlots s ∧ ∀ g ∈ s.resolution, SlotCoherent C N As g)
  (by
    intro s As hs
    simp [ProtectedSlots, SchemeRow.protectedSlots, hs])
  (by
    intro s t hm hp As
    exact and_congr hp (by rw [hm]))
  (by
    intro D η s hD As hl h
    exact ⟨h.1, fun g hg => slotCoherent_restrict C N D η s hD As hl h.1 g hg (h.2 g hg)⟩)

/-- Allowed-instance elimination exposes a genuine descriptor, including the
literal observation family rather than a result inferred from the input alone. -/
theorem allowed_descriptor (C : Capabilities) (N : Fam) (s : SchemeRow ι)
    (As : List MixedFamily) (ha : (descriptorDomain C N).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) :
    ∃ (d : Descriptor C N) (T O R : MixedFamily),
      As[g.input]? = some T ∧ As[g.observation]? = some O ∧ As[g.result]? = some R ∧
      T.value.1 = d.input ∧ O.value.1 = d.observation ∧ R.value.1 = d.result := by
  obtain ⟨T, O, R, hT, hO, hR, hs, hr, ho, hf⟩ := ha.2 g hg
  exact ⟨⟨T.value.1, O.value.1, R.value.1, T.value.2, O.value.2, R.value.2,
    hs, hr, ho, hf⟩, T, O, R, hT, hO, hR, rfl, rfl, rfl⟩

variable {C : Capabilities} {N : Fam}

def Descriptor.restrict (d : Descriptor C N) (B : Fam) (hb : Adm B) :
    Descriptor C N where
  input := interT d.input B
  observation := d.observation
  result := d.result
  input_valid := ⟨interT_adm _ _ d.input_valid.1 hb,
    fun n W v h => d.input_valid.2 n W v h.1⟩
  observation_valid := d.observation_valid
  result_valid := d.result_valid
  stable := d.stable
  resolved := C.resolve.narrow (fun _ _ _ h => h.1) d.resolved
  observed := C.observe.narrow (fun _ _ _ h => h.1) d.observed
  forwarded := d.forwarded

/-- A bound tests only the input, below the current level. The associated
result is retained when restricting an instance to establish admissibility. -/
def InputBounded (B : Fam) (d : Descriptor C N) (n : Nat) : Prop :=
  ∀ j, j < n → ∀ W v, d.input j W v → B j W v

def quantified (B : Fam) (body : Descriptor C N → Fam) : Fam :=
  fun n W f => Invocable f ∧ ∀ d, InputBounded B d n → body d n W f

abbrev Assignment (C : Capabilities) (N : Fam) := Nat → Descriptor C N

/-- Variable renaming carries all three projections of a descriptor. -/
def substitute (η : Assignment C N) (σ : Nat → Nat) : Assignment C N :=
  fun i => η (σ i)

/-- Actual mutable storage uses the same associated family on both reads
and writes; admissibility needs no covariance rule for writable references. -/
def storage (η : Assignment C N) (i : Nat) : Fam := refT (η i).result

/-- Negative occurrences are ordinary arrow-domain occurrences of R. -/
def consumer (η : Assignment C N) (i : Nat) : Fam :=
  callsT [(topF, [(η i).result], numT)]

#print axioms slotCoherent_restrict
#print axioms allowed_descriptor
end Verification.ResolutionDescriptors
