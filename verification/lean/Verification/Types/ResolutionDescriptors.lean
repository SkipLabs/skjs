import Verification.Types.PositiveGraphs

/- Qualified generic parameters carry input, literal observation and stable
associated-result families. The operation relations and stable family are
fixed independently of recursive graph approximations. -/
namespace Verification.ResolutionDescriptors
open PositiveGraphs

/-- Fresh settlement and observation retain independent operation contracts.
Both are exact on stable inputs: an input within `N` is its own observation
and its own resolved result. -/
structure Capabilities (N : Fam) where
  resolve : Fam → Fam → Prop
  observe : Fam → Fam → Prop
  resolve_exact : ∀ {A R}, FamLe A N → resolve A R → R = A
  observe_exact : ∀ {A O}, FamLe A N → observe A O → O = A

/-- Stable inputs have their own type as both observation and resolved result.
Operation-output inclusions alone do not establish this type equality. -/
def StableExact (N A O R : Fam) : Prop :=
  FamLe A N → O = A ∧ R = A

structure Descriptor {N : Fam} (C : Capabilities N) where
  input : Fam
  observation : Fam
  result : Fam
  input_valid : ValueFam input
  observation_valid : ValueFam observation
  result_valid : ValueFam result
  stable : FamLe result N
  resolved : C.resolve input result
  observed : C.observe input observation
  forwarded : C.resolve observation result

/-- Stable exactness follows from the capabilities' exactness. -/
theorem Descriptor.exactStable {N : Fam} {C : Capabilities N} (d : Descriptor C) :
    StableExact N d.input d.observation d.result :=
  fun h => ⟨C.observe_exact h d.observed, C.resolve_exact h d.resolved⟩

theorem Descriptor.result_eq_input {N : Fam} {C : Capabilities N}
    (d : Descriptor C) (h : FamLe d.input N) : d.result = d.input :=
  (d.exactStable h).2

abbrev ProtectedSlots (s : SchemeRow ι) := s.protectedSlots

/-- One allowed tuple retains all three operation contracts. The value
projection permits ordinary argument-list binders alongside resolution groups. -/
def SlotCoherent {N : Fam} (C : Capabilities N) (As : List MixedFamily)
    (g : ResolutionSlots) : Prop :=
  ∃ T O R : MixedFamily,
    As[g.input]? = some T ∧ As[g.observation]? = some O ∧ As[g.result]? = some R ∧
    FamLe R.value.1 N ∧ C.resolve T.value.1 R.value.1 ∧
    C.observe T.value.1 O.value.1 ∧ C.resolve O.value.1 R.value.1

/-- The fixed descriptor universe is shared by all schemes in the graph.
Ordinary schemes retain their unrestricted substitutions. -/
def descriptorDomain {N : Fam} (C : Capabilities N) : SchemeDomain ι .mixed where
  allowed s As := ProtectedSlots s ∧ ∀ g ∈ s.resolution, SlotCoherent C As g
  ordinary_allowed := by
    intro s As hs
    simp [ProtectedSlots, SchemeRow.protectedSlots, hs]
  congr := by
    intro s t hm hp As
    exact and_congr hp (by rw [hm])

/-- Allowed-instance elimination exposes a genuine descriptor, including the
literal observation family rather than a result inferred from the input alone. -/
theorem allowed_descriptor {N : Fam} (C : Capabilities N) (s : SchemeRow ι)
    (As : List MixedFamily) (ha : (descriptorDomain C).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) :
    ∃ (d : Descriptor C) (T O R : MixedFamily),
      As[g.input]? = some T ∧ As[g.observation]? = some O ∧ As[g.result]? = some R ∧
      T.value.1 = d.input ∧ O.value.1 = d.observation ∧ R.value.1 = d.result := by
  obtain ⟨T, O, R, hT, hO, hR, hs, hr, ho, hf⟩ := ha.2 g hg
  exact ⟨⟨T.value.1, O.value.1, R.value.1, T.value.2, O.value.2, R.value.2,
    hs, hr, ho, hf⟩, T, O, R, hT, hO, hR, rfl, rfl, rfl⟩

variable {N : Fam} {C : Capabilities N}

/-- A bound tests only the input, below the current level. -/
def InputBounded (B : Fam) (d : Descriptor C) (n : Nat) : Prop :=
  ∀ j, j < n → ∀ W v, d.input j W v → B j W v

def quantified (B : Fam) (body : Descriptor C → Fam) : Fam :=
  fun n W f => Invocable f ∧ ∀ j (hj : j ≤ n) d, InputBounded B d j →
    body d j (trunc j hj W) f

abbrev Assignment {N : Fam} (C : Capabilities N) := Nat → Descriptor C

/-- Variable renaming carries all three projections of a descriptor. -/
def substitute (η : Assignment C) (σ : Nat → Nat) : Assignment C :=
  fun i => η (σ i)

/-- Actual mutable storage uses the same associated family on both reads
and writes; admissibility needs no covariance rule for writable references. -/
def storage (η : Assignment C) (i : Nat) : Fam := refT (η i).result

/-- Negative occurrences are ordinary arrow-domain occurrences of R. -/
def consumer (η : Assignment C) (i : Nat) : Fam :=
  callsT [(topF, [(η i).result], numT)]

#print axioms Descriptor.exactStable
#print axioms Descriptor.result_eq_input
#print axioms allowed_descriptor
end Verification.ResolutionDescriptors
