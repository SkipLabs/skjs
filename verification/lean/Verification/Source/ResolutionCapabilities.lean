import Verification.Types.ResolutionDescriptors

/-! Finite native-resolution classifications over a fixed, independently
interpreted native Promise constructor. These relations specify the instances
of external operation contracts; their constructors do not prove JavaScript
execution. Native callable membership remains a reviewed environment premise. -/
namespace Verification.ResolutionCapabilities
open PositiveGraphs ResolutionDescriptors

/-- Fresh resolution follows the literal payload of a native promise until
it reaches a stable family. Union arms share the declared target family. -/
inductive Resolves (P : Fam → Fam) (N : Fam) : Fam → Fam → Prop where
  | stable {A} : ValueFam A → FamLe A N → Resolves P N A A
  | native {A R} : Resolves P N A R → Resolves P N (P A) R
  | union {A B R S} : Resolves P N A R → Resolves P N B S →
      Resolves P N (unionT A B) (unionT R S)
  | narrow {A B R} : FamLe A B → Resolves P N B R → Resolves P N A R

/-- Observation reads a native promise's literal fulfillment family once. -/
inductive Observes (P : Fam → Fam) (N : Fam) : Fam → Fam → Prop where
  | stable {A} : ValueFam A → FamLe A N → Observes P N A A
  | native {A} : Observes P N (P A) A
  | union {A B O Q} : Observes P N A O → Observes P N B Q →
      Observes P N (unionT A B) (unionT O Q)
  | narrow {A B O} : FamLe A B → Observes P N B O → Observes P N A O

def capabilities (P : Fam → Fam) (N : Fam) : Capabilities where
  resolve := ⟨Resolves P N, Resolves.narrow⟩
  observe := ⟨Observes P N, Observes.narrow⟩

private theorem union_valid {A B : Fam} (ha : ValueFam A) (hb : ValueFam B) :
    ValueFam (unionT A B) :=
  ⟨unionT_adm A B ha.1 hb.1, fun n W v h => h.elim (ha.2 n W v) (hb.2 n W v)⟩

/-- A stable leaf uses one family for all three slots. -/
def stable (P : Fam → Fam) (N A : Fam) (ha : ValueFam A) (hn : FamLe A N) :
    Descriptor (capabilities P N) N where
  input := A
  observation := A
  result := A
  input_valid := ha
  observation_valid := ha
  result_valid := ha
  stable := hn
  resolved := .stable ha hn
  observed := .stable ha hn
  forwarded := .stable ha hn

/-- Native lifting preserves the child's associated result and observes its
input literally, including when that input is itself a native promise. -/
def native (P : Fam → Fam) (N : Fam)
    (hp : ∀ A, ValueFam A → ValueFam (P A))
    (d : Descriptor (capabilities P N) N) : Descriptor (capabilities P N) N where
  input := P d.input
  observation := d.input
  result := d.result
  input_valid := hp d.input d.input_valid
  observation_valid := d.input_valid
  result_valid := d.result_valid
  stable := d.stable
  resolved := .native d.resolved
  observed := .native
  forwarded := d.resolved

/-- Every union arm contributes its input, observation and result. -/
def union (P : Fam → Fam) (N : Fam)
    (d e : Descriptor (capabilities P N) N) : Descriptor (capabilities P N) N where
  input := unionT d.input e.input
  observation := unionT d.observation e.observation
  result := unionT d.result e.result
  input_valid := union_valid d.input_valid e.input_valid
  observation_valid := union_valid d.observation_valid e.observation_valid
  result_valid := union_valid d.result_valid e.result_valid
  stable := fun n W v h => h.elim (d.stable n W v) (e.stable n W v)
  resolved := .union d.resolved e.resolved
  observed := .union d.observed e.observed
  forwarded := .union d.forwarded e.forwarded

/-- Finite instance evidence constructs all slots together. A lexical binder
retains its whole descriptor, including its operation witnesses. -/
inductive Certificate (P : Fam → Fam) (N : Fam) where
  | stable (A : Fam) (valid : ValueFam A) (bounded : FamLe A N)
  | native (child : Certificate P N)
  | union (left right : Certificate P N)
  | binder (descriptor : Descriptor (capabilities P N) N)

def Certificate.denote {P : Fam → Fam} {N : Fam}
    (hp : ∀ A, ValueFam A → ValueFam (P A)) :
    Certificate P N → Descriptor (capabilities P N) N
  | .stable A hv hn => ResolutionCapabilities.stable P N A hv hn
  | .native child => ResolutionCapabilities.native P N hp (child.denote hp)
  | .union left right => ResolutionCapabilities.union P N (left.denote hp) (right.denote hp)
  | .binder d => d

#print axioms stable
#print axioms native
#print axioms union

/-- The modeled operation is safe at every admissible world and satisfying
heap. Unlike an outcome-only relation, this also constrains executions that
throw or do not return. -/
def OperationContract (op : Val → Tm) (A B : Fam) : Prop :=
  ∀ n (W : WorldT n) heap v, WorldAdm W → HeapOk n W heap →
    A n W v → Safe B n W heap (op v)

namespace OperationContract

theorem narrow {op A A' B} (h : OperationContract op A B)
    (ha : FamLe A' A) : OperationContract op A' B :=
  fun n W heap v hw hh hv => h n W heap v hw hh (ha n W v hv)

theorem widen {op A B B'} (h : OperationContract op A B)
    (hb : FamLe B B') : OperationContract op A B' := by
  intro n W heap v hw hh hv
  exact Safe_mono n (fun m _ U u hu => hb m U u hu) W heap (op v)
    (h n W heap v hw hh hv)

theorem union {op A B R S} (ha : OperationContract op A R)
    (hb : OperationContract op B S) :
    OperationContract op (unionT A B) (unionT R S) := by
  intro n W heap v hw hh hv
  rcases hv with hv | hv
  · exact ha.widen (fun _ _ _ h => Or.inl h) n W heap v hw hh hv
  · exact hb.widen (fun _ _ _ h => Or.inr h) n W heap v hw hh hv

theorem union_input {op A B R} :
    OperationContract op (unionT A B) R ↔
      OperationContract op A R ∧ OperationContract op B R := by
  constructor
  · intro h
    exact ⟨h.narrow (fun _ _ _ h => Or.inl h), h.narrow (fun _ _ _ h => Or.inr h)⟩
  · rintro ⟨ha, hb⟩ n W heap v hw hh (hv | hv)
    · exact ha n W heap v hw hh hv
    · exact hb n W heap v hw hh hv
end OperationContract

/-- Reviewed host contracts expressed in the verifier's own world and safety
model. `fresh` returns a native promise, while `observe` returns its delivered
value. Fresh resolution is not the native-identity operation Promise.resolve.
These are explicit premises, not consequences of structural Promise methods. -/
structure NativeOperationContracts (P : Fam → Fam) (N : Fam)
    (observe fresh : Val → Tm) : Prop where
  promise_mono : ∀ {A B}, FamLe A B → FamLe (P A) (P B)
  observe_stable : ∀ {A}, ValueFam A → FamLe A N → OperationContract observe A A
  fresh_stable : ∀ {A}, ValueFam A → FamLe A N → OperationContract fresh A (P A)
  observe_native : ∀ A, OperationContract observe (P A) A
  fresh_native : ∀ {A R}, OperationContract fresh A (P R) →
    OperationContract fresh (P A) (P R)

/-- Every finite observation derivation supplies the actual safety contract. -/
theorem Observes.safe {P N observe fresh}
    (host : NativeOperationContracts P N observe fresh)
    {A O} (h : Observes P N A O) : OperationContract observe A O := by
  induction h with
  | stable hv hn => exact host.observe_stable hv hn
  | native => exact host.observe_native _
  | union _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | narrow hb _ ih => exact ih.narrow hb

/-- Resolution derivations produce the declared native result; safety includes
world evolution and every intermediate computation admitted by Safe. -/
theorem Resolves.safe {P N observe fresh}
    (host : NativeOperationContracts P N observe fresh)
    {A R} (h : Resolves P N A R) : OperationContract fresh A (P R) := by
  induction h with
  | stable hv hn => exact host.fresh_stable hv hn
  | native _ ih => exact host.fresh_native ih
  | union _ _ ih₁ ih₂ =>
      apply (OperationContract.union_input).mpr
      exact ⟨ih₁.widen (host.promise_mono (fun _ _ _ h => Or.inl h)),
        ih₂.widen (host.promise_mono (fun _ _ _ h => Or.inr h))⟩
  | narrow hb _ ih => exact ih.narrow hb

#print axioms OperationContract.union_input
#print axioms Observes.safe
#print axioms Resolves.safe

end Verification.ResolutionCapabilities
