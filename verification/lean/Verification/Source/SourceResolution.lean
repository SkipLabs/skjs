import Verification.Source.EquationStore
import Verification.Source.ResolutionWire

/-! Source resolution certificates retain the input, literal observation and
stable result. Every accepted certificate supplies all three semantic equalities
under the descriptors of its enclosing generic scope. -/
namespace Verification.SourceResolution
open EquationStore EquationGraphs PositiveGraphs PositiveRules PositiveCertificates

abbrev Ty (E : Equations) := List (Label E.signature)

/-- The value interpretation of one source type. -/
def valueMeaning (E : Equations) (η : MixedAssignment (Label E.signature)) (A : Ty E) : Fam :=
  fun n W v => mixedMeaning E.graph η A n W (.inl v)

abbrev Descriptor (c : ResolutionContext E) :=
  ResolutionDescriptors.Descriptor c.capabilities

/-- All three source types denote the corresponding components of one descriptor. -/
def Describes (c : ResolutionContext E) (η : MixedAssignment (Label E.signature))
    (A O R : Ty E) : Prop :=
  ∃ d : Descriptor c, d.input = valueMeaning E η A ∧
    d.observation = valueMeaning E η O ∧ d.result = valueMeaning E η R

structure Binding (E : Equations) where
  name : String
  input : Ty E
  observation : Ty E
  result : Ty E
  deriving DecidableEq

/-- The scope's semantic premise is discharged by the enclosing scheme's
allowed descriptor assignment. -/
def ScopeHolds (c : ResolutionContext E) (scope : List (Binding E))
    (η : MixedAssignment (Label E.signature)) : Prop :=
  ∀ b ∈ scope, Describes c η b.input b.observation b.result

/-- A source binder is tied to an actual resolution group of its enclosing
scheme. Its interpretation follows from that scheme's allowed assignment. -/
structure LexicalBinding (c : ResolutionContext E) (source : SchemeRow (Label E.signature)) where
  binding : Binding E
  sound : ∀ η As, As.length = source.binders.length → c.domain.allowed source As →
    Describes c (assign η source.binders As) binding.input binding.observation binding.result

def lexicalBinding (c : ResolutionContext E) (source : SchemeRow (Label E.signature))
    (name : String) (group : PositiveGraphs.ResolutionSlots) : Option (LexicalBinding c source) :=
  let _ : BEq PositiveGraphs.ResolutionSlots := instBEqOfDecidableEq
  if unique : source.binders.Nodup then
    if member : group ∈ source.resolution then
      match checked : QualifiedGraphs.groupBinders E.graph source group with
      | none => none
      | some (t, o, r) => some {
          binding := ⟨name, [t], [o], [r]⟩
          sound := fun η As length allowed => by
            obtain ⟨ht, ho, hr, kt, ko, kr⟩ := QualifiedGraphs.groupBinders_some checked
            obtain ⟨d, et, eo, er⟩ := QualifiedGraphs.assigned_descriptor E.graph η source As
              allowed group member t o r
              (QualifiedGraphs.assignment_position unique length ht)
              (QualifiedGraphs.assignment_position unique length ho)
              (QualifiedGraphs.assignment_position unique length hr) kt ko kr
            exact ⟨d, et.symm, eo.symm, er.symm⟩ }
    else none
  else none

structure Checked (c : ResolutionContext E) (scope : List (Binding E)) (A : Ty E) where
  observation : Ty E
  result : Ty E
  sound : ∀ η, ScopeHolds c scope η → Describes c η A observation result

private theorem valueMeaning_append (E : Equations) (η : MixedAssignment (Label E.signature))
    (A B : Ty E) : valueMeaning E η (A ++ B) = unionT (valueMeaning E η A) (valueMeaning E η B) := by
  funext n W v
  apply propext
  change (∃ l ∈ A ++ B, _) ↔ ((∃ l ∈ A, _) ∨ (∃ l ∈ B, _))
  simp only [List.mem_append, or_and_right, exists_or]

private theorem describes_append (c : ResolutionContext E)
    (η : MixedAssignment (Label E.signature)) {A O R B Q S : Ty E}
    (left : Describes c η A O R) (right : Describes c η B Q S) :
    Describes c η (A ++ B) (O ++ Q) (R ++ S) := by
  obtain ⟨d, hd, ho, hr⟩ := left
  obtain ⟨e, he, hq, hs⟩ := right
  refine ⟨ResolutionCapabilities.union c.native d e, ?_, ?_, ?_⟩
  · change unionT d.input e.input = _
    rw [hd, he, valueMeaning_append]
  · change unionT d.observation e.observation = _
    rw [ho, hq, valueMeaning_append]
  · change unionT d.result e.result = _
    rw [hr, hs, valueMeaning_append]

private def empty (c : ResolutionContext E) (scope : List (Binding E)) : Checked c scope [] where
  observation := []
  result := []
  sound η _ := by
    have hv : ValueFam (valueMeaning E η []) :=
      (MixedFamily.value ⟨_, mixedMeaning_valid _ _ _⟩).2
    have hn : FamLe (valueMeaning E η []) c.stableFamily := by
      intro n W v h
      change ∃ l ∈ ([] : Ty E), _ at h
      simp at h
    exact ⟨ResolutionCapabilities.stable c.native _ hv hn,
      rfl, rfl, rfl⟩

/-- Stable leaves are checked against the retained intrinsic bound by the
ordinary semantic subtype checker. -/
def stable (c : ResolutionContext E) (scope : List (Binding E)) (A : Ty E)
    (images : InstanceImageCheck E.graph) : Option (Checked c scope A) :=
  if E.graph.hasKind .value A then
    if accepted : (CertificateProducer.comparisonUsing E.graph images A c.stable).accepted = true then
      some {
        observation := A
        result := A
        sound := fun η _ => by
          have hv : ValueFam (valueMeaning E η A) :=
            (MixedFamily.value ⟨_, mixedMeaning_valid _ _ _⟩).2
          have hn : FamLe (valueMeaning E η A) c.stableFamily := by
            rw [← c.stable_meaning η]
            exact fun n W v h => CertificateProducer.comparisonUsing_sound accepted η n W (.inl v) h
          exact ⟨ResolutionCapabilities.stable c.native _ hv hn,
            rfl, rfl, rfl⟩ }
    else none
  else none

/-- A subtype of an enclosing descriptor's result is stable by that
scope's checked descriptor assignment. -/
def stableInScope (c : ResolutionContext E) (scope : List (Binding E)) (A : Ty E)
    (images : InstanceImageCheck E.graph) : Option (Checked c scope A) := do
  if !E.graph.hasKind .value A then none else
    scope.findSome? fun b =>
      if member : b ∈ scope then
        if accepted : (CertificateProducer.comparisonUsing E.graph images A b.result).accepted = true then
          some {
            observation := A
            result := A
            sound := fun η hs => by
              obtain ⟨d, _, _, hr⟩ := hs b member
              have hv : ValueFam (valueMeaning E η A) :=
                (MixedFamily.value ⟨_, mixedMeaning_valid _ _ _⟩).2
              have hn : FamLe (valueMeaning E η A) c.stableFamily := by
                intro n W v h
                apply d.stable n W v
                rw [hr]
                exact CertificateProducer.comparisonUsing_sound accepted η n W (.inl v) h
              exact ⟨ResolutionCapabilities.stable c.native _ hv hn,
                rfl, rfl, rfl⟩ }
        else none
      else none

/-- Native lifting observes the literal payload and retains its stable result. -/
def native (c : ResolutionContext E) (scope : List (Binding E)) (l : Label E.signature)
    (payload : { A : Ty E // l = (c.promise.application A).label ∧ E.graph.hasKind .value A = true })
    (child : Checked c scope payload.1) : Checked c scope [l] where
  observation := payload.1
  result := child.result
  sound η hs := by
    obtain ⟨d, hd, _, hr⟩ := child.sound η hs
    refine ⟨c.promise.descriptor c.native d, ?_, hd, hr⟩
    exact c.promise.descriptor_input c.native η l payload d hd

/-- Equivalent input types retain the same descriptor. -/
def equivalent (c : ResolutionContext E) (scope : List (Binding E)) {A B : Ty E}
    (child : Checked c scope B)
    (equality : ∀ η, valueMeaning E η A = valueMeaning E η B) : Checked c scope A where
  observation := child.observation
  result := child.result
  sound η hs := by
    obtain ⟨d, hd, ho, hr⟩ := child.sound η hs
    exact ⟨d, hd.trans (equality η).symm, ho, hr⟩

/-- Combining union arms retains every arm's observation and result. -/
def append (c : ResolutionContext E) (scope : List (Binding E))
    {A B : Ty E} (left : Checked c scope A) (right : Checked c scope B) :
    Checked c scope (A ++ B) where
  observation := left.observation ++ right.observation
  result := left.result ++ right.result
  sound η hs := describes_append c η (left.sound η hs) (right.sound η hs)

/-- The fuel bounds certificate traversal only; every successful branch carries
its semantic proof. Binder lookup checks the complete input type. -/
def check (c : ResolutionContext E) (scope : List (Binding E))
    (images : InstanceImageCheck E.graph) :
    Nat → (A : Ty E) → ResolutionWire.Certificate → Option (Checked c scope A)
  | 0, _, _ => none
  | fuel + 1, A, certificate => match certificate with
    | .stable => (stable c scope A images).orElse fun _ => stableInScope c scope A images
    | .native cert => match A with
      | [l] => do
        let payload ← c.promise.payload l
        let child ← check c scope images fuel payload.1 cert
        return native c scope l payload child
      | _ => none
    | .binder name => do
      let b ← scope.find? (fun b => b.name == name)
      if member : b ∈ scope then
        if E.graph.hasKind .value A then
          if accepted : (CertificateProducer.comparisonUsing E.graph images A b.input).accepted = true then
            let bound : Checked c scope b.input := {
              observation := b.observation
              result := b.result
              sound := fun _ hs => hs b member }
            if reverse : (CertificateProducer.comparisonUsing E.graph images b.input A).accepted = true then
              return equivalent c scope bound fun η => by
                funext n W v
                apply propext
                exact ⟨fun h => CertificateProducer.comparisonUsing_sound accepted η n W (.inl v) h,
                  fun h => CertificateProducer.comparisonUsing_sound reverse η n W (.inl v) h⟩
            else stable c scope A images
          else none
        else none
      else none
    | .union arms =>
      let rec collect : (A : Ty E) → List ResolutionWire.Certificate → Option (Checked c scope A)
        | [], [] => some (empty c scope)
        | a :: rest, cert :: certs => do
          let first ← check c scope images fuel [a] cert
          let remaining ← collect rest certs
          return append c scope first remaining
        | _, _ => none
      collect A arms

private def emptyFamily : MixedFamily :=
  ⟨fun _ _ _ => False,
    ⟨⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩, fun _ _ _ h => h.elim⟩⟩

private theorem assign_empty {E : Equations} (bs : List (Label E.signature)) :
    assign (ParameterAssignment.empty .mixed) bs (bs.map fun _ => emptyFamily) =
      ParameterAssignment.empty .mixed := by
  classical
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ bs
  · exact assign_map_mem _ _ _ hp
  · exact assign_map_nmem _ _ _ hp

private theorem empty_allowed (c : ResolutionContext E) (source : SchemeRow (Label E.signature))
    (valid : source.resolutionValid = true) :
    c.domain.allowed source (source.binders.map fun _ => emptyFamily) := by
  refine ⟨resolutionValid_protected valid, ?_⟩
  intro g hg
  have positions : g.input < source.binders.length ∧ g.observation < source.binders.length ∧
      g.result < source.binders.length := by
    simp only [SchemeRow.resolutionValid, Bool.or_eq_true] at valid
    rcases valid with ordinary | qualified
    · have he : source.resolution = [] := List.isEmpty_iff.mp ordinary
      simp [he] at hg
    · have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp qualified).2 g hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
  have atPosition (i : Nat) (hi : i < source.binders.length) :
      (source.binders.map fun _ => emptyFamily)[i]? = some emptyFamily := by
    simp [hi]
  have bounded : FamLe emptyFamily.value.1 c.stableFamily := fun _ _ _ h => h.elim
  have stable := ResolutionCapabilities.Resolves.stable (P := c.promise.constructor) emptyFamily.value.2 bounded
  have observe := ResolutionCapabilities.Observes.stable (P := c.promise.constructor) emptyFamily.value.2 bounded
  exact ⟨emptyFamily, emptyFamily, emptyFamily,
    atPosition _ positions.1, atPosition _ positions.2.1, atPosition _ positions.2.2,
    bounded, stable, observe, stable⟩

/-- The row a stable-bounded input is read as: a candidate meet row whose only
part is the input and whose clauses include every clause of the bound, else
the input's own row. The candidate is checked here; any choice is sound. -/
def boundedRow [DecidableEq ι] (G : NormalGraph ι) (t : ι) (B candidates : List ι) : ι :=
  (candidates.find? fun m => G.meetRow m && meetParts G m == [t] &&
    B.all fun l => G.plain l && (G l).all fun c => decide (c ∈ meetClauses G m)).getD t

private theorem single_value {ι : Type} (G : NormalGraph ι) (η : MixedAssignment ι) (l : ι) (n W v) :
    mixedValues G η [l] n W v ↔ qDenoteWithArgs G (mixedParameters G) (η, l) n W v := by
  change (∃ i ∈ [l], _) ↔ _
  simp

/-- Within the bound, the bounded row denotes exactly the input. -/
theorem boundedRow_value [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {t : ι} {B : List ι} (candidates : List ι)
    (kt : G.parameterKinds t = some .value)
    (bound : ∀ n W v, mixedValues G η [t] n W v → mixedValues G η B n W v) (n W v) :
    mixedValues G η [boundedRow G t B candidates] n W v ↔ mixedValues G η [t] n W v := by
  unfold boundedRow
  cases hf : candidates.find? (fun m => G.meetRow m && meetParts G m == [t] &&
      B.all fun l => G.plain l && (G l).all fun c => decide (c ∈ meetClauses G m)) with
  | none => exact Iff.rfl
  | some m =>
    have hm := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hm
    obtain ⟨⟨hrow, hparts⟩, hclauses⟩ := hm
    have hpart : G.partRow t = true := by
      simp [NormalGraph.partRow, NormalGraph.params, kt]
    simp only [Option.getD_some]
    rw [single_value, single_value, meet_row_iff hrow, hparts]
    constructor
    · rintro ⟨hp, _⟩
      exact (part_denote hpart).mpr (hp t (List.mem_singleton_self t))
    · intro ht
      refine ⟨fun q hq => ?_, ?_⟩
      · rw [List.mem_singleton] at hq
        subst hq
        exact (part_denote hpart).mp ht
      · obtain ⟨l, hl, hv⟩ := bound n W v ((single_value G η t n W v).mpr ht)
        obtain ⟨hplain, hcs⟩ := hclauses l hl
        obtain ⟨c, hc, hcv⟩ := (mixed_unfold_plain η hplain n W v).mp hv
        exact ⟨c, hcs c hc, hcv⟩

/-- The aliases one resolution group contributes: where its input has a closed
declared bound within the stable family, the observation and result are read
as the input's bounded row, the canonical meet of the input and its bound,
which is how a body reads a bounded binder. -/
def stableAlias (c : ResolutionContext E) (source : SchemeRow (Label E.signature))
    (images : InstanceImageCheck E.graph)
    (g : PositiveGraphs.ResolutionSlots) : List (Label E.signature × Label E.signature) :=
  match QualifiedGraphs.groupBinders E.graph source g with
  | none => []
  | some (t, o, r) => match source.bounds.find? (·.1 == t) with
    | none => []
    | some (_, B) =>
      if decide source.binders.Nodup && B.all (·.free.isEmpty) &&
          (CertificateProducer.comparisonUsing E.graph images B c.stable).accepted then
        let candidates := (Label.ofTree? (canonMeet (t.1 :: B.map (·.1)))).toList
        let m := boundedRow E.graph t B candidates
        [(r, m), (o, m)]
      else []

def stableAliases (c : ResolutionContext E) (source : SchemeRow (Label E.signature))
    (images : InstanceImageCheck E.graph) :
    List (Label E.signature × Label E.signature) :=
  source.resolution.flatMap (stableAlias c source images)

/-- **Stable bound.** A resolution-qualified input bounded within the stable
family is its own observation and result (`Descriptor.exactStable`), so each
alias denotes the input at every admitted, bounded assignment. -/
theorem stableAliases_sound (c : ResolutionContext E) (domain : E.domain = c.domain)
    (source : SchemeRow (Label E.signature)) (images : InstanceImageCheck E.graph) :
    ProgramCertificates.AliasesSound E.graph source (stableAliases c source images) := by
  intro η As length allowed bounded p hp n W v
  obtain ⟨g, hg, hp⟩ := List.mem_flatMap.mp hp
  unfold stableAlias at hp
  split at hp
  · cases hp
  rename_i t o r hgb
  split at hp
  · cases hp
  rename_i t' B hf
  split at hp
  rotate_left
  · cases hp
  rename_i checked
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.isEmpty_iff] at checked
  obtain ⟨⟨unique, closed⟩, accepted⟩ := checked
  have allowed' : c.domain.allowed source As := by
    have h : E.domain.allowed source As := allowed
    rwa [domain] at h
  obtain ⟨ht, ho, hr, kt, ko, kr⟩ := QualifiedGraphs.groupBinders_some hgb
  obtain ⟨d, et, eo, er⟩ := QualifiedGraphs.assigned_descriptor (C := c.capabilities) E.graph η
    source As allowed' g hg t o r
    (QualifiedGraphs.assignment_position unique length ht)
    (QualifiedGraphs.assignment_position unique length ho)
    (QualifiedGraphs.assignment_position unique length hr) kt ko kr
  have hmem : (t', B) ∈ source.bounds := List.mem_of_find?_eq_some hf
  have hname : t' = t := Subtype.ext (by simpa using List.find?_some hf)
  subst hname
  have hbinder : t' ∈ source.binders := List.mem_of_getElem? ht
  let η' := assign η source.binders As
  -- The input lies within its bound, read at the enclosing assignment.
  have within : ∀ j U u, mixedValues E.graph η' [t'] j U u →
      mixedMeaning E.graph η B j U (.inl u) := by
    intro j U u hu
    have h1 : mixedMeaning E.graph η' [t'] j U (.inl u) := hu
    rw [mixedMeaning_parameter E.graph η' t' .value kt] at h1
    exact bounded (j + 1) (t', B) hmem hbinder j (by omega) U (.inl u) h1.2
  have stable : FamLe d.input c.stableFamily := by
    intro j U u hu
    rw [← c.stable_meaning η]
    exact CertificateProducer.comparisonUsing_sound accepted η j U (.inl u)
      (within j U u (by rw [et]; exact hu))
  have hresult : d.result = d.input := d.result_eq_input stable
  have hobservation : d.observation = d.input := (d.exactStable stable).1
  have same : mixedMeaning E.graph η B = mixedMeaning E.graph η' B :=
    E.agree_free η η' B (fun l hl q hq => by simp [closed l hl] at hq)
  have row := boundedRow_value (G := E.graph) (η := η')
    (Label.ofTree? (canonMeet (t'.1 :: B.map (·.1)))).toList kt
    (fun j U u hu => by
      have h := within j U u hu
      rw [same] at h
      exact h) n W v
  have input : mixedMeaning E.graph η'
      [boundedRow E.graph t' B (Label.ofTree? (canonMeet (t'.1 :: B.map (·.1)))).toList] n W (.inl v) ↔
      d.input n W v := by
    rw [← et]; exact row
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · change mixedValues E.graph η' [r] n W v ↔ _
    rw [input, er, hresult]
  · change mixedValues E.graph η' [o] n W v ↔ _
    rw [input, eo, hobservation]

/-- Construct the qualified body checker only for a valid source signature,
using the descriptor domain installed in the frozen equations. -/
def bodyChecking (c : ResolutionContext E) (domain : E.domain = c.domain)
    (source : SchemeRow (Label E.signature)) (images : InstanceImageCheck E.graph) :
    Option (RequestJson.QualifiedBody E.graph images) :=
  if valid : source.resolutionValid = true then
    some {
      source := source
      capabilities := c.capabilities
      stable := c.stableFamily
      domain := domain
      body := {
        check := ProgramCertificates.lexicalBodyCheck E.graph images source
          (stableAliases c source images)
        sound := by
          intro A B proof checked
          have allowed : E.graph.domain.allowed source (source.binders.map fun _ => emptyFamily) := by
            change E.domain.allowed _ _
            rw [domain]
            exact empty_allowed c source valid
          have bounded : ∀ m, Bounded (mixedMeaning E.graph) (ParameterAssignment.empty .mixed)
              source (source.binders.map fun _ => emptyFamily) m := by
            intro m b _ hb j _ U u hu
            rw [assign_map_mem _ _ _ hb] at hu
            exact hu.elim
          let body := ProgramCertificates.lexicalBodySubtyping E.graph images source domain
            (stableAliases c source images)
            (stableAliases_sound c domain source images)
            (ParameterAssignment.empty .mixed) (source.binders.map fun _ => emptyFamily)
            (List.length_map ..) allowed bounded
          have result := body.sound checked
          have same : reassign E.graph (ParameterAssignment.empty .mixed) = E.graph := by
            rfl
          simpa only [assign_empty, same] using result }
      aliases := stableAliases c source images
      aliases_sound := stableAliases_sound c domain source images
      check_eq := rfl }
  else none

#print axioms stableInScope
#print axioms stableAliases_sound
#print axioms bodyChecking

#print axioms Checked.sound
#print axioms native
#print axioms equivalent

end Verification.SourceResolution
