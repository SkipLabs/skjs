import Verification.ExperimentState.HeapKnowledge

/-! Checked expression rules with finite state postconditions. Ordinary evidence
retains only immutable-value facts; special rules justify stronger heap facts.
No fact is accepted as an ordinary reference type or captured by a lambda. -/
namespace Verification.ExperimentState.HeapExpressionRules
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower
open HeapFacts HeapKnowledge HeapObservations ProgramCertificates

/-- Copy an immutable slot into the result while preserving the old slots. -/
def copyFacts (fs : Facts) (i : Nat) : Facts :=
  (fs.filter (fun f => f.slot == i)).map (fun f => {f with slot := 0}) ++ HeapFacts.shift fs

def copy (k : Knowledge) (i : Nat) : Knowledge := ⟨copyFacts k.cells i,copyFacts k.values i⟩

theorem copy_holds {k i ρ h} (hk : HeapKnowledge.Holds k ρ h) :
    HeapKnowledge.Holds (copy k i) (push (ρ i) ρ) h := by
  have shifted := HeapKnowledge.shift_holds (v := ρ i) hk
  constructor
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      simpa [push,of_decide_eq_true (show decide (g.slot = i) = true from hg.2)] using hk.1 g hg.1
    · exact shifted.1 f hf
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      simpa [push,of_decide_eq_true (show decide (g.slot = i) = true from hg.2)] using hk.2 g hg.1
    · exact shifted.2 f hf

/-- Primitive slot facts take precedence over the ordinary (possibly wider)
value type. Both sources have independently proved membership. -/
def valuesAt (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i : Nat) : Option (List Literal) :=
  match k.values.find? (fun f => f.slot == i) with
  | some f => some f.contents
  | none => (Γ[i]?).bind (HeapKnowledge.literals G)

theorem valuesAt_sound {G : NormalGraph ι} {Γ k i R ρ n W h}
    (hr : valuesAt G Γ k i = some R) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) : ∃ a ∈ R, ρ i = a.value := by
  unfold valuesAt at hr
  split at hr
  · rename_i f hf
    cases hr
    have hm := List.mem_of_find?_eq_some hf
    have hi : f.slot = i := by simpa using List.find?_some hf
    simpa [hi] using hk.2 f hm
  · cases hb : Γ[i]? with
    | none => simp [hb] at hr
    | some B =>
      simp only [hb,Option.bind_some] at hr
      exact (literals_sem hr n W (ρ i)).mp (he.2 i B hb)

/-- A primitive type's literal set is a structural view, not semantic search. -/
def includes (G : NormalGraph ι) (A : Ty ι) (R : List Literal) : Bool :=
  match literals G A with
  | some S => R.all S.contains
  | none => false

theorem includes_sound {G : NormalGraph ι} {A R v} (hc : includes G A R = true)
    (hv : ∃ a ∈ R, v = a.value) (n W) : meaning G A n W v := by
  unfold includes at hc
  split at hc
  · rename_i S hs
    obtain ⟨a,ha,he⟩ := hv
    apply (literals_sem hs n W v).mpr
    exact ⟨a,List.contains_iff_mem.mp (List.all_eq_true.mp hc a ha),he⟩
  · contradiction

def withResult (k : Knowledge) (R : List Literal) : Knowledge :=
  ⟨k.cells,⟨0,R⟩::k.values⟩

theorem result_holds {k R ρ h v} (hk : HeapKnowledge.Holds k (push v ρ) h)
    (hr : ∃ a ∈ R, v = a.value) : HeapKnowledge.Holds (withResult k R) (push v ρ) h := by
  refine ⟨hk.1,?_⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hr
  · exact hk.2 f hf

/-- Reading uses a current-cell fact; its result is also an immutable value fact.
This latter fact is what permits a subsequent result-contract check to retain
precision even when the producer supplied a wider expression type. -/
def readOutput (k : Knowledge) (R : List Literal) : Knowledge := withResult (HeapKnowledge.shift k) R

theorem read_sound {G : NormalGraph ι} {Γ k i R A ρ n W h}
    (hm : Fact.mk i R ∈ k.cells) (hc : includes G A R = true)
    (_he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readOutput k R) (push v ρ) h') n W h (.read (ρ i)) := by
  obtain ⟨l,v,hl,hv,a,ha,rfl⟩ := hk.1 _ hm
  rw [hl]
  apply consequence _ _ (read_observed hw hh (by cases a <;> rfl) hv)
  · intro j U u hu; exact includes_sound hc ⟨a,ha,hu⟩ j U
  · intro h' u hp
    rw [hp.1]
    exact result_holds (HeapKnowledge.shift_holds hk) ⟨a,ha,hp.2⟩

theorem value_sound {G : NormalGraph ι} {Γ k i R A ρ n W h}
    (hr : valuesAt G Γ k i = some R) (hc : includes G A R = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (withResult (copy k i) R) (push v ρ) h') n W h (ρ i) := by
  have hv := valuesAt_sound hr he hk
  have hval : isVal (ρ i) = true := by
    obtain ⟨a,_,ha⟩ := hv; rw [ha]; cases a <;> rfl
  exact HeapObservations.value hval (includes_sound hc hv n W)
    (result_holds (copy_holds hk) hv)

/-- Ordinary calls and arbitrary expressions retain immutable snapshots, but no
heap observation without a specific proved effect rule. -/
def ordinaryOutput (k : Knowledge) : Knowledge := ⟨[],HeapFacts.shift k.values⟩

theorem ordinary_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k t A ρ n W h}
    (ht : HasTy G Γ t A) (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (ordinaryOutput k) (push v ρ) h') n W h (instantiate 0 ρ t) := by
  apply of_value_property _ (ht.sound n W h ρ he hw hh)
  intro _ _ heap v _
  exact ⟨holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2⟩

/-- Allocation retains facts about old cells and records the fresh cell. -/
def allocOutput (k : Knowledge) (R : List Literal) : Knowledge :=
  ⟨⟨0,R⟩ :: HeapFacts.shift k.cells, HeapFacts.shift k.values⟩

theorem alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i R A ρ n W h}
    (ht : HasTy G Γ (.alloc (.var i)) A)
    (hr : valuesAt G Γ k i = some R)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (allocOutput k R) (push v ρ) h')
      n W h (.alloc (ρ i)) := by
  obtain ⟨a,ha,hv⟩ := valuesAt_sound hr he hk
  have hvv : isVal (ρ i) = true := by rw [hv]; cases a <;> rfl
  apply one_step rfl rfl (.allocV hvv) _
    (by simpa [instantiate] using ht.sound n W h ρ he hw hh)
  refine ⟨?_,(HeapKnowledge.shift_holds (v := .loc h.length) hk).2⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact ⟨h.length,ρ i,rfl,alloc_new h (ρ i),a,ha,hv⟩
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    obtain ⟨l,v,hl,hh',b,hb,hv'⟩ := hk.1 g hg
    exact ⟨l,v,hl,alloc_frame hh',b,hb,hv'⟩

/-- A write forgets all old cell observations (including aliases), establishes
its new contents, and retains immutable values already read into slots. -/
def writeOutput (k : Knowledge) (i : Nat) (R : List Literal) : Knowledge :=
  ⟨[⟨i+1,R⟩],⟨0,[.nul]⟩ :: HeapFacts.shift k.values⟩

theorem write_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i j R old A ρ n W h}
    (ht : HasTy G Γ (.write (.var i) (.var j)) A)
    (hm : Fact.mk i old ∈ k.cells) (hr : valuesAt G Γ k j = some R)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (writeOutput k i R) (push v ρ) h')
      n W h (.write (ρ i) (ρ j)) := by
  obtain ⟨l,v,hl,hlookup,_⟩ := hk.1 _ hm
  obtain ⟨a,ha,hv⟩ := valuesAt_sound hr he hk
  have hvv : isVal (ρ j) = true := by rw [hv]; cases a <;> rfl
  have hlt := (List.getElem?_eq_some_iff.mp hlookup).1
  have hs := ht.sound n W h ρ he hw hh
  simp [instantiate] at hs
  rw [hl] at hs ⊢
  apply one_step rfl rfl (.writeV hvv hlt) _ hs
  constructor
  · intro f hf
    have hf : f = ⟨i+1,R⟩ := List.mem_singleton.mp hf
    subst f
    exact ⟨l,ρ j,hl,write_new hlt,a,ha,hv⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨.nul,by simp,rfl⟩
    · exact (HeapKnowledge.shift_holds (v := .nul) hk).2 f hf

/-- Source lowering inserts variable copies and literal/lambda nodes between
operations. These are pure: unlike calls they must not discard cell facts. -/
def pureTerm : Tm → Bool
  | .var _ => true
  | t => isVal t

def pureOutput (k : Knowledge) : Tm → Knowledge
  | .var i => copy k i
  | _ => HeapKnowledge.shift k

theorem pure_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k t A ρ n W h}
    (ht : HasTy G Γ t A) (hp : pureTerm t = true)
    (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (pureOutput k t) (push v ρ) h')
      n W h (instantiate 0 ρ t) := by
  have hs := ht.sound n W h ρ he hw hh
  cases t <;> simp only [pureTerm,isVal] at hp
  all_goals try contradiction
  case var i =>
    have hi : i < Γ.length := by simpa [checkScope] using hc
    have hv := meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))
    simpa [instantiate,pureOutput] using
      refine_value hv.1 (copy_holds hk) (show Safe (meaning G A) n W h (ρ i) by simpa [instantiate] using hs)
  all_goals exact refine_value rfl (HeapKnowledge.shift_holds hk) hs

/-- Evidence names the particular observation used. The checker binds it to
an actual source sequent, so neither the slot nor the requested result type can
be changed by an untrusted producer. -/
inductive StepEvidence (ι : Type) where
  | ordinary (proof : ProgramCertificates.Evidence ι)
  | pure (proof : ProgramCertificates.Evidence ι)
  | observedRead (slot : Nat) (contents : List Literal)
  | knownValue (slot : Nat) (contents : List Literal)
  | allocated (slot : Nat) (contents : List Literal) (proof : ProgramCertificates.Evidence ι)
  | written (receiver value : Nat) (old contents : List Literal) (proof : ProgramCertificates.Evidence ι)

/-- The successful result is the guaranteed postcondition in the result-pushed
frame. Edge checking must entail the destination's facts from this output;
checking a node alone does not establish its supplied input knowledge. -/
def checkStep [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι)
    (k : Knowledge) : StepEvidence ι → Option Knowledge
  | .ordinary e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTree G e = true
    then some (ordinaryOutput k) else none
  | .pure e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧
        checkTree G e = true ∧ pureTerm j.term = true
    then some (pureOutput k j.term) else none
  | .observedRead i R =>
    if j.term = .read (.var i) ∧ i < j.context.length ∧
        Fact.mk i R ∈ k.cells ∧ includes G j.type R = true
    then some (readOutput k R) else none
  | .knownValue i R =>
    if j.term = .var i ∧ i < j.context.length ∧
        valuesAt G j.context k i = some R ∧ includes G j.type R = true
    then some (withResult (copy k i) R) else none
  | .allocated i R e =>
    if claim e = j ∧ checkTree G e = true ∧
        j.term = .alloc (.var i) ∧ i < j.context.length ∧
        valuesAt G j.context k i = some R
    then some (allocOutput k R) else none
  | .written i v old R e =>
    if claim e = j ∧ checkTree G e = true ∧
        j.term = .write (.var i) (.var v) ∧ i < j.context.length ∧ v < j.context.length ∧
        Fact.mk i old ∈ k.cells ∧ valuesAt G j.context k v = some R
    then some (writeOutput k i R) else none

theorem checkStep_sound [DecidableEq ι] {G : NormalGraph ι} {j k e out}
    (hc : checkStep G j k e = some out) {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds out (push v ρ) h')
      n W h (instantiate 0 ρ j.term) := by
  cases e with
  | ordinary e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,_,ht⟩ := hp
      have typed := checkTree_sound e ht
      rw [hj] at typed
      cases hc
      exact ordinary_sound typed he hk hw hh
    · contradiction
  | pure e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,scope,ht,hpure⟩ := hp
      have typed := checkTree_sound e ht
      rw [hj] at typed
      cases hc
      exact pure_sound typed hpure scope he hk hw hh
    · contradiction
  | observedRead i R =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨ht,_,hm,hi⟩ := hp
      cases hc
      rw [ht]
      simpa [instantiate] using read_sound hm hi he hk hw hh
    · contradiction
  | knownValue i R =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨ht,_,hr,hi⟩ := hp
      cases hc
      rw [ht]
      simpa [instantiate] using value_sound hr hi he hk
    · contradiction
  | allocated i R e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,ht,term,_,hr⟩ := hp
      have typed := checkTree_sound e ht
      rw [hj] at typed
      rw [term] at typed
      cases hc
      rw [term]
      simpa [instantiate] using alloc_sound typed hr he hk hw hh
    · contradiction
  | written i v old R e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,ht,term,_,_,hm,hr⟩ := hp
      have typed := checkTree_sound e ht
      rw [hj] at typed
      rw [term] at typed
      cases hc
      rw [term]
      simpa [instantiate] using write_sound typed hm hr he hk hw hh
    · contradiction

#print axioms checkStep_sound
#print axioms read_sound
#print axioms value_sound
#print axioms ordinary_sound
end Verification.ExperimentState.HeapExpressionRules
