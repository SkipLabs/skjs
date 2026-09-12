import Verification.ExperimentState.HeapKnowledge

/-! Checked expression rules with finite state postconditions. Ordinary evidence
retains only immutable-value facts; special rules justify stronger heap facts.
No fact is accepted as an ordinary reference type or captured as a permanent call contract. -/
namespace Verification.ExperimentState.HeapExpressionRules
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower
open HeapFacts HeapKnowledge HeapObservations ProgramCertificates

/-- Copy an immutable slot into the result while preserving the old slots. -/
def copyFacts (fs : Facts) (i : Nat) : Facts :=
  (fs.filter (fun f => f.slot == i)).map (fun f => {f with slot := 0}) ++ HeapFacts.shift fs

def copySlots (i j : Nat) : List Nat := if j = i then [0,j+1] else [j+1]

def copy (k : Knowledge) (i : Nat) : Knowledge := ⟨copyFacts k.cells i,copyFacts k.values i,⟨0,i+1,true⟩ :: HeapLinks.pull k.links (copySlots i)⟩

theorem copy_holds {k i ρ h} (hk : HeapKnowledge.Holds k ρ h) :
    HeapKnowledge.Holds (copy k i) (push (ρ i) ρ) h := by
  have shifted := HeapKnowledge.shift_holds (v := ρ i) hk
  refine ⟨?_,?_,?_⟩
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
      simpa [push,of_decide_eq_true (show decide (g.slot = i) = true from hg.2)] using hk.2.1 g hg.1
    · exact shifted.2.1 f hf

  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · rfl
    · have hp := HeapLinks.pull_holds (pre := copySlots i) (τ := push (ρ i) ρ) hk.2.2 (by
        intro j v hv
        unfold copySlots at hv
        split at hv
        · rename_i hj
          rcases List.mem_cons.mp hv with rfl | hv
          · simpa [push,hj]
          · have hv := List.mem_singleton.mp hv; subst v; rfl
        · have hv := List.mem_singleton.mp hv; subst v; rfl)
      exact hp g hg

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
    simpa [hi] using hk.2.1 f hm
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
  ⟨k.cells,⟨0,R⟩::k.values,k.links⟩

theorem result_holds {k R ρ h v} (hk : HeapKnowledge.Holds k (push v ρ) h)
    (hr : ∃ a ∈ R, v = a.value) : HeapKnowledge.Holds (withResult k R) (push v ρ) h := by
  refine ⟨hk.1,?_,hk.2.2⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hr
  · exact hk.2.1 f hf

/-- An ordinary typed read preserves the heap and records which cell its result
came from. This does not claim the cell had any particular contents beforehand. -/
def readFrame (k : Knowledge) (i : Nat) : Knowledge :=
  let out := HeapKnowledge.shift k
  {out with links := (HeapLinks.aliases k.links i).map (fun j => ⟨j+1,0,false⟩) ++ out.links}

/-- Reading uses a current-cell fact; its result is also an immutable value fact.
This latter fact is what permits a subsequent result-contract check to retain
precision even when the producer supplied a wider expression type. -/
def readOutput (k : Knowledge) (i : Nat) (R : List Literal) : Knowledge :=
  withResult (readFrame k i) R

theorem read_sound {G : NormalGraph ι} {Γ k i R A ρ n W h}
    (hm : Fact.mk i R ∈ k.cells) (hc : includes G A R = true)
    (_he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readOutput k i R) (push v ρ) h') n W h (.read (ρ i)) := by
  obtain ⟨l,c,v,hl,hv,a,ha,rfl⟩ := hk.1 _ hm
  rw [hl]
  apply consequence _ _ (read_observed hw hh (by cases a <;> rfl) hv)
  · intro j U u hu; exact includes_sound hc ⟨a,ha,hu⟩ j U
  · intro h' u hp
    rw [hp.1]
    have hout := result_holds (HeapKnowledge.shift_holds hk) ⟨a,ha,hp.2⟩
    refine ⟨hout.1,hout.2.1,?_⟩
    intro link hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      have he := HeapLinks.aliases_eq hk.2.2 hj
      exact ⟨l,c,he.trans hl,by simpa [push,hp.2] using hv⟩
    · exact hout.2.2 link hm

/-- The first invariant bag operand, for either plain or callable objects. -/
def bagOperand : List (PositiveNormalization.Clause α) → Option α
  | [.refs B _] | [.callable B _ _] => some B
  | _ => none

theorem bagOperand_sound {G : NormalGraph ι} {Ref B n W v}
    (hr : bagOperand (expand G Ref) = some B) (hv : meaning G Ref n W v) :
    bagT (meaning G B) n W v := by
  unfold bagOperand at hr
  split at hr
  · rename_i A rest he
    cases hr
    exact refT_bag ((represents_sem he n W v).mp hv).1
  · rename_i A rest L he
    cases hr
    exact ((represents_sem he n W v).mp hv).1.1
  · contradiction

theorem typedRead_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i Ref B A ρ n W h}
    (ht : HasTy G Γ (.read (.var i)) A) (hi : Γ[i]? = some Ref)
    (hr : bagOperand (expand G Ref) = some B)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readFrame k i) (push v ρ) h') n W h (.read (ρ i)) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨l,code,hl,_,r,c,hproj,hlookup,hagree⟩ := bagOperand_sound hr (he.2 i Ref hi)
    cases hproj
    obtain ⟨v,hv,hmem⟩ := hh.2 l c hlookup
    have hval := meaning_valOnly G B 0 _ v ((hagree 0 (by omega) _ v).mp (hmem 0 (by omega)))
    have hs : Safe (meaning G A) (n+1) W h (.read (ρ i)) := by
      simpa [instantiate] using ht.sound (n+1) W h ρ he hw hh
    rw [hl] at hs ⊢
    apply one_step rfl hval (.readV hv) _ hs
    have hout := HeapKnowledge.shift_holds (v := v) hk
    refine ⟨hout.1,hout.2.1,?_⟩
    intro link hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      exact ⟨l,code,(HeapLinks.aliases_eq hk.2.2 hj).trans hl,hv⟩
    · exact hout.2.2 link hm

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
def ordinaryOutput (k : Knowledge) : Knowledge := ⟨[],HeapFacts.shift k.values,HeapLinks.stable (HeapKnowledge.shift k).links⟩

theorem ordinary_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k t A ρ n W h}
    (ht : HasTy G Γ t A) (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (ordinaryOutput k) (push v ρ) h') n W h (instantiate 0 ρ t) := by
  apply of_value_property _ (ht.sound n W h ρ he hw hh)
  intro _ _ heap v _
  exact ⟨holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2.1,HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2⟩

/-- Allocation retains facts about old cells and records the fresh cell. -/
def allocOutput (k : Knowledge) (R : List Literal) : Knowledge :=
  ⟨⟨0,R⟩ :: HeapFacts.shift k.cells, HeapFacts.shift k.values,(HeapKnowledge.shift k).links⟩

theorem alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i R A ρ n W h} {code : CallCode}
    (hr : valuesAt G Γ k i = some R)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hs : Safe (meaning G A) n W h (.make code (ρ i))) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (allocOutput k R) (push v ρ) h')
      n W h (.make code (ρ i)) := by
  obtain ⟨a,ha,hv⟩ := valuesAt_sound hr he hk
  have hvv : isVal (ρ i) = true := by rw [hv]; cases a <;> rfl
  apply one_step rfl rfl (.makeV hvv) _ hs
  refine ⟨?_,(HeapKnowledge.shift_holds (v := .obj h.length code) hk).2.1,
    HeapLinks.alloc_frame (HeapKnowledge.shift_holds (v := .obj h.length code) hk).2.2⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact ⟨h.length,code,ρ i,rfl,alloc_new h (ρ i),a,ha,hv⟩
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    obtain ⟨l,c,v,hl,hh',b,hb,hv'⟩ := hk.1 g hg
    exact ⟨l,c,v,hl,alloc_frame hh',b,hb,hv'⟩

/-- A write forgets all old cell observations (including aliases), establishes
its new contents, and retains immutable values already read into slots. -/
def writeOutput (k : Knowledge) (i : Nat) (R : List Literal) : Knowledge :=
  ⟨(HeapLinks.aliases k.links i).map (fun j => ⟨j+1,R⟩),⟨0,[.nul]⟩ :: HeapFacts.shift k.values,HeapLinks.stable (HeapKnowledge.shift k).links⟩

private theorem write_inv {h a b h' t} (ha : isVal a = true) (hb : isVal b = true)
    (hs : Step h (.write a b) h' t) :
    ∃ l c, a = .obj l c ∧ l < h.length ∧ h' = h.set l b ∧ t = .nul := by
  cases hs with
  | writeC1 hs => exact False.elim (value_no_step ha hs)
  | writeC2 _ hs => exact False.elim (value_no_step hb hs)
  | writeV _ hl => exact ⟨_,_,rfl,hl,rfl,rfl⟩

/-- The ordinary typing proof guarantees a writable location. An old observation
is unnecessary: the postcondition depends only on the value being written. -/
theorem write_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i j R A ρ n W h}
    (ht : HasTy G Γ (.write (.var i) (.var j)) A) (hi : i < Γ.length)
    (hr : valuesAt G Γ k j = some R)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (writeOutput k i R) (push v ρ) h')
      n W h (.write (ρ i) (ρ j)) := by
  obtain ⟨a,ha,hv⟩ := valuesAt_sound hr he hk
  have hvv : isVal (ρ j) = true := by rw [hv]; cases a <;> rfl
  have hiv := (meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
  have hs : Safe (meaning G A) n W h (.write (ρ i) (ρ j)) := by
    simpa [instantiate] using ht.sound n W h ρ he hw hh
  cases n with
  | zero => trivial
  | succ n =>
    have step := hs
    rcases step with ⟨hbad,_⟩ | ⟨U,h',t',_,_,step,_,_⟩
    · contradiction
    · obtain ⟨l,c,hl,hlt,_,_⟩ := write_inv hiv hvv step
      rw [hl] at hs ⊢
      apply one_step rfl rfl (.writeV hvv hlt) _ hs
      refine ⟨?_,?_,HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := .nul) hk).2.2⟩
      · intro f hf
        obtain ⟨slot,hs,rfl⟩ := List.mem_map.mp hf
        have heq := HeapLinks.aliases_eq hk.2.2 hs
        exact ⟨l,c,ρ j,heq.trans hl,write_new hlt,a,ha,hv⟩
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨.nul,by simp,rfl⟩
        · exact (HeapKnowledge.shift_holds (v := .nul) hk).2.1 f hf

/-- Source lowering inserts variable copies and literal nodes between
operations. These are pure: unlike calls they must not discard cell facts. -/
def pureTerm : Tm → Bool
  | .var _ => true
  | .test _ a => pureTerm a
  | .ite c t e => pureTerm c && pureTerm t && pureTerm e
  | t => isVal t

/-- Purity is closed under actual reduction and rules out every heap change.
Stored closure bodies need not be pure: observing an object does not invoke it. -/
theorem pure_step {h t h' t'} (hs : Step h t h' t') (hp : pureTerm t = true) :
    h' = h ∧ pureTerm t' = true := by
  induction hs <;> simp_all [pureTerm,isVal]
  case testV => split <;> simp [pureTerm,isVal]

theorem pure_instantiate {G : NormalGraph ι} {Γ t ρ n W}
    (hp : pureTerm t = true) (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) : pureTerm (instantiate 0 ρ t) = true := by
  induction t using Tm.induct <;> simp_all [pureTerm,isVal,instantiate,checkScope]
  case var i =>
    have hi : i < Γ.length := by omega
    have hv := (meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
    cases h : ρ i <;> simp_all [pureTerm,isVal]

/-- Any heap predicate can be framed across a checked pure computation. -/
theorem pure_frame {T Q} : ∀ {n W h t}, Safe T n W h t → pureTerm t = true →
    (∀ v, Q h v) → SafePost T Q n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs hp hq
    rcases hs with ⟨hv,ht⟩ | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl ⟨hv,ht,hq t⟩
    · obtain ⟨rfl,hp'⟩ := pure_step step hp
      exact Or.inr ⟨U,_,t',hx,hu,step,hh,ih hs hp' hq⟩

def pureOutput (k : Knowledge) : Tm → Knowledge
  | .var i => copy k i
  | .nul => withResult (HeapKnowledge.shift k) [.nul]
  | .undef => withResult (HeapKnowledge.shift k) [.undef]
  | .tru => withResult (HeapKnowledge.shift k) [.tru]
  | .fls => withResult (HeapKnowledge.shift k) [.fls]
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
  have hpClosed := pure_instantiate hp hc he
  cases t <;> simp only [pureTerm,isVal] at hp
  all_goals try contradiction
  case var i =>
    have hi : i < Γ.length := by simpa [checkScope] using hc
    have hv := meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))
    simpa [instantiate,pureOutput] using
      refine_value hv.1 (copy_holds hk) (show Safe (meaning G A) n W h (ρ i) by simpa [instantiate] using hs)
  all_goals first
    | exact pure_frame hs hpClosed (fun _ => HeapKnowledge.shift_holds hk)
    | exact refine_value rfl (result_holds (HeapKnowledge.shift_holds hk) ⟨.nul,by simp,rfl⟩) hs
    | exact refine_value rfl (result_holds (HeapKnowledge.shift_holds hk) ⟨.undef,by simp,rfl⟩) hs
    | exact refine_value rfl (result_holds (HeapKnowledge.shift_holds hk) ⟨.tru,by simp,rfl⟩) hs
    | exact refine_value rfl (result_holds (HeapKnowledge.shift_holds hk) ⟨.fls,by simp,rfl⟩) hs
    | exact refine_value rfl (HeapKnowledge.shift_holds hk) hs

/-- Creating a function allocates a fresh bag without executing its body or
invalidating knowledge about existing cells. -/
theorem creation_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k b A ρ n W h}
    (ht : HasTy G Γ (.funE b) A) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h')
      n W h (instantiate 0 ρ (.funE b)) := by
  have hs := ht.sound n W h ρ he hw hh
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with ⟨hv, _⟩ | ⟨U,h',t',hx,hu,step,hh',hs'⟩
    · simp [instantiate,Tm.funE,isVal] at hv
    · obtain ⟨rfl,rfl⟩ := make_step_inv rfl step
      exact Or.inr ⟨U,_,_,hx,hu,step,hh',
        refine_value rfl (HeapKnowledge.shift_holds (HeapKnowledge.alloc_frame hk)) hs'⟩

/-- Evidence names the particular observation used. The checker binds it to
an actual source sequent, so neither the slot nor the requested result type can
be changed by an untrusted producer. -/
inductive StepEvidence (ι : Type) where
  | ordinary (proof : ProgramCertificates.Evidence ι)
  | pure (proof : ProgramCertificates.Evidence ι)
  | created (proof : ProgramCertificates.Evidence ι)
  | typedRead (slot : Nat) (element : Ty ι) (proof : ProgramCertificates.Evidence ι)
  | observedRead (slot : Nat) (contents : List Literal)
  | knownValue (slot : Nat) (contents : List Literal)
  | allocated (slot : Nat) (contents : List Literal) (proof : ProgramCertificates.Evidence ι)
  | written (receiver value : Nat) (contents : List Literal) (proof : ProgramCertificates.Evidence ι)

/-- Only allocation whose initializer is an existing value slot can frame facts.
The descriptor is not evaluated; its code obligations stay in ordinary evidence. -/
def allocationSlot : Tm → Option Nat
  | .make _ (.var i) => some i
  | _ => none

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
  | .created e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTree G e = true then
      match j.term with
      | .funE _ => some (HeapKnowledge.shift k)
      | _ => none
    else none
  | .typedRead i B e =>
    if claim e = j ∧ checkTree G e = true ∧ j.term = .read (.var i) ∧
        (j.context[i]?).any (fun Ref => decide (bagOperand (expand G Ref) = some B))
    then some (readFrame k i) else none
  | .observedRead i R =>
    if j.term = .read (.var i) ∧ i < j.context.length ∧
        Fact.mk i R ∈ k.cells ∧ includes G j.type R = true
    then some (readOutput k i R) else none
  | .knownValue i R =>
    if j.term = .var i ∧ i < j.context.length ∧
        valuesAt G j.context k i = some R ∧ includes G j.type R = true
    then some (withResult (copy k i) R) else none
  | .allocated i R e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTree G e = true ∧
        allocationSlot j.term = some i ∧ i < j.context.length ∧
        valuesAt G j.context k i = some R
    then some (allocOutput k R) else none
  | .written i v R e =>
    if claim e = j ∧ checkTree G e = true ∧
        j.term = .write (.var i) (.var v) ∧ i < j.context.length ∧ v < j.context.length ∧
        valuesAt G j.context k v = some R
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
  | created e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,_,ht⟩ := hp
      have typed := checkTree_sound e ht
      rw [hj] at typed
      split at hc
      · rename_i b hb
        cases hc
        rw [hb] at typed ⊢
        exact creation_sound typed he hk hw hh
      · contradiction
    · contradiction
  | typedRead i B e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,ht,term,hr⟩ := hp
      cases hi : j.context[i]? with
      | none => simp [hi] at hr
      | some Ref =>
        have hrep : bagOperand (expand G Ref) = some B := by simpa [hi] using hr
        have typed := checkTree_sound e ht
        rw [hj,term] at typed
        cases hc
        rw [term]
        simpa [instantiate] using typedRead_sound typed hi hrep he hk hw hh
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
      obtain ⟨hj,_,ht,term,_,hr⟩ := hp
      have typed := checkTree_sound e ht
      rw [hj] at typed
      unfold allocationSlot at term
      split at term
      · rename_i code slot heq
        cases term
        cases hc
        rw [heq] at typed ⊢
        have hs := typed.sound n W h ρ he hw hh
        cases code <;> simpa [instantiate] using alloc_sound hr he hk hs
      · contradiction
    · contradiction
  | written i v R e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,ht,term,hi,_,hr⟩ := hp
      have typed := checkTree_sound e ht
      rw [hj] at typed
      rw [term] at typed
      cases hc
      rw [term]
      simpa [instantiate] using write_sound typed hi hr he hk hw hh
    · contradiction

#print axioms bagOperand_sound
#print axioms alloc_sound
#print axioms creation_sound
#print axioms checkStep_sound
#print axioms typedRead_sound
#print axioms write_sound
#print axioms read_sound
#print axioms value_sound
#print axioms ordinary_sound
end Verification.ExperimentState.HeapExpressionRules
