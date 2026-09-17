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

def copy (k : Knowledge) (i : Nat) : Knowledge :=
  ⟨copyFacts k.cells i,copyFacts k.values i,
    ⟨0,i+1,true,valueField⟩ :: HeapLinks.pull k.links (copySlots i)⟩

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
  ⟨k.cells,⟨0,R,valueField⟩::k.values,k.links⟩

theorem result_holds {k R ρ h v} (hk : HeapKnowledge.Holds k (push v ρ) h)
    (hr : ∃ a ∈ R, v = a.value) : HeapKnowledge.Holds (withResult k R) (push v ρ) h := by
  refine ⟨hk.1,?_,hk.2.2⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hr
  · exact hk.2.1 f hf

/-- An ordinary typed read preserves the heap and records which cell its result
came from. This does not claim the cell had any particular contents beforehand. -/
def readFrame (k : Knowledge) (i : Nat) (fld : String) : Knowledge :=
  let out := HeapKnowledge.shift k
  {out with links := (HeapLinks.aliases k.links i).map (fun j => ⟨j+1,0,false,fld⟩) ++ out.links}

/-- Reading uses a current-cell fact; its result is also an immutable value fact.
This latter fact is what permits a subsequent result-contract check to retain
precision even when the producer supplied a wider expression type. -/
def readOutput (k : Knowledge) (i : Nat) (fld : String) (R : List Literal) : Knowledge :=
  withResult (readFrame k i fld) R

theorem read_sound {G : NormalGraph ι} {Γ k i fld R A ρ n W h}
    (hm : Fact.mk i R fld ∈ k.cells) (hc : includes G A R = true)
    (_he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readOutput k i fld R) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  obtain ⟨flds,c,l,v,hl,hfd,hv,a,ha,rfl⟩ := hk.1 _ hm
  rw [hl]
  apply consequence _ _ (read_observed hw hh hfd (by cases a <;> rfl) hv)
  · intro j U u hu; exact includes_sound hc ⟨a,ha,hu⟩ j U
  · intro h' u hp
    rw [hp.1]
    have hout := result_holds (HeapKnowledge.shift_holds hk) ⟨a,ha,hp.2⟩
    refine ⟨hout.1,hout.2.1,?_⟩
    intro link hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      have he := HeapLinks.aliases_eq hk.2.2 hj
      exact ⟨flds,c,l,he.trans hl,hfd,by simpa [push,hp.2] using hv⟩
    · exact hout.2.2 link hm

/-- A clause's first invariant bag operand, independent of callability. -/
def clauseBagOperand : PositiveNormalization.Clause α → Option (List (String × α))
  | .refs B _ | .callable B _ _ => some B
  | _ => none

/-- Every alternative must promise the same invariant. This includes a neutral
plain/callable view, but excludes empty unions, non-bags, and mixed operands. -/
def bagOperand [DecidableEq α] :
    List (PositiveNormalization.Clause α) → Option (List (String × α))
  | [] => none
  | c :: cs => do
    let B ← clauseBagOperand c
    if cs.all (fun d => decide (clauseBagOperand d = some B)) then some B else none

theorem bagOperand_mem [DecidableEq α] {cs : List (PositiveNormalization.Clause α)} {B c}
    (hr : bagOperand cs = some B) (hm : c ∈ cs) : clauseBagOperand c = some B := by
  cases cs with
  | nil => contradiction
  | cons d ds =>
    simp only [bagOperand] at hr
    cases hd : clauseBagOperand d with
    | none => simp [hd] at hr
    | some D =>
      simp only [hd] at hr
      change (if ds.all (fun d => decide (clauseBagOperand d = some D)) then
        some D else none) = some B at hr
      split at hr
      · rename_i hall
        cases hr
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hd
        · exact of_decide_eq_true (List.all_eq_true.mp hall c hm)
      · contradiction

theorem bagOperand_sound [DecidableEq ι] {G : NormalGraph ι} {Ref B n W v}
    (hr : bagOperand (expand G Ref) = some B) (hv : meaning G Ref n W v) :
    bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v := by
  obtain ⟨c,hm,hc⟩ := (expand_sem G Ref n W v).mp hv
  have hb := bagOperand_mem hr hm
  cases c <;> simp only [clauseBagOperand] at hb
  all_goals try contradiction
  · cases hb; exact recT_bag hc.1
  · cases hb; exact hc.1.1

theorem typedRead_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i fld Ref B El A ρ n W h}
    (ht : HasTy G Γ (.readAt fld (.var i)) A) (hi : Γ[i]? = some Ref)
    (hr : bagOperand (expand G Ref) = some B) (hmem : (fld, El) ∈ B)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readFrame k i fld) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨flds,code,hl,_,hrec⟩ := bagOperand_sound hr (he.2 i Ref hi)
    obtain ⟨flds',l,c,hproj,hfd,hlookup,hagree⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hrec
    cases hproj
    obtain ⟨v,hv,hmm⟩ := hh.2 l c hlookup
    have hval := meaning_valOnly G El 0 _ v ((hagree 0 (by omega) _ v).mp (hmm 0 (by omega)))
    have hs : Safe (meaning G A) (n+1) W h (.readAt fld (ρ i)) := by
      simpa [instantiate] using ht.sound (n+1) W h ρ he hw hh
    rw [hl] at hs ⊢
    apply one_step rfl hval (.readField hfd hv) _ hs
    have hout := HeapKnowledge.shift_holds (v := v) hk
    refine ⟨hout.1,hout.2.1,?_⟩
    intro link hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      exact ⟨flds,code,l,(HeapLinks.aliases_eq hk.2.2 hj).trans hl,hfd,hv⟩
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

/-- Allocation retains facts about old cells and records the fresh object, one
assertion per named field it was given. -/
def allocOutput (k : Knowledge) (Rs : List (String × List Literal)) : Knowledge :=
  ⟨(Rs.map fun p => (⟨0,p.2,p.1⟩ : Fact)) ++ HeapFacts.shift k.cells, HeapFacts.shift k.values,
    (HeapKnowledge.shift k).links⟩

/-- The slots a fresh allocation's initializers stand in, with the field each
one fills. Nothing else can frame facts: every initializer must already be a
value this state knows about. -/
def allocationParts : List String → List Tm → Option (List (String × Nat))
  | [], [] => some []
  | f :: fs, .var i :: as => (allocationParts fs as).map ((f, i) :: ·)
  | _, _ => none

def allocationSlots : Tm → Option (List (String × Nat))
  | .makeAt _ ns inits => allocationParts ns inits
  | _ => none

/-- What each initializer slot is known to hold. An allocation frames facts only
when every one of its fields has a known finite set of values. -/
def allocationFacts [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) :
    List (String × Nat) → Option (List (String × Nat × List Literal))
  | [] => some []
  | (f, i) :: rest =>
    match valuesAt G Γ k i, allocationFacts G Γ k rest with
    | some R, some ps => some ((f, i, R) :: ps)
    | _, _ => none

theorem allocationFacts_eq [DecidableEq ι] {G : NormalGraph ι} {Γ k} :
    ∀ {slots parts}, allocationFacts G Γ k slots = some parts →
      slots = parts.map (fun p => (p.1, p.2.1)) ∧
      ∀ p ∈ parts, valuesAt G Γ k p.2.1 = some p.2.2 := by
  intro slots
  induction slots with
  | nil => intro parts h; simp only [allocationFacts, Option.some.injEq] at h; subst h; simp
  | cons q qs ih =>
    intro parts h
    obtain ⟨f, i⟩ := q
    simp only [allocationFacts] at h
    split at h
    · rename_i R ps hR hps
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := ih hps
      refine ⟨by rw [List.map_cons, ← h1], ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hR
      · exact h2 p hp
    · contradiction

theorem allocationParts_eq : ∀ {ns inits parts}, allocationParts ns inits = some parts →
    ns = parts.map Prod.fst ∧ inits = parts.map fun p => Tm.var p.2 := by
  intro ns
  induction ns with
  | nil => intro inits parts h; cases inits <;> simp_all [allocationParts]
  | cons f fs ih =>
    intro inits parts h
    cases inits with
    | nil => simp [allocationParts] at h
    | cons a as =>
      cases a <;> simp only [allocationParts] at h
      all_goals try simp at h
      rename_i i
      cases hr : allocationParts fs as with
      | none => rw [hr] at h; simp at h
      | some rest =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨a, ha, rfl⟩ := h
        subst ha
        obtain ⟨h1,h2⟩ := ih hr
        subst h1; subst h2
        simp

theorem allocationSlots_eq {t : Tm} {parts : List (String × Nat)}
    (h : allocationSlots t = some parts) :
    ∃ code, t = .makeAt code (parts.map Prod.fst) (parts.map fun p => .var p.2) := by
  unfold allocationSlots at h
  split at h
  · rename_i code ns inits
    obtain ⟨h1,h2⟩ := allocationParts_eq h
    exact ⟨code, by rw [h1, h2]⟩
  · simp at h

theorem alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k A ρ n W h} {code : CallCode}
    {parts : List (String × Nat × List Literal)}
    (hnd : (parts.map Prod.fst).Nodup)
    (hv : ∀ p ∈ parts, valuesAt G Γ k p.2.1 = some p.2.2)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hs : Safe (meaning G A) n W h
      (.makeAt code (parts.map Prod.fst) (parts.map fun p => ρ p.2.1))) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds
        (allocOutput k (parts.map fun p => (p.1, p.2.2))) (push v ρ) h')
      n W h (.makeAt code (parts.map Prod.fst) (parts.map fun p => ρ p.2.1)) := by
  have hval : ∀ p ∈ parts, isVal (ρ p.2.1) = true := by
    intro p hp
    obtain ⟨a,_,hq⟩ := valuesAt_sound (hv p hp) he hk
    rw [hq]; cases a <;> rfl
  have hvals : ∀ v ∈ parts.map (fun p => ρ p.2.1), isVal v = true := by
    intro v hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact hval p hp
  apply one_step rfl rfl (.makeFields hvals (by simp)) _ hs
  have hshift := HeapKnowledge.shift_holds
    (v := Tm.objAt (slots h.length (parts.map Prod.fst)) code) hk
  have hmap : ((parts.map fun p => (p.1, p.2.2)).map fun q => (⟨0,q.2,q.1⟩ : HeapFacts.Fact))
      = parts.map fun p => (⟨0,p.2.2,p.1⟩ : HeapFacts.Fact) := by
    simp [List.map_map, Function.comp_def]
  refine ⟨?_, hshift.2.1, ?_⟩
  · intro f hf
    simp only [allocOutput, hmap] at hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
      obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
      obtain ⟨a,ha,hq⟩ := valuesAt_sound (hv p hp) he hk
      refine ⟨slots h.length (parts.map Prod.fst), code, h.length + i, ρ p.2.1, rfl, ?_, ?_,
        a, ha, hq⟩
      · have hname : (parts.map Prod.fst)[i]'(by simpa using hi) = p.1 := by simp [hpi]
        rw [← hname]
        exact lookup_slots hnd (by simpa using hi)
      · rw [List.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem?_eq_getElem (by simpa using hi)]
        simp [hpi]
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      obtain ⟨flds,c,l,v,hl,hfd,hh',b,hb,hv'⟩ := hk.1 g hg
      exact ⟨flds,c,l,v,hl,hfd,alloc_frames _ hh',b,hb,hv'⟩
  · show HeapLinks.Holds (HeapKnowledge.shift k).links _ _
    exact HeapLinks.alloc_frames (parts.map fun p => ρ p.2.1) hshift.2.2

/-- A write forgets all old cell observations (including aliases), establishes
its new contents, and retains immutable values already read into slots. -/
def writeOutput (k : Knowledge) (i : Nat) (fld : String) (R : List Literal) : Knowledge :=
  ⟨(HeapLinks.aliases k.links i).map (fun j => ⟨j+1,R,fld⟩),
    ⟨0,[.nul],valueField⟩ :: HeapFacts.shift k.values,
    HeapLinks.stable (HeapKnowledge.shift k).links⟩

private theorem write_inv {f h a b h' t} (ha : isVal a = true) (hb : isVal b = true)
    (hs : Step h (.writeAt f a b) h' t) :
    ∃ flds c l, a = .objAt flds c ∧ flds.lookup f = some l ∧ l < h.length ∧
      h' = h.set l b ∧ t = .nul := by
  cases hs with
  | writeC1 hs => exact False.elim (value_no_step ha hs)
  | writeC2 _ hs => exact False.elim (value_no_step hb hs)
  | writeField _ hf hl => exact ⟨_,_,_,rfl,hf,hl,rfl,rfl⟩

/-- The ordinary typing proof guarantees a writable location. An old observation
is unnecessary: the postcondition depends only on the value being written. -/
theorem write_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k i j fld R A ρ n W h}
    (ht : HasTy G Γ (.writeAt fld (.var i) (.var j)) A) (hi : i < Γ.length)
    (hr : valuesAt G Γ k j = some R)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (writeOutput k i fld R) (push v ρ) h')
      n W h (.writeAt fld (ρ i) (ρ j)) := by
  obtain ⟨a,ha,hv⟩ := valuesAt_sound hr he hk
  have hvv : isVal (ρ j) = true := by rw [hv]; cases a <;> rfl
  have hiv := (meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
  have hs : Safe (meaning G A) n W h (.writeAt fld (ρ i) (ρ j)) := by
    simpa [instantiate] using ht.sound n W h ρ he hw hh
  cases n with
  | zero => trivial
  | succ n =>
    have step := hs
    rcases step with ⟨hbad,_⟩ | ⟨U,h',t',_,_,step,_,_⟩
    · contradiction
    · obtain ⟨flds,c,l,hl,hfd,hlt,_,_⟩ := write_inv hiv hvv step
      rw [hl] at hs ⊢
      apply one_step rfl rfl (.writeField hvv hfd hlt) _ hs
      refine ⟨?_,?_,HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := .nul) hk).2.2⟩
      · intro f hf
        obtain ⟨slot,hs,rfl⟩ := List.mem_map.mp hf
        have heq := HeapLinks.aliases_eq hk.2.2 hs
        exact ⟨flds,c,l,ρ j,heq.trans hl,hfd,write_new hlt,a,ha,hv⟩
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
theorem creation_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k arity b A ρ n W h}
    (ht : HasTy G Γ (.make (.closure arity b) .nul) A) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h')
      n W h (instantiate 0 ρ (.make (.closure arity b) .nul)) := by
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
  | typedRead (slot : Nat) (element : List (String × Ty ι)) (proof : ProgramCertificates.Evidence ι)
  | observedRead (slot : Nat) (contents : List Literal)
  | knownValue (slot : Nat) (contents : List Literal)
  /-- The fields, their slots and their contents are read off the term and the
  state, so this carries only the ordinary derivation it stands beside. -/
  | allocated (proof : ProgramCertificates.Evidence ι)
  | written (receiver value : Nat) (contents : List Literal) (proof : ProgramCertificates.Evidence ι)

/-- Only allocation whose initializer is an existing value slot can frame facts.
The descriptor is not evaluated; its code obligations stay in ordinary evidence. -/
def allocationSlot : Tm → Option Nat
  | .make _ (.var i) => some i
  | _ => none

/-- The field an operation names, read off the term rather than supplied by the
producer, so evidence cannot claim a fact about a field the program never
touched. -/
def readSlot : Tm → Option (String × Nat)
  | .readAt f (.var i) => some (f, i)
  | _ => none

def writeSlots : Tm → Option (String × Nat × Nat)
  | .writeAt f (.var i) (.var v) => some (f, i, v)
  | _ => none

theorem readSlot_eq {t f i} (h : readSlot t = some (f, i)) : t = .readAt f (.var i) := by
  unfold readSlot at h
  split at h <;> simp_all

theorem writeSlots_eq {t f i v} (h : writeSlots t = some (f, i, v)) :
    t = .writeAt f (.var i) (.var v) := by
  unfold writeSlots at h
  split at h <;> simp_all

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
      | .make (.closure _ _) .nul => some (HeapKnowledge.shift k)
      | _ => none
    else none
  | .typedRead i B e =>
    match readSlot j.term with
    | some (fld, i') =>
      if claim e = j ∧ checkTree G e = true ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => decide (bagOperand (expand G Ref) = some B)) ∧
          B.any (fun p => p.1 == fld)
      then some (readFrame k i fld) else none
    | none => none
  | .observedRead i R =>
    match readSlot j.term with
    | some (fld, i') =>
      if i' = i ∧ i < j.context.length ∧
          Fact.mk i R fld ∈ k.cells ∧ includes G j.type R = true
      then some (readOutput k i fld R) else none
    | none => none
  | .knownValue i R =>
    if j.term = .var i ∧ i < j.context.length ∧
        valuesAt G j.context k i = some R ∧ includes G j.type R = true
    then some (withResult (copy k i) R) else none
  | .allocated e =>
    match allocationSlots j.term with
    | some slots =>
      match allocationFacts G j.context k slots with
      | some parts =>
        if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTree G e = true ∧
            (parts.map Prod.fst).Nodup
        then some (allocOutput k (parts.map fun p => (p.1, p.2.2))) else none
      | none => none
    | none => none
  | .written i v R e =>
    match writeSlots j.term with
    | some (fld, i', v') =>
      if claim e = j ∧ checkTree G e = true ∧ i' = i ∧ v' = v ∧
          i < j.context.length ∧ v < j.context.length ∧
          valuesAt G j.context k v = some R
      then some (writeOutput k i fld R) else none
    | none => none

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
      · rename_i arity b hb
        cases hc
        rw [hb] at typed ⊢
        exact creation_sound typed he hk hw hh
      · contradiction
    · contradiction
  | typedRead i B e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i fld i' hslot
      split at hc
      · rename_i hp
        obtain ⟨hj,ht,rfl,hr,hfld⟩ := hp
        have term := readSlot_eq hslot
        cases hi : j.context[i']? with
        | none => simp [hi] at hr
        | some Ref =>
          have hrep : bagOperand (expand G Ref) = some B := by simpa [hi] using hr
          obtain ⟨q,hq,hq1⟩ := List.any_eq_true.mp hfld
          have hqeq : q.1 = fld := by simpa using hq1
          have typed := checkTree_sound e ht
          rw [hj,term] at typed
          cases hc
          rw [term]
          simpa [instantiate] using
            typedRead_sound (El := q.2) typed hi hrep (by rw [← hqeq]; simpa using hq) he hk hw hh
      · contradiction
    · contradiction
  | observedRead i R =>
    simp only [checkStep] at hc
    split at hc
    · rename_i fld i' hslot
      split at hc
      · rename_i hp
        obtain ⟨rfl,_,hm,hi⟩ := hp
        have term := readSlot_eq hslot
        cases hc
        rw [term]
        simpa [instantiate] using read_sound hm hi he hk hw hh
      · contradiction
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
  | allocated e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i slots hslots
      split at hc
      · rename_i parts hparts
        split at hc
        · rename_i hp
          obtain ⟨hj,_,ht,hnd⟩ := hp
          have typed := checkTree_sound e ht
          rw [hj] at typed
          obtain ⟨code, term⟩ := allocationSlots_eq hslots
          obtain ⟨hslot, hvals⟩ := allocationFacts_eq hparts
          have hterm : j.term = .makeAt code (parts.map Prod.fst)
              (parts.map fun p => Tm.var p.2.1) := by
            rw [term, hslot]
            simp [List.map_map, Function.comp_def]
          cases hc
          rw [hterm] at typed ⊢
          have hs := typed.sound n W h ρ he hw hh
          cases code
          all_goals
            simp only [instantiate, instantiateArgs_eq_map, List.map_map,
              Function.comp_def] at hs ⊢
          all_goals
            exact alloc_sound (parts := parts)
              (by simpa [List.map_map, Function.comp_def] using hnd) hvals he hk hs
        · contradiction
      · contradiction
    · contradiction
  | written i v R e =>
    simp only [checkStep] at hc
    split at hc
    · rename_i fld i' v' hslots
      split at hc
      · rename_i hp
        obtain ⟨hj,ht,rfl,rfl,hi,_,hr⟩ := hp
        have term := writeSlots_eq hslots
        have typed := checkTree_sound e ht
        rw [hj] at typed
        rw [term] at typed
        cases hc
        rw [term]
        simpa [instantiate] using write_sound typed hi hr he hk hw hh
      · contradiction
    · contradiction

#print axioms bagOperand_mem
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
