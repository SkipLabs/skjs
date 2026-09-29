import Verification.Model.Semantics.Purity
import Verification.Model.Semantics.HeapKnowledge

/-! Checked expression rules with primitive state postconditions. Ordinary evidence
retains only immutable-value facts; special rules justify stronger heap facts.
No fact is accepted as an ordinary reference type or captured as a permanent call contract. -/
namespace Verification.Model.HeapExpressionRules
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower
open HeapFacts HeapKnowledge HeapObservations ProgramCertificates
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

/-- Copy an immutable slot into the result while preserving the old slots. -/
def copyFacts (fs : Facts) (i : Nat) : Facts :=
  (fs.filter (fun f => f.slot == i)).map (fun f => {f with slot := 0}) ++ HeapFacts.shift fs

def copySlots (i j : Nat) : List Nat := if j = i then [0,j+1] else [j+1]

def copy (k : Knowledge) (i : Nat) : Knowledge :=
  ⟨copyFacts k.cells i,copyFacts k.values i,
    ⟨0,i+1,true,valueField,false,valueField,false⟩ :: HeapLinks.pull k.links (copySlots i)⟩

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
def valuesAt (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) (i : Nat) : Option (List Atom) :=
  match k.values.find? (fun f => f.slot == i) with
  | some f => some f.contents
  | none => (Γ[i]?).bind fun B => (HeapKnowledge.atoms G B).orElse fun _ =>
      -- A type no member of which is `undefined`: some value other than it.
      if G.plainTy B && (expand G B).all (fun c => tagClause .isUndef c == some false)
      then some [.defined] else none

theorem valuesAt_sound {G : NormalGraph ι} {Γ k i R ρ n W h}
    (hr : valuesAt G Γ k i = some R) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) : ∃ a ∈ R, a.holds (ρ i) := by
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
      cases ha : HeapKnowledge.atoms G B with
      | some S =>
        rw [ha] at hr
        cases hr
        exact (atoms_sem ha n W (ρ i)).mp (he.2 i B hb)
      | none =>
        rw [ha] at hr
        simp only [Option.orElse_none] at hr
        split at hr
        · rename_i hq
          cases hr
          have hq : Answers G B .isUndef false := by
            simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hq
            exact ⟨hq.1, hq.2⟩
          have hv := he.2 i B hb
          refine ⟨.defined, by simp, (meaning_value hv).1, fun hu => ?_⟩
          have := answers_sound hq hv
          rw [hu] at this
          simp [tagHolds] at this
        · cases hr

/-- A primitive type's predicate is a structural view, not semantic search. -/
def includes (G : NormalGraph ι) (A : Ty ι) (R : List Atom) : Bool :=
  match atoms G A with
  | some S => covers R S
  | none => false

theorem includes_sound {G : NormalGraph ι} {A R v} (hc : includes G A R = true)
    (hv : ∃ a ∈ R, a.holds v) (n W) : meaning G A n W v := by
  unfold includes at hc
  split at hc
  · rename_i S hs
    obtain ⟨a,ha,he⟩ := hv
    apply (atoms_sem hs n W v).mpr
    exact covers_sound hc ⟨a,ha,he⟩
  · contradiction

def withResult (k : Knowledge) (R : List Atom) : Knowledge :=
  ⟨k.cells,⟨0,R,valueField⟩::k.values,k.links⟩

theorem result_holds {k R ρ h v} (hk : HeapKnowledge.Holds k (push v ρ) h)
    (hr : ∃ a ∈ R, a.holds v) : HeapKnowledge.Holds (withResult k R) (push v ρ) h := by
  refine ⟨hk.1,?_,hk.2.2⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hr
  · exact hk.2.1 f hf

/-- An ordinary typed read preserves the heap and records which cell its result
came from. This does not claim the cell had any particular contents beforehand. -/
def readFrame (k : Knowledge) (i : Nat) (fld : PropKey) (optional : Bool := false) : Knowledge :=
  let out := HeapKnowledge.shift k
  let fresh := (HeapLinks.aliases k.links i).map fun j => (⟨j+1,0,false,fld,false,valueField,optional⟩ : HeapLinks.Link)
  {out with links := fresh ++ out.links}

/-- Reading uses a current-cell fact; its result is also an immutable value fact.
This latter fact is what permits a subsequent result-contract check to retain
precision even when the producer supplied a wider expression type. -/
def readOutput (k : Knowledge) (i : Nat) (fld : PropKey) (R : List Atom) : Knowledge :=
  withResult (readFrame k i fld) R

theorem read_sound {G : NormalGraph ι} {Γ k i fld R A ρ n W h}
    (hm : Fact.mk i R fld ∈ k.cells) (hc : includes G A R = true)
    (_he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readOutput k i fld R) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  obtain ⟨flds,c,l,v,hl,hfd,hv,a,ha,hav⟩ := hk.1 _ hm
  rw [hl]
  apply consequence _ _ (read_observed hw hh hfd (Atom.isValue hav) hv)
  · intro j U u hu; subst u; exact includes_sound hc ⟨a,ha,hav⟩ j U
  · intro h' u hp
    rw [hp.1]
    have hout := result_holds (HeapKnowledge.shift_holds (v := u) hk) ⟨a,ha,by simpa [hp.2] using hav⟩
    refine ⟨hout.1,hout.2.1,?_⟩
    intro link hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
      have he := HeapLinks.aliases_eq hk.2.2 hj
      exact ⟨flds,c,l,he.trans hl,hfd,by simpa [push,hp.2] using hv⟩
    · exact hout.2.2 link hm

/-- A clause's first invariant bag operand, independent of callability. -/
def clauseBagOperand : PositiveNormalization.Clause α → Option (List (PropKey × α))
  | .refs B _ _ _ _ _ | .callable B _ _ _ => some B
  | _ => none

/-- Every alternative must promise the same invariant. This includes a neutral
plain/callable view, but excludes empty unions, non-bags, and mixed operands. -/
def bagOperand [DecidableEq α] :
    List (PositiveNormalization.Clause α) → Option (List (PropKey × α))
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
  have hp : G.plainTy Ref = true := by
    cases he : expand G Ref with
    | nil => rw [he] at hr; contradiction
    | cons c _ => exact plain_of_mem_expand (c := c) (by simp [he])
  obtain ⟨c,hm,hc,-⟩ := (expand_sem G Ref hp n W v).mp hv
  have hb := bagOperand_mem hr hm
  cases c <;> simp only [clauseBagOperand] at hb
  all_goals try contradiction
  · cases hb; exact recT_bag hc.1.1
  · cases hb; exact hc.1.1.1

/-- Whether every alternative is a record whose first invariant operand has
the field `fld`, whatever its type in each: a read of it is then of a
location of the object. -/
def fieldOperand (cs : List (PositiveNormalization.Clause α)) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => match clauseBagOperand c with
    | some B => B.any fun p => decide (p.1 = fld)
    | none => false

theorem fieldOperand_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : fieldOperand (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ B El, (fld, El) ∈ B ∧ bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v := by
  simp only [fieldOperand, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hr.1
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c,hm,hc,-⟩ := (expand_sem G Ref hp n W v).mp hv
  have hb := hr.2 c hm
  cases c <;> simp only [clauseBagOperand] at hb
  all_goals try contradiction
  all_goals
    obtain ⟨⟨g, El⟩, hmem, hg⟩ := List.any_eq_true.mp hb
    simp only [decide_eq_true_eq] at hg
    subst hg
  · exact ⟨_, El, hmem, recT_bag hc.1.1⟩
  · exact ⟨_, El, hmem, hc.1.1.1⟩

theorem typedRead_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k i fld Ref A ρ n W h}
    (ht : HasTyUsing G images Γ (.readAt fld (.var i)) A) (hi : Γ[i]? = some Ref)
    (hr : fieldOperand (expand G Ref) fld = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readFrame k i fld) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨B,El,hmem,hbag⟩ := fieldOperand_sound hr (he.2 i Ref hi)
    obtain ⟨flds,code,hl,_,hrec⟩ := hbag
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

/-- A value that is no `undefined` answers the test for it `false`. -/
theorem tagHolds_isUndef_false {v : Tm} (hne : v ≠ .undef) : tagHolds .isUndef v = false := by
  cases v <;> simp_all [tagHolds]

/-- A value of a type that is no `undefined` is of the type's slice without
it, at every step count: what a finished read returns. -/
theorem slice_value {G : NormalGraph ι} {C : Ty ι} {Q : Post} {n W h v}
    (hs : SafePost (meaning G C) Q n W h v) (hv : isVal v = true) (hne : v ≠ .undef) :
    SafePost (meaning G (BranchRefinement.tagSlice G C .isUndef false)) Q n W h v := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hv',ht,hq⟩ | hth) | ⟨_,_,_,_,_,step,_,_⟩
    · exact Or.inl (Or.inl ⟨hv',BranchRefinement.tagSlice_sound ht (Or.inl (tagHolds_isUndef_false hne)),hq⟩)
    · exact absurd hth (val_not_thrown hv)
    · exact False.elim (value_no_step hv step)

/-- A read of a location a fact says holds no `undefined`, typed at its
contract `C` by the ordinary rule: its result is of `C` less `undefined`.
The fact is about the location the read finds, so the value it returns is
one the fact describes. -/
theorem slicedRead_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k i fld Ref C R ρ n W h}
    (ht : HasTyUsing G images Γ (.readAt fld (.var i)) C) (hi : Γ[i]? = some Ref)
    (hr : fieldOperand (expand G Ref) fld = true)
    (hm : Fact.mk i R fld ∈ k.cells) (hR : R.all (· != .undef) = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G (BranchRefinement.tagSlice G C .isUndef false))
      (fun h' v => HeapKnowledge.Holds (readFrame k i fld) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  have base := typedRead_sound ht hi hr he hk hw hh
  obtain ⟨flds,c,l,v,hl,hfd,hv,a,ha,hav⟩ := hk.1 _ hm
  have hne : v ≠ .undef := by
    intro hu
    subst hu
    have hau := HeapKnowledge.holds_undef hav
    subst hau
    have := List.all_eq_true.mp hR _ ha
    simp at this
  have hvv : isVal v = true := Atom.isValue hav
  have step : Step h (.readAt fld (ρ i)) h v := by rw [hl]; exact .readField hfd hv
  cases n with
  | zero => trivial
  | succ n =>
    rcases base with (⟨hval,_,_⟩ | hth) | ⟨U,h',t',hx,hu,step',hh',hs'⟩
    · rw [hl] at hval; simp [isVal] at hval
    · exact absurd step hth.no_step
    · obtain ⟨rfl,rfl⟩ := Step_det step' step
      exact Or.inr ⟨U,h',t',hx,hu,step',hh',slice_value hs' hvv hne⟩

/-- Whether every alternative is a plain record naming the field `fld`,
required or optional: a read of it is then of a location of the object, or,
where an optional key is absent, `undefined`, since such an object has no
prototype. -/
def optionalOperand (cs : List (PositiveNormalization.Clause α)) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => match c with
    | .refs a _ _ os _ _ => a.any (fun p => decide (p.1 = fld)) || os.any (fun o => decide (o.key = fld))
    | _ => false

/-- What such a read finds: the object, and, where it has the key, a
location whose contract admits only values, or else no prototype. -/
theorem optionalOperand_sound [DecidableEq ι] {G : NormalGraph ι} {Ref fld n W v}
    (hr : optionalOperand (expand G Ref) fld = true) (hv : meaning G Ref (n+1) W v) :
    ∃ flds, v = .objAt flds .absent ∧
      (∀ l, flds.lookup fld = some l → ∃ c : Ctr (n+1), lookup W l = some c ∧
        ∀ (W' : WorldT 0) (u : Val), c 0 (by omega) W' u → isVal u = true) ∧
      (flds.lookup fld = none → flds.lookup CallArguments.protoField = none) := by
  simp only [optionalOperand, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hr.1
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c,hm,hc,-⟩ := (expand_sem G Ref hp (n+1) W v).mp hv
  have hb := hr.2 c hm
  cases c with
  | refs a bs vs os ms ks =>
    simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨flds, hvf, hrec⟩, _⟩ := hc.1
    subst hvf
    refine ⟨flds, rfl, ?_, ?_⟩
    · intro l hl
      rcases hb with ⟨⟨g, El⟩, hmem, rfl⟩ | ⟨o, hmem, rfl⟩
      · obtain ⟨l', c', hl', hw, hag⟩ := hrec g (meaning G El)
          (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩)
        rw [hl] at hl'
        cases hl'
        exact ⟨c', hw, fun W' u hu => meaning_valOnly G El 0 W' u ((hag 0 (by omega) W' u).mp hu)⟩
      · obtain ⟨c', hw, hsc⟩ := optT_present (List.mem_map.mpr ⟨o, hmem, rfl⟩) hc.2.2.1 hl
        exact ⟨c', hw, fun W' u hu => meaning_valOnly G o.type 0 W' u ((hsc 0 (by omega) W' u).1 hu)⟩
    · intro hl
      rcases hb with ⟨⟨g, El⟩, hmem, rfl⟩ | ⟨o, hmem, rfl⟩
      · obtain ⟨l', c', hl', _⟩ := hrec g (meaning G El)
          (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩)
        rw [hl] at hl'
        cases hl'
      · exact optT_no_proto (List.mem_map.mpr ⟨o, hmem, rfl⟩) hc.2.2.1 hl
  | _ => simp at hb

/-- A read of a field that may be optional: it records a read link that also
covers the absent key, where it gave `undefined`. -/
theorem optionalRead_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k i fld Ref A ρ n W h}
    (ht : HasTyUsing G images Γ (.readAt fld (.var i)) A) (hi : Γ[i]? = some Ref)
    (hr : optionalOperand (expand G Ref) fld = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (readFrame k i fld true) (push v ρ) h') n W h
      (.readAt fld (ρ i)) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨flds, hl, hpres, habs⟩ := optionalOperand_sound hr (he.2 i Ref hi)
    have hs : Safe (meaning G A) (n+1) W h (.readAt fld (ρ i)) := by
      simpa [instantiate] using ht.sound (n+1) W h ρ he hw hh
    rw [hl] at hs ⊢
    have out : ∀ u, HeapLinks.ReadGave flds fld h u →
        HeapKnowledge.Holds (readFrame k i fld true) (push u ρ) h := by
      intro u hu
      have hout := HeapKnowledge.shift_holds (v := u) hk
      refine ⟨hout.1,hout.2.1,?_⟩
      intro link hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
        simp only [Bool.false_eq_true, ite_false, ite_true]
        exact ⟨flds, .absent, (HeapLinks.aliases_eq hk.2.2 hj).trans hl, hu⟩
      · exact hout.2.2 link hm
    cases hlk : flds.lookup fld with
    | some l =>
      obtain ⟨c, hc, hvals⟩ := hpres l hlk
      obtain ⟨u,hu,hmm⟩ := hh.2 l c hc
      have hval := hvals _ u (hmm 0 (by omega))
      apply one_step rfl hval (.readField hlk hu) _ hs
      exact out u (by simp [HeapLinks.ReadGave, hlk, hu])
    | none =>
      apply one_step rfl rfl (.readMissing hlk (habs hlk)) _ hs
      exact out .undef (by simp [HeapLinks.ReadGave, hlk])

theorem value_sound {G : NormalGraph ι} {Γ k i R A ρ n W h}
    (hr : valuesAt G Γ k i = some R) (hc : includes G A R = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (withResult (copy k i) R) (push v ρ) h') n W h (ρ i) := by
  have hv := valuesAt_sound hr he hk
  have hval : isVal (ρ i) = true := by
    obtain ⟨a,_,ha⟩ := hv; exact Atom.isValue ha
  exact HeapObservations.value hval (includes_sound hc hv n W)
    (result_holds (copy_holds hk) hv)

/-- Ordinary calls and arbitrary expressions retain immutable snapshots, but no
heap observation without a specific proved effect rule. -/
def ordinaryOutput (k : Knowledge) : Knowledge := ⟨[],HeapFacts.shift k.values,HeapLinks.stable (HeapKnowledge.shift k).links⟩

theorem ordinary_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k t A ρ n W h}
    (ht : HasTyUsing G images Γ t A) (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (ordinaryOutput k) (push v ρ) h') n W h (instantiate 0 ρ t) := by
  apply of_value_property _ (ht.sound n W h ρ he hw hh)
  intro _ _ heap v _
  exact ⟨holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2.1,HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2⟩

/-- The named fields of every record-typed slot: the locations a fresh
allocation is known to differ from, read off the context's contracts. A slot
of a union of records has the fields every one of them names. -/
def contractFields [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) : List (Nat × PropKey) :=
  Γ.zipIdx.flatMap fun (A, s) => match (expand G A).head? >>= clauseBagOperand with
    | some B => (B.map Prod.fst).eraseDups.filterMap fun f =>
        if fieldOperand (expand G A) f then some (s, f) else none
    | none => []

theorem contractFields_mem [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {s f}
    (hm : (s, f) ∈ contractFields G Γ) :
    ∃ Ref, Γ[s]? = some Ref ∧ fieldOperand (expand G Ref) f = true := by
  obtain ⟨⟨A,s'⟩,hA,hsel⟩ := List.mem_flatMap.mp hm
  simp only at hsel
  split at hsel
  · obtain ⟨g,_,hg⟩ := List.mem_filterMap.mp hsel
    split at hg
    · rename_i hf
      cases hg
      exact ⟨A, List.mem_zipIdx_iff_getElem?.mp hA, hf⟩
    · cases hg
  · simp at hsel

/-- Allocation retains facts about old cells and records the fresh object: one
assertion per field whose initializer is known to hold a supported primitive
predicate (`Rs`). Its locations are fresh, so each of its fields (`fields`, by
default those of `Rs`) is distinct from every contract field of every
record-typed slot, whatever it holds. -/
def allocOutput (k : Knowledge) (Rs : List (PropKey × List Atom))
    (others : List (Nat × PropKey) := []) (fields : List PropKey := Rs.map Prod.fst) : Knowledge :=
  ⟨(Rs.map fun p => (⟨0,p.2,p.1⟩ : Fact)) ++ HeapFacts.shift k.cells, HeapFacts.shift k.values,
    (fields.flatMap fun p => others.map fun q =>
      (⟨0,q.1+1,false,p,true,q.2,false⟩ : HeapLinks.Link)) ++ (HeapKnowledge.shift k).links⟩

/-- The slots a fresh allocation's initializers stand in, with the field each
one fills. Nothing else can frame facts: every initializer must already be a
value this state knows about. -/
def allocationParts : List PropKey → List Tm → Option (List (PropKey × Nat))
  | [], [] => some []
  | f :: fs, .var i :: as => (allocationParts fs as).map ((f, i) :: ·)
  | _, _ => none

def allocationSlots : Tm → Option (List (PropKey × Nat))
  | .makeAt _ ns inits => allocationParts ns inits
  | _ => none

/-- What the initializers are known to hold, field by field, where that is a
supported primitive predicate; a field whose initializer is not has no fact. -/
def allocationFacts (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge)
    (slots : List (PropKey × Nat)) : List (PropKey × List Atom) :=
  slots.filterMap fun p => (valuesAt G Γ k p.2).map (p.1, ·)

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

theorem allocationSlots_eq {t : Tm} {parts : List (PropKey × Nat)}
    (h : allocationSlots t = some parts) :
    ∃ code, t = .makeAt code (parts.map Prod.fst) (parts.map fun p => .var p.2) := by
  unfold allocationSlots at h
  split at h
  · rename_i code ns inits
    obtain ⟨h1,h2⟩ := allocationParts_eq h
    exact ⟨code, by rw [h1, h2]⟩
  · simp at h

theorem alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k A ρ n W h} {code : CallCode}
    {parts : List (PropKey × Nat)}
    (hnd : (parts.map Prod.fst).Nodup)
    (hin : ∀ p ∈ parts, p.2 < Γ.length)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (hs : Safe (meaning G A) n W h
      (.makeAt code (parts.map Prod.fst) (parts.map fun p => ρ p.2))) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds
        (allocOutput k (allocationFacts G Γ k parts) (contractFields G Γ) (parts.map Prod.fst))
        (push v ρ) h')
      n W h (.makeAt code (parts.map Prod.fst) (parts.map fun p => ρ p.2)) := by
  have hval : ∀ p ∈ parts, isVal (ρ p.2) = true := fun p hp =>
    (meaning_value (he.2 p.2 _ (List.getElem?_eq_getElem (hin p hp)))).1
  have hvals : ∀ v ∈ parts.map (fun p => ρ p.2), isVal v = true := by
    intro v hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact hval p hp
  apply one_step rfl rfl (.makeFields hvals (by simp)) _ hs
  have hshift := HeapKnowledge.shift_holds
    (v := Tm.objAt (slots h.length (parts.map Prod.fst)) code) hk
  refine ⟨?_, hshift.2.1, ?_⟩
  · intro f hf
    simp only [allocOutput] at hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf
      obtain ⟨p,hp,hpq⟩ := List.mem_filterMap.mp hq
      obtain ⟨R,hR,rfl⟩ := Option.map_eq_some_iff.mp hpq
      obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
      obtain ⟨a,ha,hq⟩ := valuesAt_sound hR he hk
      refine ⟨slots h.length (parts.map Prod.fst), code, h.length + i, ρ p.2, rfl, ?_, ?_,
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
  · intro g hg
    simp only [allocOutput] at hg
    rcases List.mem_append.mp hg with hg | hg
    · -- A fresh field sits at or beyond the old heap's end; a contract field of
      -- an existing object holds a heap value, so it sits below it.
      obtain ⟨fld,hfld,hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hfld
      obtain ⟨Ref,hidx,hfo⟩ := contractFields_mem hq
      obtain ⟨B,El,hmem,hbag⟩ := fieldOperand_sound hfo (he.2 q.1 Ref hidx)
      obtain ⟨flds0,code0,hl0,_,hrec⟩ := hbag
      obtain ⟨flds1,l1,c1,hproj,hfd1,hlookup,_⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hrec
      obtain ⟨u,hu,_⟩ := hh.2 l1 c1 hlookup
      have hlt : l1 < h.length := List.getElem?_eq_some_iff.mp hu |>.1
      simp only [ite_true]
      intro flds c l flds' c' l' h0 hfl hs' hfl'
      simp only [push] at h0 hs'
      cases h0
      have hsl : (slots h.length (parts.map Prod.fst)).lookup fld = some (h.length + i) := by
        rw [← hpi]; exact lookup_slots hnd hi
      have hleq : l = h.length + i := Option.some.inj (hfl.symm.trans hsl)
      rw [hl0] at hs'
      cases hs'
      cases hproj
      have hl'eq : l' = l1 := Option.some.inj (hfl'.symm.trans hfd1)
      omega
    · exact HeapLinks.alloc_frames (parts.map fun p => ρ p.2) hshift.2.2 g hg

theorem slots_lookup_ge {base : Nat} {ns : List PropKey} {f : PropKey} {l : Nat}
    (h : (slots base ns).lookup f = some l) : base ≤ l := by
  induction ns generalizing base with
  | nil => simp [slots, List.lookup] at h
  | cons g ns ih =>
    simp only [slots, List.lookup] at h
    split at h
    · cases h; exact Nat.le_refl _
    · have := ih h; omega

/-- An object allocated past the heap's end keeps what was known of the old
heap, and each of its fields, whichever keys it has, is distinct from every
contract field of the context's record-typed slots. -/
theorem fresh_holds [DecidableEq ι] {G : NormalGraph ι} {Γ k ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (ns : List PropKey) (vs : List Val) (code : CallCode) (fields : List PropKey) :
    HeapKnowledge.Holds (allocOutput k [] (contractFields G Γ) fields)
      (push (.objAt (slots h.length ns) code) ρ) (h ++ vs) := by
  have hshift := HeapKnowledge.shift_holds (v := Tm.objAt (slots h.length ns) code) hk
  refine ⟨?_, hshift.2.1, ?_⟩
  · intro f hf
    simp only [allocOutput, List.map_nil, List.nil_append] at hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    obtain ⟨flds,c,l,v,hl,hfd,hh',b,hb,hv'⟩ := hk.1 g hg
    exact ⟨flds,c,l,v,hl,hfd,alloc_frames _ hh',b,hb,hv'⟩
  · intro g hg
    simp only [allocOutput] at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨fld,_,hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      obtain ⟨Ref,hidx,hfo⟩ := contractFields_mem hq
      obtain ⟨B,El,hmem,hbag⟩ := fieldOperand_sound hfo (he.2 q.1 Ref hidx)
      obtain ⟨flds0,code0,hl0,_,hrec⟩ := hbag
      obtain ⟨flds1,l1,c1,hproj,hfd1,hlookup,_⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨El, hmem, rfl⟩) hrec
      obtain ⟨u,hu,_⟩ := hh.2 l1 c1 hlookup
      have hlt : l1 < h.length := List.getElem?_eq_some_iff.mp hu |>.1
      simp only [ite_true]
      intro flds c l flds' c' l' h0 hfl hs' hfl'
      simp only [push] at h0 hs'
      cases h0
      have hge : h.length ≤ l := slots_lookup_ge hfl
      rw [hl0] at hs'
      cases hs'
      cases hproj
      have hl'eq : l' = l1 := Option.some.inj (hfl'.symm.trans hfd1)
      omega
    · exact HeapLinks.alloc_frames vs hshift.2.2 g hg

/-- A merge of two values reads the heap and allocates a fresh object: what
was known of the heap stays known, and the new object's fields are distinct
from the context's contract fields, as a literal's are (`alloc_sound`). -/
theorem merge_alloc_sound [DecidableEq ι] {G : NormalGraph ι} {Γ k A ρ n W h}
    {d : List PropKey} {a b : Tm} (fields : List PropKey)
    (hva : isVal a = true) (hvb : isVal b = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hh : HeapOk n W h)
    (hs : Safe (meaning G A) n W h (.merge d a b)) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (allocOutput k [] (contractFields G Γ) fields) (push v ρ) h')
      n W h (.merge d a b) := by
  cases n with
  | zero => trivial
  | succ p =>
    rcases hs with (⟨hval,_⟩ | hr) | ⟨U,h1,t1,hx,hu,step,hh1,hs1⟩
    · simp [isVal] at hval
    · obtain ⟨v, hr, _⟩ := hr
      cases hr with
      | mergeC1 hr => rw [raises_not_val hr] at hva; contradiction
      | mergeC2 _ hr => rw [raises_not_val hr] at hvb; contradiction
    · cases step with
      | mergeC1 s => exact absurd s (value_no_step hva)
      | mergeC2 _ s => exact absurd s (value_no_step hvb)
      | mergeV _ _ hparts =>
        refine Or.inr ⟨U, h, _, hx, hu, .mergeV hva hvb hparts, hh1, ?_⟩
        refine one_step rfl rfl (.makeFields ?vals (by simp)) (fresh_holds he hk hh _ _ _ fields) hs1
        case vals =>
          intro v hv
          obtain ⟨e, hm, rfl⟩ := List.mem_map.mp hv
          rcases mergeParts_vals hparts e hm with h1 | ⟨-, h2⟩
          · rw [h1]; rfl
          · exact h2

/-- A write forgets old cell observations, except those about locations known
to be distinct from the written one, establishes its new contents where the
written value is a known primitive (`R`), and retains immutable values
already read into slots. -/
def writeOutput (k : Knowledge) (i : Nat) (fld : PropKey) (R : Option (List Atom)) : Knowledge :=
  ⟨(R.map fun R => (HeapLinks.aliases k.links i).map (fun j => (⟨j+1,R,fld⟩ : Fact))).getD [] ++
      (k.cells.filter fun f => (f.slot,f.field) ∈ HeapLinks.distinctFrom k.links i fld).map
        (fun f => {f with slot := f.slot + 1}),
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
theorem write_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k i j fld R A ρ n W h}
    (ht : HasTyUsing G images Γ (.writeAt fld (.var i) (.var j)) A) (hi : i < Γ.length) (hj : j < Γ.length)
    (hr : valuesAt G Γ k j = R)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (writeOutput k i fld R) (push v ρ) h')
      n W h (.writeAt fld (ρ i) (ρ j)) := by
  have hvv : isVal (ρ j) = true :=
    (meaning_value (he.2 j Γ[j] (List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩))).1
  have hiv := (meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
  have hs : Safe (meaning G A) n W h (.writeAt fld (ρ i) (ρ j)) := by
    simpa [instantiate] using ht.sound n W h ρ he hw hh
  cases n with
  | zero => trivial
  | succ n =>
    have step := hs
    rcases step with (⟨hbad,_⟩ | ⟨_,hr,_⟩) | ⟨U,h',t',_,_,step,_,_⟩
    · contradiction
    · cases hr with
      | writeC1 hr => rw [raises_not_val hr] at hiv; contradiction
      | writeC2 _ hr => rw [raises_not_val hr] at hvv; contradiction
    · obtain ⟨flds,c,l,hl,hfd,hlt,_,_⟩ := write_inv hiv hvv step
      rw [hl] at hs ⊢
      apply one_step rfl rfl (.writeField hvv hfd hlt) _ hs
      refine ⟨?_,?_,HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := .nul) hk).2.2⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · cases hR : R with
          | none => simp [hR] at hf
          | some R' =>
            rw [hR] at hf
            obtain ⟨a,ha,hv⟩ := valuesAt_sound (hR ▸ hr) he hk
            obtain ⟨slot,hs,rfl⟩ := List.mem_map.mp (by simpa using hf)
            have heq := HeapLinks.aliases_eq hk.2.2 hs
            exact ⟨flds,c,l,ρ j,heq.trans hl,hfd,write_new hlt,a,ha,hv⟩
        · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
          have hg := List.mem_filter.mp hg
          obtain ⟨flds0,c0,l0,u,hs0,hfd0,hu,b,hb,hb'⟩ := hk.1 g hg.1
          have hne : l ≠ l0 := HeapLinks.distinct_sound hk.2.2 (of_decide_eq_true hg.2) hl hfd hs0 hfd0
          refine ⟨flds0,c0,l0,u,?_,hfd0,?_,b,hb,hb'⟩
          · simpa [push] using hs0
          · rw [List.getElem?_set_ne hne]; exact hu
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨.nul,by simp,rfl⟩
        · exact (HeapKnowledge.shift_holds (v := .nul) hk).2.1 f hf

export Purity (pureTerm pure_step)

theorem pure_instantiate {G : NormalGraph ι} {Γ t ρ n W} {d : Nat}
    (hp : pureTerm t = true) (hc : checkScope (Γ.length + d) t = true)
    (he : EnvOk G Γ ρ n W) : pureTerm (instantiate d ρ t) = true := by
  induction t using Tm.induct generalizing d <;>
    simp_all [pureTerm,isVal,instantiate,checkScope,Nat.add_assoc]
  case var i =>
    split
    · rfl
    · have hi : i - d < Γ.length := by omega
      have hv := (meaning_value (he.2 (i-d) Γ[i-d] (List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩))).1
      cases h : ρ (i-d) <;> simp_all [pureTerm,isVal]

/-- Any heap predicate can be framed across a checked pure computation. -/
theorem pure_frame {T Q} : ∀ {n W h t}, Safe T n W h t → pureTerm t = true →
    (∀ v, Q h v) → SafePost T Q n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs hp hq
    rcases hs with (⟨hv,ht⟩ | hr) | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl (Or.inl ⟨hv,ht,hq t⟩)
    · exact Or.inl (Or.inr hr)
    · obtain ⟨rfl,hp'⟩ := pure_step step hp
      exact Or.inr ⟨U,_,t',hx,hu,step,hh,ih hs hp' hq⟩

def pureOutput (k : Knowledge) : Tm → Knowledge
  | .var i => copy k i
  | .nul => withResult (HeapKnowledge.shift k) [.nul]
  | .undef => withResult (HeapKnowledge.shift k) [.undef]
  | .tru => withResult (HeapKnowledge.shift k) [.tru]
  | .fls => withResult (HeapKnowledge.shift k) [.fls]
  | _ => HeapKnowledge.shift k

theorem pure_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ k t A ρ n W h}
    (ht : HasTyUsing G images Γ t A) (hp : pureTerm t = true)
    (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (pureOutput k t) (push v ρ) h')
      n W h (instantiate 0 ρ t) := by
  have hs := ht.sound n W h ρ he hw hh
  have hpClosed := pure_instantiate (d := 0) hp hc he
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

/-- Creating graph code allocates a fresh bag without running its code or
invalidating knowledge about existing cells: its captures are slots, already
values. -/
theorem graphCreation_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ k arity E K start caps kind rest A ρ n W h}
    (ht : HasTyUsing G images Γ (.makeFn (.graph arity E K start caps kind rest) .nul) A) (he : EnvOk G Γ ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h')
      n W h (instantiate 0 ρ (.makeFn (.graph arity E K start caps kind rest) .nul)) := by
  have hs := ht.sound n W h ρ he hw hh
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hv, _⟩ | ⟨_,hr,_⟩) | ⟨U,h',t',hx,hu,step,hh',hs'⟩
    · simp [instantiate,isVal] at hv
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at hr
      cases hr with | makeArg hg _ hr => obtain ⟨rfl, rfl⟩ := singleton_get hg; cases hr
    · simp only [instantiate, instantiateArgs_eq_map, List.map] at step hs' ⊢
      obtain ⟨rfl,rfl⟩ := makeFn_step_inv rfl step
      exact Or.inr ⟨U,_,_,hx,hu,step,hh',
        refine_value rfl (HeapKnowledge.shift_holds (HeapKnowledge.alloc_frame hk)) hs'⟩

/-- Evidence names the particular observation used. The checker binds it to
an actual source sequent, so neither the slot nor the requested result type can
be changed by an untrusted producer. -/
inductive StepEvidence (ι : Type) where
  | ordinary (proof : ProgramCertificates.Evidence ι)
  | pure (proof : ProgramCertificates.Evidence ι)
  | created (proof : ProgramCertificates.Evidence ι)
  | typedRead (slot : Nat) (proof : ProgramCertificates.Evidence ι)
  | observedRead (slot : Nat) (contents : List Atom)
  /-- A read of a location a fact says holds no `undefined`: the ordinary read
  at the location's contract (`proof`), whose slice without `undefined` is
  below the claim (`sub`). -/
  | slicedRead (slot : Nat) (proof : ProgramCertificates.Evidence ι) (sub : PositiveCertificates.Proof ι)
  | knownValue (slot : Nat) (contents : List Atom)
  /-- The fields, their slots and their contents are read off the term and the
  state, so this carries only the ordinary derivation it stands beside. -/
  | allocated (proof : ProgramCertificates.Evidence ι)
  | written (receiver value : Nat) (contents : Option (List Atom)) (proof : ProgramCertificates.Evidence ι)

/-- Only allocation whose initializer is an existing value slot can frame facts.
The descriptor is not evaluated; its code obligations stay in ordinary evidence. -/
def allocationSlot : Tm → Option Nat
  | .make _ (.var i) => some i
  | _ => none

/-- The field an operation names, read off the term rather than supplied by the
producer, so evidence cannot claim a fact about a field the program never
touched. -/
def readSlot : Tm → Option (PropKey × Nat)
  | .readAt f (.var i) => some (f, i)
  | _ => none

def writeSlots : Tm → Option (PropKey × Nat × Nat)
  | .writeAt f (.var i) (.var v) => some (f, i, v)
  | _ => none

theorem readSlot_eq {t f i} (h : readSlot t = some (f, i)) : t = .readAt f (.var i) := by
  unfold readSlot at h
  split at h <;> simp_all

/-- A merge of two slots, which allocates the object it copies into. -/
def mergeSlots : Tm → Option (List PropKey × Nat × Nat)
  | .merge d (.var a) (.var b) => some (d, a, b)
  | _ => none

theorem mergeSlots_eq {t d a b} (h : mergeSlots t = some (d, a, b)) :
    t = .merge d (.var a) (.var b) := by
  unfold mergeSlots at h
  split at h <;> simp_all

/-- A store allocated from value slots: its elements' fresh locations lie past
the heap's end, so what was known of the heap stays known. -/
def storeSlots : Tm → Option (List Nat)
  | .arrLit inits => ProgramCertificates.varSlots inits
  | _ => none

theorem storeSlots_eq {t slots} (h : storeSlots t = some slots) :
    t = .arrLit (slots.map .var) := by
  unfold storeSlots at h
  split at h
  · rw [ProgramCertificates.varSlots_eq h]
  · simp at h

/-- A store of values takes one fresh location per element, past the heap's
end: every fact about the old heap, and every link, still holds. -/
theorem store_alloc_sound [DecidableEq ι] {G : NormalGraph ι} {k A ρ n W h}
    {vs : List Tm} (hvals : ∀ v ∈ vs, isVal v = true)
    (hk : HeapKnowledge.Holds k ρ h)
    (hs : Safe (meaning G A) n W h (.arrLit vs)) :
    SafePost (meaning G A)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h')
      n W h (.arrLit vs) :=
  one_step rfl rfl (.arrAlloc hvals)
    (HeapKnowledge.shift_holds (HeapKnowledge.alloc_frames vs hk)) hs

/-- The keys a claimed object type names: the fields a fresh object's
distinctness is stated at, since a later claim can name no other. -/
def namedKeys [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) : List PropKey :=
  ((expand G A).flatMap fun c => match c with
    | .refs fs rs vs os _ _ => ((fs :: rs).flatten ++ vs).map Prod.fst ++ os.map (·.key)
    | _ => []).eraseDups

theorem writeSlots_eq {t f i v} (h : writeSlots t = some (f, i, v)) :
    t = .writeAt f (.var i) (.var v) := by
  unfold writeSlots at h
  split at h <;> simp_all

/-- The successful result is the guaranteed postcondition in the result-pushed
frame. Edge checking must entail the destination's facts from this output;
checking a node alone does not establish its supplied input knowledge. -/
def checkStepUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : Knowledge) (step : StepEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) : Option Knowledge :=
  match step with
  | .ordinary e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTreeUsing G images e codes = true
    then some (ordinaryOutput k) else none
  | .pure e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧
        checkTreeUsing G images e codes = true ∧ pureTerm j.term = true
    then some (pureOutput k j.term) else none
  | .created e =>
    if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTreeUsing G images e codes = true then
      match j.term with
      | .makeFn (.graph _ _ _ _ _ _ _) .nul => some (HeapKnowledge.shift k)
      | _ => none
    else none
  | .typedRead i e =>
    match readSlot j.term with
    | some (fld, i') =>
      if claim e = j ∧ checkTreeUsing G images e codes = true ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld)
      then some (readFrame k i fld)
      else if claim e = j ∧ checkTreeUsing G images e = true ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => optionalOperand (expand G Ref) fld)
      then some (readFrame k i fld true) else none
    | none => none
  | .observedRead i R =>
    match readSlot j.term with
    | some (fld, i') =>
      if i' = i ∧ i < j.context.length ∧
          Fact.mk i R fld ∈ k.cells ∧ includes G j.type R = true
      then some (readOutput k i fld R) else none
    | none => none
  | .slicedRead i e p =>
    match readSlot j.term with
    | some (fld, i') =>
      if (claim e).context = j.context ∧ (claim e).term = j.term ∧ checkTreeUsing G images e codes = true ∧ i' = i ∧
          (j.context[i]?).any (fun Ref => fieldOperand (expand G Ref) fld) ∧
          (k.cells.any fun f => f.slot == i && f.field == fld && f.contents.all (· != .undef)) ∧
          PositiveCertificates.checkUsing G images (BranchRefinement.tagSlice G (claim e).type .isUndef false)
            j.type p = true
      then some (readFrame k i fld) else none
    | none => none
  | .knownValue i R =>
    if j.term = .var i ∧ i < j.context.length ∧
        valuesAt G j.context k i = some R ∧ includes G j.type R = true
    then some (withResult (copy k i) R) else none
  | .allocated e =>
    match allocationSlots j.term with
    | some slots =>
      if claim e = j ∧ checkScope j.context.length j.term = true ∧ checkTreeUsing G images e codes = true ∧
          (slots.map Prod.fst).Nodup ∧ ∀ p ∈ slots, p.2 < j.context.length
      then some (allocOutput k (allocationFacts G j.context k slots) (contractFields G j.context)
        (slots.map Prod.fst)) else none
    | none =>
      match mergeSlots j.term with
      | some (_, a, b) =>
        if claim e = j ∧ checkTreeUsing G images e codes = true ∧ a < j.context.length ∧ b < j.context.length
        then some (allocOutput k [] (contractFields G j.context) (namedKeys G j.type)) else none
      | none =>
        match storeSlots j.term with
        | some slots =>
          if claim e = j ∧ checkTreeUsing G images e codes = true ∧ ∀ i ∈ slots, i < j.context.length
          then some (HeapKnowledge.shift k) else none
        | none => none
  | .written i v R e =>
    match writeSlots j.term with
    | some (fld, i', v') =>
      if claim e = j ∧ checkTreeUsing G images e codes = true ∧ i' = i ∧ v' = v ∧
          i < j.context.length ∧ v < j.context.length ∧
          valuesAt G j.context k v = R
      then some (writeOutput k i fld R) else none
    | none => none

/-- The finite image checker, the default. -/
abbrev checkStep [DecidableEq ι] (G : NormalGraph ι) :=
  @checkStepUsing _ _ G (finiteInstanceImages G)

theorem checkStep_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {j k e out}
    {codes : CodeEntry ι → Bool} (hc : checkStepUsing G images j k e codes = some out)
    (hcodes : CodesSound G codes := by exact Verification.Model.ProgramCertificates.codesSound_none _)
    {ρ n W h}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds out (push v ρ) h')
      n W h (instantiate 0 ρ j.term) := by
  cases e with
  | ordinary e =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,_,ht⟩ := hp
      have typed := checkTreeUsing_sound e ht hcodes
      rw [hj] at typed
      cases hc
      exact ordinary_sound typed he hk hw hh
    · contradiction
  | pure e =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,scope,ht,hpure⟩ := hp
      have typed := checkTreeUsing_sound e ht hcodes
      rw [hj] at typed
      cases hc
      exact pure_sound typed hpure scope he hk hw hh
    · contradiction
  | created e =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i hp
      obtain ⟨hj,_,ht⟩ := hp
      have typed := checkTreeUsing_sound e ht hcodes
      rw [hj] at typed
      split at hc
      · rename_i arity E K start caps kind rest hb
        cases hc
        rw [hb] at typed ⊢
        exact graphCreation_sound typed he hk hw hh
      · contradiction
    · contradiction
  | typedRead i e =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i fld i' hslot
      split at hc
      · rename_i hp
        obtain ⟨hj,ht,rfl,hr⟩ := hp
        have term := readSlot_eq hslot
        cases hi : j.context[i']? with
        | none => simp [hi] at hr
        | some Ref =>
          have hrep : fieldOperand (expand G Ref) fld = true := by simpa [hi] using hr
          have typed := checkTreeUsing_sound e ht hcodes
          rw [hj,term] at typed
          cases hc
          rw [term]
          simpa [instantiate] using typedRead_sound typed hi hrep he hk hw hh
      · split at hc
        · rename_i hp
          obtain ⟨hj,ht,rfl,hr⟩ := hp
          have term := readSlot_eq hslot
          cases hi : j.context[i']? with
          | none => simp [hi] at hr
          | some Ref =>
            have hrep : optionalOperand (expand G Ref) fld = true := by simpa [hi] using hr
            have typed := checkTreeUsing_sound e ht
            rw [hj,term] at typed
            cases hc
            rw [term]
            simpa [instantiate] using optionalRead_sound typed hi hrep he hk hw hh
        · contradiction
    · contradiction
  | observedRead i R =>
    simp only [checkStepUsing] at hc
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
  | slicedRead i e p =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i fld i' hslot
      split at hc
      · rename_i hp
        obtain ⟨hctx,hterm,ht,rfl,hr,hf,hsub⟩ := hp
        have term := readSlot_eq hslot
        cases hi : j.context[i']? with
        | none => simp [hi] at hr
        | some Ref =>
          have hrep : fieldOperand (expand G Ref) fld = true := by simpa [hi] using hr
          obtain ⟨f,hfm,hff⟩ := List.any_eq_true.mp hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hff
          obtain ⟨⟨hfs,hfd⟩,hfc⟩ := hff
          have hm : Fact.mk i' f.contents fld ∈ k.cells := by
            have : f = Fact.mk i' f.contents fld := by cases f; simp_all
            rw [← this]; exact hfm
          have typed := checkTreeUsing_sound e ht hcodes
          have hj : claim e = ⟨j.context,j.term,(claim e).type⟩ := by
            cases hce : claim e; simp_all
          rw [hj,term] at typed
          cases hc
          rw [term]
          have hs := slicedRead_sound typed hi hrep hm hfc he hk hw hh
          simpa [instantiate] using
            consequence (PositiveCertificates.acceptedUsing hsub) (fun _ _ hq => hq) hs
      · contradiction
    · contradiction
  | knownValue i R =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i hp
      obtain ⟨ht,_,hr,hi⟩ := hp
      cases hc
      rw [ht]
      simpa [instantiate] using value_sound hr hi he hk
    · contradiction
  | allocated e =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i slots hslots
      split at hc
      · rename_i hp
        obtain ⟨hj,_,ht,hnd,hin⟩ := hp
        have typed := checkTreeUsing_sound e ht hcodes
        rw [hj] at typed
        obtain ⟨code, term⟩ := allocationSlots_eq hslots
        cases hc
        rw [term] at typed ⊢
        have hs := typed.sound n W h ρ he hw hh
        cases code
        all_goals
          simp only [instantiate, instantiateArgs_eq_map, List.map_map,
            Function.comp_def] at hs ⊢
        all_goals exact alloc_sound hnd hin he hk hh hs
      · contradiction
    · split at hc
      · rename_i d a b hmerge
        split at hc
        · rename_i hp
          obtain ⟨hj,ht,ha,hb⟩ := hp
          have typed := checkTreeUsing_sound e ht hcodes
          rw [hj] at typed
          have term := mergeSlots_eq hmerge
          cases hc
          rw [term] at typed ⊢
          have hs := typed.sound n W h ρ he hw hh
          simp only [instantiate] at hs ⊢
          have hva := (meaning_value (he.2 a _ (List.getElem?_eq_getElem ha))).1
          have hvb := (meaning_value (he.2 b _ (List.getElem?_eq_getElem hb))).1
          exact merge_alloc_sound _ hva hvb he hk hh hs
        · contradiction
      · split at hc
        · rename_i slots hstore
          split at hc
          · rename_i hp
            obtain ⟨hj,ht,hin⟩ := hp
            have typed := checkTreeUsing_sound e ht hcodes
            rw [hj] at typed
            have term := storeSlots_eq hstore
            cases hc
            rw [term] at typed ⊢
            have hs := typed.sound n W h ρ he hw hh
            simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def] at hs ⊢
            refine store_alloc_sound ?_ hk hs
            intro v hv
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
            exact (meaning_value (he.2 i _ (List.getElem?_eq_getElem (hin i hi)))).1
          · contradiction
        · contradiction
  | written i v R e =>
    simp only [checkStepUsing] at hc
    split at hc
    · rename_i fld i' v' hslots
      split at hc
      · rename_i hp
        obtain ⟨hj,ht,rfl,rfl,hi,hv,hr⟩ := hp
        have term := writeSlots_eq hslots
        have typed := checkTreeUsing_sound e ht hcodes
        rw [hj] at typed
        rw [term] at typed
        cases hc
        rw [term]
        simpa [instantiate] using write_sound typed hi hv hr he hk hw hh
      · contradiction
    · contradiction

#print axioms bagOperand_mem
#print axioms bagOperand_sound
#print axioms alloc_sound
#print axioms merge_alloc_sound
#print axioms store_alloc_sound
#print axioms graphCreation_sound
#print axioms checkStep_sound
#print axioms fieldOperand_sound
#print axioms typedRead_sound
#print axioms optionalRead_sound
#print axioms write_sound
#print axioms read_sound
#print axioms value_sound
#print axioms ordinary_sound
end Verification.Model.HeapExpressionRules
