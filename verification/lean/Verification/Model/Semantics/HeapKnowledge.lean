import Verification.Model.Semantics.HeapLinks
import Verification.Model.Programs.BranchRefinement

/-! Primitive heap and immutable-value facts for expression postconditions. Facts
are execution-state assertions, not extra world contracts or source type labels. -/
namespace Verification.Model.HeapKnowledge
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapFacts

structure Knowledge where
  cells : Facts := []
  values : Facts := []
  links : HeapLinks.Links := []
  deriving DecidableEq, Repr

def ValueHolds (facts : Facts) (ρ : Env) : Prop :=
  ∀ f ∈ facts, ∃ a ∈ f.contents, a.holds (ρ f.slot)

def Holds (k : Knowledge) (ρ : Env) (h : Heap) : Prop :=
  HeapFacts.Holds k.cells ρ h ∧ ValueHolds k.values ρ ∧ HeapLinks.Holds k.links ρ h

theorem empty (ρ h) : Holds ⟨[],[],[]⟩ ρ h := ⟨holds_nil ρ h,by simp [ValueHolds],by simp [HeapLinks.Holds]⟩

/-- A fresh allocation preserves every assertion about existing cells and aliases. -/
theorem alloc_frame {k ρ h v} (hk : Holds k ρ h) : Holds k ρ (h ++ [v]) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frame hk.2.2⟩
  intro f hf
  obtain ⟨flds,c,l,u,he,hfd,hu,a,ha,hv⟩ := hk.1 f hf
  exact ⟨flds,c,l,u,he,hfd,HeapObservations.alloc_frame hu,a,ha,hv⟩

/-- The same across a whole object's worth of fresh locations. -/
theorem alloc_frames {k ρ h} (vs : List Val) (hk : Holds k ρ h) : Holds k ρ (h ++ vs) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frames vs hk.2.2⟩
  intro f hf
  obtain ⟨flds,c,l,u,he,hfd,hu,a,ha,hv⟩ := hk.1 f hf
  exact ⟨flds,c,l,u,he,hfd,HeapObservations.alloc_frames vs hu,a,ha,hv⟩

/-- What every one of several states establishes: a fact about a slot and
field each of them states, holding what any of them says it holds; the first's
links that appear verbatim in all the others. Used by the producer at a merge
that is not a cut, where no requirement is stated; every edge is still
checked, and each state's fact covers the union. -/
def meet : List Knowledge → Knowledge
  | [] => ⟨[],[],[]⟩
  | k :: ks =>
    let joined := fun (pick : Knowledge → Facts) =>
      (pick k).filterMap fun f =>
        let others := ks.map fun o => (pick o).filter fun g => g.slot == f.slot && g.field == f.field
        if others.all (!·.isEmpty) then
          some { f with contents := (f.contents ++ others.flatten.flatMap (·.contents)).eraseDups }
        else none
    ⟨(joined (·.cells)).eraseDups, (joined (·.values)).eraseDups,
     k.links.filter (fun g => ks.all (·.links.contains g))⟩

def check (a b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  HeapFacts.check a.cells b.cells m && (HeapFacts.check a.values b.values m && HeapLinks.check a.links b.links m)

theorem check_sound {a b m ρ h} (hc : check a b m = true) (ha : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  simp only [check,Bool.and_eq_true] at hc
  refine ⟨HeapFacts.check_sound hc.1 ha.1,?_,HeapLinks.check_sound hc.2.2 ha.2.2⟩
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc.2.1 f hf)
  simp only [Bool.and_eq_true,beq_iff_eq] at hc
  obtain ⟨a,ham,he⟩ := ha.2.1 g hg
  simpa [PointClaims.mapEnv,hc.1] using covers_sound hc.2 ⟨a,ham,he⟩

def shift (k : Knowledge) : Knowledge := ⟨HeapFacts.shift k.cells,HeapFacts.shift k.values,HeapLinks.pull k.links (fun i => [i+1])⟩

theorem shift_holds {k ρ h v} (hk : Holds k ρ h) : Holds (shift k) (push v ρ) h := by
  refine ⟨HeapFacts.shift_holds hk.1,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact hk.2.1 g hg
  · apply HeapLinks.pull_holds (pre := fun i => [i+1]) hk.2.2
    intro i j hj
    have hj := List.mem_singleton.mp hj
    subst j
    rfl
/-- Effect-only continuations discard the result slot. Facts about it cannot
be transferred into the old environment. -/
def dropFacts (fs : Facts) : Facts :=
  (fs.filter fun f => 0 < f.slot).map fun f => {f with slot := f.slot - 1}

def dropResult (k : Knowledge) : Knowledge := ⟨dropFacts k.cells,dropFacts k.values,HeapLinks.pull k.links (fun i => if i = 0 then [] else [i-1])⟩

theorem dropResult_holds {k ρ h v} (hk : Holds k (push v ρ) h) :
    Holds (dropResult k) ρ h := by
  constructor
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg := List.mem_filter.mp hg
    have hp : 0 < g.slot := of_decide_eq_true hg.2
    have he : push v ρ g.slot = ρ (g.slot - 1) := by
      cases hs : g.slot with
      | zero => omega
      | succ i => rfl
    simpa [he] using hk.1 g hg.1
  · constructor
    · intro f hf
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      have hp : 0 < g.slot := of_decide_eq_true hg.2
      have he : push v ρ g.slot = ρ (g.slot - 1) := by
        cases hs : g.slot with
        | zero => omega
        | succ i => rfl
      simpa [he] using hk.2.1 g hg.1
    · apply HeapLinks.pull_holds (pre := fun i => if i = 0 then [] else [i-1]) hk.2.2
      intro i j hj
      split at hj
      · simp at hj
      · have hj := List.mem_singleton.mp hj
        subst j
        cases i with
        | zero => contradiction
        | succ i => rfl

/-- Project facts along an executable slot map. All runtime aliases selected by
that map are retained; facts about unselected slots are forgotten. -/
def projectFacts (facts : Facts) (m : PointClaims.Mapping) (count : Nat) : Facts :=
  (List.range count).flatMap fun i =>
    (facts.filter fun f => f.slot == PointClaims.slot m i).map fun f => { f with slot := i }

def project (k : Knowledge) (m : PointClaims.Mapping) (count : Nat) : Knowledge :=
  ⟨projectFacts k.cells m count,projectFacts k.values m count,
    HeapLinks.pull k.links (fun i => (List.range count).filter fun j => PointClaims.slot m j == i)⟩

theorem project_checked (k : Knowledge) (m count) : check k (project k m count) m = true := by
  have one (fs : Facts) : HeapFacts.check fs (projectFacts fs m count) m = true := by
    apply List.all_eq_true.mpr
    intro f hf
    obtain ⟨i,_,hf⟩ := List.mem_flatMap.mp hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg := List.mem_filter.mp hg
    apply List.any_eq_true.mpr
    exact ⟨g,hg.1,by simp [hg.2,covers_refl]⟩
  simp only [check,Bool.and_eq_true]
  refine ⟨one _,one _,?_⟩
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨f,hf,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  apply List.any_eq_true.mpr
  refine ⟨f,hf,?_⟩
  have hc := List.mem_filter.mp hc
  have hv := List.mem_filter.mp hv
  simp only [beq_iff_eq] at hc hv
  simp [hc.2,hv.2]

/-- The facts an observed value `R` gives about the fields it was read from:
one per current read link ending at `slot`. A read through an optional key
also covers the object lacking the key, where it gave `undefined`; it tells
what the field holds only where `R` rules `undefined` out, and then that the
key is present. -/
def linkFacts (k : Knowledge) (slot : Nat) (R : List Atom) : Facts :=
  (k.links.filter (fun g => (!g.alias && !g.distinct) && g.value == slot &&
    (!g.optional || !R.contains .undef))).map (fun g => ⟨g.cell,R,g.field⟩)

theorem holds_undef {a : Atom} (h : a.holds .undef) : a = .undef := by
  cases a <;> simp_all [Atom.holds]

theorem linkFacts_holds {k slot R ρ h} (hk : Holds k ρ h) (hv : ∃ a ∈ R, a.holds (ρ slot)) :
    HeapFacts.Holds (linkFacts k slot R) ρ h := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  have hg := List.mem_filter.mp hg
  have hg2 := hg.2
  simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq,Bool.or_eq_true] at hg2
  obtain ⟨a,ha,hav⟩ := hv
  have hl := hk.2.2 g hg.1
  simp only [hg2.1.1.1,hg2.1.1.2,Bool.false_eq_true,ite_false] at hl
  cases ho : g.optional
  · simp only [ho,Bool.false_eq_true,ite_false] at hl
    obtain ⟨flds,c,l,hl,hfd,hh⟩ := hl
    exact ⟨flds,c,l,ρ g.value,hl,hfd,hh,a,ha,by simpa [hg2.1.2] using hav⟩
  · simp only [ho,ite_true] at hl
    obtain ⟨flds,c,hl,hr⟩ := hl
    have hnu : R.contains .undef = false := by
      rcases hg2.2 with h | h
      · simp [ho] at h
      · simpa using h
    unfold HeapLinks.ReadGave at hr
    cases hfd : flds.lookup g.field with
    | none =>
      rw [hfd] at hr
      have : a = .undef := holds_undef (by rw [← hr, hg2.1.2]; exact hav)
      subst this
      simp at hnu
      exact absurd ha hnu
    | some l =>
      rw [hfd] at hr
      exact ⟨flds,c,l,ρ g.value,hl,hfd,hr,a,ha,by simpa [hg2.1.2] using hav⟩

/-- An observed Boolean outcome refines cells only through current read links.
The ordinary value fact is useful even when no cell link exists. -/
def observeBoolean (k : Knowledge) (slot : Nat) (q : Bool) : Knowledge :=
  let R := [if q then HeapFacts.Atom.tru else .fls]
  ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links⟩

theorem observeBoolean_holds {k slot q ρ h} (hk : Holds k ρ h)
    (hq : ρ slot = if q then .tru else .fls) : Holds (observeBoolean k slot q) ρ h := by
  have hv : ∃ a ∈ [if q then HeapFacts.Atom.tru else .fls], a.holds (ρ slot) :=
    ⟨(if q then .tru else .fls), by simp, by cases q <;> simpa [HeapFacts.Atom.holds] using hq⟩
  refine ⟨?_,?_,hk.2.2⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact linkFacts_holds hk hv f hf
    · exact hk.1 f hf
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hv
    · exact hk.2.1 f hf

/-- What of a predicate remains where a tag answered `q`: nothing where the
predicate's values all answer the other way; where the tag is equality with
one number or string and holds of a value of its family, that value, a
singleton (equality with a zero holds of both zeros, which stay the family);
the predicate otherwise. -/
def observeAtom (tag : Tag) (q : Bool) (a : Atom) : List Atom :=
  if tagClause tag (a.clause (α := Ty Nat)) == some (!q) then [] else
  match tag, q, a with
  | .numEq b, true, .num => if b &&& 0x7fffffffffffffff == 0 then [.num] else [.numLit b]
  | .strEq t, true, .str => [.strLit t]
  | _, _, a => [a]

theorem observeAtom_holds {tag : Tag} {q : Bool} {a : Atom} {v : Tm}
    (hv : a.holds v) (hq : tagHolds tag v = q) : ∃ a' ∈ observeAtom tag q a, a'.holds v := by
  unfold observeAtom
  split
  · rename_i hbad
    have hanswer := tagClause_sound (S := fun (_ : Ty Nat) => nulT) (P := fun _ _ _ _ => False)
      (n := 0) (W := ofList []) (beq_iff_eq.mp hbad) (Atom.sem.mpr hv)
    rw [hq] at hanswer
    cases q <;> contradiction
  · split
    · rename_i b _
      split
      · exact ⟨.num, by simp, hv⟩
      · rename_i hb
        obtain ⟨bits, rfl⟩ := hv
        refine ⟨.numLit b, by simp, ?_⟩
        simp only [tagHolds, numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hq
        simp only [Atom.holds]
        rcases hq.2 with h | h
        · rw [h]
        · exact absurd (beq_iff_eq.mpr h.2) hb
    · rename_i t _
      obtain ⟨s', rfl⟩ := hv
      refine ⟨.strLit t, by simp, ?_⟩
      simp only [tagHolds, beq_iff_eq] at hq
      simp [Atom.holds, hq]
    · exact ⟨a, by simp, hv⟩

/-- A tag narrows a saved primitive predicate, and its still-live read links transfer
that observation to the heap. No link means no assertion about a mutable cell. -/
def observeTag (k : Knowledge) (slot : Nat) (tag : Tag) (q : Bool) : Knowledge :=
  match k.values.find? (fun f => f.slot == slot) with
  | none => k
  | some f =>
    let R := f.contents.flatMap (observeAtom tag q)
    ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links⟩

/-- A primitive reads no prototype. -/
theorem atom_protoFree {a : Atom} {v : Tm} (h : a.holds v) (t : Tag) : protoFree t v = true := by
  cases v with
  | objAt fs c => cases a <;> simp [Atom.holds] at h
  | _ => cases t <;> rfl

theorem observeTag_holds {k slot tag q ρ h} (hk : Holds k ρ h)
    (hq' : tagHolds tag (ρ slot) = q ∨ protoFree tag (ρ slot) = false) :
    Holds (observeTag k slot tag q) ρ h := by
  unfold observeTag
  split
  · exact hk
  · rename_i f hf
    have hm := List.mem_of_find?_eq_some hf
    have hs : f.slot = slot := by simpa using List.find?_some hf
    obtain ⟨a,ha,hv⟩ := hk.2.1 f hm
    have hv : a.holds (ρ slot) := by simpa [hs] using hv
    -- A primitive reads no prototype.
    have hq : tagHolds tag (ρ slot) = q := hq'.resolve_right (by
      rw [atom_protoFree hv tag]; simp)
    obtain ⟨a',ha',hv'⟩ := observeAtom_holds hv hq
    have hR : ∃ b ∈ f.contents.flatMap (observeAtom tag q), b.holds (ρ slot) :=
      ⟨a', List.mem_flatMap.mpr ⟨a,ha,ha'⟩, hv'⟩
    refine ⟨?_,?_,hk.2.2⟩
    · intro f' hf'
      rcases List.mem_append.mp hf' with hf' | hf'
      · exact linkFacts_holds hk hR f' hf'
      · exact hk.1 f' hf'
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact hR
      · exact hk.2.1 f' hf'

def observe (k : Knowledge) (slot : Nat) : BranchRefinement.Observation → Knowledge
  | .boolean q => observeBoolean k slot q
  | .tag t q => observeTag k slot t q

theorem observe_holds {k slot o ρ h} (hk : Holds k ρ h)
    (ho : o.holds (ρ slot)) : Holds (observe k slot o) ρ h := by
  cases o with
  | boolean q => exact observeBoolean_holds hk ho
  | tag t q => exact observeTag_holds hk ho

/-- A finite predicate vocabulary exactly interprets supported primitive clauses. -/
def primitive : List (Clause (Ty ι)) → Option (List Atom)
  | [] => some []
  | .nul :: cs => (primitive cs).map ([.nul] ++ ·)
  | .undef :: cs => (primitive cs).map ([.undef] ++ ·)
  | .bool :: cs => (primitive cs).map ([.tru,.fls] ++ ·)
  | .boolLit b :: cs => (primitive cs).map ([if b then .tru else .fls] ++ ·)
  | .num :: cs => (primitive cs).map ([.num] ++ ·)
  | .numLit b :: cs => (primitive cs).map ([.numLit b] ++ ·)
  | .str :: cs => (primitive cs).map ([.str] ++ ·)
  | .strLit s :: cs => (primitive cs).map ([.strLit s] ++ ·)
  | _ => none

/-- A type's members as atoms, when it is of clause rows. -/
def atoms (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then primitive (expand G A) else none

theorem primitive_sem {G : NormalGraph ι} {cs R} (hc : primitive cs = some R) (n W v) :
    semList (meaning G) (argMeaning G) cs n W v ↔ ∃ a ∈ R, a.holds v := by
  induction cs generalizing R with
  | nil => simp [primitive] at hc; subst R; simp [semList,setSem]
  | cons c cs ih =>
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        simp only [hr,Option.map_some,Option.some.injEq] at hc
        subst R
        have hi := ih hr
        simp only [semList,setSem,List.mem_cons,exists_eq_or_imp] at hi ⊢
        rw [hi]
        simp [semWithArgs,nulT,undefT,boolT,numT,strT,Atom.holds,apply_ite,or_assoc]
        all_goals try (split <;> simp_all [Atom.holds])

theorem atoms_sem {G : NormalGraph ι} {A R} (h : atoms G A = some R) (n W v) :
    meaning G A n W v ↔ ∃ a ∈ R, a.holds v := by
  unfold atoms at h
  split at h
  · rw [expand_sem G A (by assumption)]
    exact primitive_sem h n W v
  · cases h

#print axioms atoms_sem
#print axioms observeTag_holds

end Verification.Model.HeapKnowledge
