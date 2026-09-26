import Verification.Model.Programs.PointClaims
import Verification.Model.Semantics.HeapObservations

/-! Finite current-content assertions. They constrain the current heap, never
change a world's contract, and carry no ownership or disjointness promise.
Edge entailment selects facts by runtime-environment slots and weakens their
primitive predicates. The representation has no execution indices in its syntax. -/
namespace Verification.Model.HeapFacts
open ProgramTyping PositiveRules PositiveGraphs HeapObservations

/-- A finite vocabulary of primitive predicates. `num` covers every numeric
value; `numLit` preserves an exact bit pattern. Neither is a storage contract.
`defined` is any value but `undefined`, of any shape: what a write of a value
whose type rules `undefined` out leaves in a cell. No clause states it, so a
read of the cell is typed at its contract less `undefined`
(`HeapExpressionRules.slicedRead`), never at the atom. -/
inductive Atom where
  | nul | undef | tru | fls | num | numLit (bits : UInt64) | str | strLit (value : String)
  | defined
  deriving DecidableEq, Repr

def Atom.holds : Atom → Tm → Prop
  | .nul, v => v = .nul
  | .undef, v => v = .undef
  | .tru, v => v = .tru
  | .fls, v => v = .fls
  | .num, v => ∃ bits, v = .num bits
  | .numLit bits, v => v = .num bits
  | .str, v => ∃ s, v = .str s
  | .strLit s, v => v = .str s
  | .defined, v => isVal v = true ∧ v ≠ .undef

theorem Atom.isValue {a : Atom} {v} (h : a.holds v) : isVal v = true := by
  cases a <;> simp only [Atom.holds] at h
  all_goals first | exact h.1 | (rcases h with ⟨bits,rfl⟩; rfl) | (subst v; rfl)

def Atom.clause (a : Atom) : PositiveNormalization.Clause α :=
  match a with
  | .nul => .nul | .undef => .undef | .tru => .boolLit true
  | .fls => .boolLit false | .num => .num | .numLit b => .numLit b
  | .str => .str | .strLit s => .strLit s
  | .defined => .top

/-- A primitive atom is exactly its clause. -/
theorem Atom.sem {a : Atom} {S : α → Fam} {P : α → ArgFam} {n W v} (hd : a ≠ .defined) :
    PositiveNormalization.semWithArgs S P a.clause n W v ↔ a.holds v := by
  cases a <;> first | rfl | exact absurd rfl hd

def Atom.le (a b : Atom) : Bool :=
  a == b || match a, b with
    | .numLit _, .num => true | .strLit _, .str => true
    | .defined, _ | .undef, _ => false
    | _, .defined => true
    | _, _ => false

theorem Atom.le_sound {a b : Atom} {v} (h : a.le b = true) (hv : a.holds v) : b.holds v := by
  simp only [Atom.le, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact hv
  · cases a <;> cases b <;> simp only [Atom.holds] at hv h ⊢ <;> try contradiction
    all_goals first
      | exact hv
      | (obtain ⟨_, rfl⟩ := hv; exact ⟨rfl, by simp⟩)
      | (subst v; exact ⟨rfl, by simp⟩)
      | (subst v; rfl)
      | (obtain ⟨_, rfl⟩ := hv; exact ⟨_, rfl⟩)

def covers (source target : List Atom) : Bool :=
  source.all fun a => target.any a.le

theorem covers_sound {source target v} (h : covers source target = true)
    (hv : ∃ a ∈ source, a.holds v) : ∃ b ∈ target, b.holds v := by
  obtain ⟨a,ha,hv⟩ := hv
  obtain ⟨b,hb,hab⟩ := List.any_eq_true.mp (List.all_eq_true.mp h a ha)
  exact ⟨b,hb,Atom.le_sound hab hv⟩

theorem covers_refl (as : List Atom) : covers as as = true := by
  apply List.all_eq_true.mpr
  intro a ha
  exact List.any_eq_true.mpr ⟨a,ha,by simp [Atom.le]⟩

/-- A current-content assertion: at the object a runtime slot holds, the named
field currently satisfies one of these primitive predicates. A value fact reuses the same
shape and ignores the field, which is why it defaults to the cell's. -/
structure Fact where
  slot : Nat
  contents : List Atom
  field : PropKey := valueField
  deriving DecidableEq, Repr

abbrev Facts := List Fact

def Holds (facts : Facts) (ρ : Env) (h : Heap) : Prop :=
  ∀ f ∈ facts, ∃ flds c l v, ρ f.slot = .objAt flds c ∧ flds.lookup f.field = some l ∧
    h[l]? = some v ∧ ∃ a ∈ f.contents, a.holds v

theorem holds_nil (ρ h) : Holds [] ρ h := by simp [Holds]

/-- All target facts must have an incoming justification. Repeated slot maps
retain aliases; different slot numbers do not imply different locations. -/
def check (source target : Facts) (mapping : PointClaims.Mapping) : Bool :=
  target.all fun f => source.any fun g =>
    g.slot == PointClaims.slot mapping f.slot && g.field == f.field &&
      covers g.contents f.contents

theorem check_sound {source target mapping ρ h}
    (hc : check source target mapping = true) (hs : Holds source ρ h) :
    Holds target (PointClaims.mapEnv mapping ρ) h := by
  intro f hmem
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc f hmem)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨flds,c,l,v,hl,hfd,hv,hm⟩ := hs g hg
  refine ⟨flds,c,l,v,?_,?_,hv,covers_sound hc.2 hm⟩
  · simpa [PointClaims.mapEnv,hc.1.1] using hl
  · rw [← hc.1.2]; exact hfd

/-- The value added by a bind shifts every old environment slot. -/
def shift (facts : Facts) : Facts := facts.map fun f => { f with slot := f.slot+1 }

theorem shift_holds {facts ρ h v} (hf : Holds facts ρ h) :
    Holds (shift facts) (push v ρ) h := by
  intro f hm
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
  exact hf g hg

/-- A read preserves all assertions because it leaves the heap unchanged. -/
theorem read {facts ρ h i fld R n W}
    (hf : Holds facts ρ h) (hm : Fact.mk i R fld ∈ facts)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (fun _ _ v => ∃ a ∈ R, a.holds v)
      (fun h' _ => Holds facts ρ h') n W h (.readAt fld (ρ i)) := by
  obtain ⟨flds,c,l,v,hl,hfd,hv,a,ha,hav⟩ := hf _ hm
  rw [hl]
  apply consequence _ _ (read_observed hw hh hfd (Atom.isValue hav) hv)
  · intro _ _ u hu; subst u; exact ⟨a,ha,hav⟩
  · intro h' _ hp; rw [hp.1]; exact hf

/-- A write invalidates every old observation, including facts about aliases.
Only the fact about the written location is established. -/
theorem write {A : Fam} (ha : Adm A) {ρ h i a v n W}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hr : refT A n W (ρ i))
    (hv : a.holds v) (ht : A n W v) :
    SafePost nulT (fun h' _ => Holds [⟨i,[a],valueField⟩] ρ h') n W h
      (.write (ρ i) v) := by
  obtain ⟨flds,l,c,he,hfd,hl,hc⟩ := refT_iff.mp hr
  have hrec : recT [(valueField, A)] n W (.objAt flds .absent) :=
    recT_single.mpr ⟨flds,l,c,rfl,hfd,hl,hc⟩
  rw [he]
  apply weaken _ (write_observed ha hw hh hrec hfd (Atom.isValue hv) ht)
  intro h' _ hp f hmem
  simp only [List.mem_singleton] at hmem
  subst f
  refine ⟨flds,.absent,l,v,he,hfd,?_,a,by simp,hv⟩
  rw [hp.1]
  apply write_new
  rw [hh.1]
  exact (List.getElem?_eq_some_iff.mp hl).1

/-- Allocation preserves existing observations and adds the new cell at the
result slot. This relies on actual heap extension, not on non-aliasing names. -/
theorem alloc {A : Fam} (ha : Adm A) {facts ρ h a v n W}
    (hf : Holds facts ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hv : a.holds v) (ht : A n W v) :
    SafePost (refT A)
      (fun h' v => Holds (⟨0,[a],valueField⟩ :: shift facts) (push v ρ) h') n W h
      (.alloc v) := by
  apply weaken _ (alloc_observed ha hw hh (Atom.isValue hv) ht)
  intro h' result hp f hm
  rw [hp.1,hp.2]
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ⟨[(valueField,h.length)],.absent,h.length,v,rfl,lookup_value _,
      alloc_new h v,a,by simp,hv⟩
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
    obtain ⟨flds,c,l,u,hl,hfd,hu,b,hb,he⟩ := hf g hg
    exact ⟨flds,c,l,u,hl,hfd,alloc_frame hu,b,hb,he⟩

#print axioms Atom.sem
#print axioms Atom.isValue
#print axioms Atom.le_sound
#print axioms covers_sound
#print axioms check_sound
#print axioms read
#print axioms write
#print axioms alloc
end Verification.Model.HeapFacts
