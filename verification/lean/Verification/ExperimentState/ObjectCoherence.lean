import Verification.ExperimentState.Bindings

/-!
# Object identity coherence

A ghost registry records the immutable descriptor chosen at each allocation.
It is not another execution machine: preservation below follows `Step` itself.
Objects in terms, nested code, and heap cells must agree with this registry.
An already allocated object's body is closed under its argument binder, even
when that object occurs inside open source code.
-/
namespace Verification.ExperimentState.ObjectCoherence

abbrev Registry := List CallCode

def Extends (D E : Registry) : Prop :=
  ∀ (l : Nat) c, D[l]? = some c → E[l]? = some c

theorem Extends.refl (D : Registry) : Extends D D := fun _ _ h => h

theorem Extends.trans {D E F} (h : Extends D E) (h' : Extends E F) : Extends D F :=
  fun l c hc => h' l c (h l c hc)

theorem extends_append (D : Registry) (c : CallCode) : Extends D (D ++ [c]) := by
  intro l b hl
  have hlt : l < D.length := List.getElem?_eq_some_iff.mp hl |>.1
  simpa [List.getElem?_append, hlt] using hl

/-- Every object occurrence agrees with its allocation, including inside code. -/
def Names (D : Registry) : Tm → Prop
  | .obj l .absent => D[l]? = some .absent
  | .obj l (.closure b) => D[l]? = some (.closure b) ∧ Scoped 1 b ∧ Names D b
  | .attach b a => Names D b ∧ Names D a
  | .letE a b | .app a b | .write a b => Names D a ∧ Names D b
  | .alloc a | .read a | .test _ a => Names D a
  | .ite c a b => Names D c ∧ Names D a ∧ Names D b
  | _ => True

theorem Names.mono {D E t} (ht : Names D t) (hx : Extends D E) : Names E t := by
  induction t using Tm.induct <;> simp_all [Names]
  case objAbsent l => exact hx _ _ ht
  case objClosure l b ih => exact hx _ _ ht.1

theorem Names.descriptor {D l c} (ht : Names D (.obj l c)) : D[l]? = some c := by
  cases c with
  | absent => exact ht
  | closure b => exact ht.1

/-- Same identity means exactly the same descriptor, including its body. -/
theorem descriptor_unique {D l c c'} (h : Names D (.obj l c))
    (h' : Names D (.obj l c')) : c = c' :=
  Option.some.inj (h.descriptor.symm.trans h'.descriptor)

theorem Names.subst {D t a} (ht : Names D t) (ha : Names D a) (j : Nat) :
    Names D (subst j a t) := by
  induction t using Tm.induct generalizing j <;> simp only [Names, ExperimentState.subst] at *
  case var i => split <;> (try split) <;> simp_all [Names]
  case objClosure l b ih => rw [subst_above ht.2.1 (by omega)]; exact ht
  all_goals simp_all

theorem Names.instantiate {D t} (ht : Names D t) (ρ : Env)
    (hρ : ∀ i, Names D (ρ i)) (d : Nat) : Names D (instantiate d ρ t) := by
  induction t using Tm.induct generalizing d <;> simp only [Names, ExperimentState.instantiate] at *
  case var i => split <;> simp_all [Names]
  case objClosure l b ih => rw [instantiate_above (ht.2.1.mono (by omega))]; exact ht
  all_goals simp_all

/-- Program syntax cannot manufacture an already allocated identity, even in
an unreachable branch or the body of an empty overload. -/
def sourceTerm : Tm → Bool
  | .obj .. => false
  | .attach b a => sourceTerm b && sourceTerm a
  | .letE a b | .app a b | .write a b => sourceTerm a && sourceTerm b
  | .alloc a | .read a | .test _ a => sourceTerm a
  | .ite c a b => sourceTerm c && sourceTerm a && sourceTerm b
  | _ => true

theorem source_names {t} (ht : sourceTerm t = true) (D : Registry) : Names D t := by
  induction t using Tm.induct <;> simp_all [sourceTerm, Names]

/-- Closed terms whose object occurrences agree with the registry. -/
def TermOk (D : Registry) (t : Tm) : Prop := Scoped 0 t ∧ Names D t

theorem TermOk.mono {D E t} (ht : TermOk D t) (hx : Extends D E) : TermOk E t :=
  ⟨ht.1, ht.2.mono hx⟩

/-- The registry and heap allocate together. Each cell holds a coherent value. -/
def HeapOk (D : Registry) (h : Heap) : Prop :=
  h.length = D.length ∧ ∀ v ∈ h, isVal v = true ∧ TermOk D v

theorem HeapOk.lookup {D h v} {l : Nat} (hh : HeapOk D h) (hv : h[l]? = some v) :
    isVal v = true ∧ TermOk D v := hh.2 v (List.mem_of_getElem? hv)

theorem HeapOk.write {D h v l} (hh : HeapOk D h) (hv : isVal v = true)
    (ht : TermOk D v) : HeapOk D (h.set l v) := by
  refine ⟨by simpa using hh.1, ?_⟩
  intro w hw
  rcases List.mem_or_eq_of_mem_set hw with hw | rfl
  · exact hh.2 w hw
  · exact ⟨hv, ht⟩

theorem HeapOk.alloc {D h v} (hh : HeapOk D h) (hv : isVal v = true)
    (ht : TermOk D v) (c : CallCode) : HeapOk (D ++ [c]) (h ++ [v]) := by
  refine ⟨by simp [hh.1], ?_⟩
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · have hw := hh.2 w hw
    exact ⟨hw.1, hw.2.mono (extends_append D c)⟩
  · have he : w = v := by simpa using hw
    subst w
    exact ⟨hv, ht.mono (extends_append D c)⟩

/-- Every actual expression step preserves coherence. Only allocation extends
its registry; existing entries are never rewritten. -/
theorem step_preserves {h t h' t'} (step : Step h t h' t') :
    ∀ D, HeapOk D h → TermOk D t →
      ∃ E, Extends D E ∧ HeapOk E h' ∧ TermOk E t' := by
  induction step with
  | appL step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | appR hv step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2,ht.2.2⟩
    exact ⟨E,hx,hh',⟨ht.1.1,hs⟩,ht.2.1.mono hx,hn⟩
  | letC step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | letV hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,subst_scoped ht.1.2 ht.1.1 (by omega),ht.2.2.subst ht.2.1 0⟩
  | beta hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,subst_scoped ht.1.1 ht.1.2 (by omega),ht.2.1.2.2.subst ht.2.2 0⟩
  | @makeC h a h' a' c step ih =>
    intro D hh ht
    cases c with
    | absent =>
      obtain ⟨E,hx,hh',ht'⟩ := ih D hh ht
      exact ⟨E,hx,hh',ht'⟩
    | closure b =>
      obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2,ht.2.2⟩
      exact ⟨E,hx,hh',⟨ht.1.1,hs⟩,ht.2.1.mono hx,hn⟩
  | @makeV v h c hv =>
    intro D hh ht
    have hx := extends_append D c
    have hl : (D ++ [c])[h.length]? = some c := by simp [hh.1]
    cases c with
    | absent =>
      refine ⟨D ++ [CallCode.absent],extends_append D .absent,hh.alloc hv ht .absent,?_⟩
      exact ⟨True.intro,hl⟩
    | closure b =>
      exact ⟨D ++ [.closure b],hx,hh.alloc hv ⟨ht.1.2,ht.2.2⟩ (.closure b),
        ht.1.1,hl,ht.1.1,ht.2.1.mono hx⟩
  | readC step ih =>
    intro D hh ht
    exact ih D hh ht
  | readV hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,(hh.lookup hv).2⟩
  | writeC1 step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | writeC2 hv step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2,ht.2.2⟩
    exact ⟨E,hx,hh',⟨ht.1.1,hs⟩,ht.2.1.mono hx,hn⟩
  | writeV hv hl =>
    intro D hh ht
    exact ⟨D,.refl D,hh.write hv ⟨ht.1.2,ht.2.2⟩,trivial,trivial⟩
  | testC step ih =>
    intro D hh ht
    exact ih D hh ht
  | testV hv =>
    intro D hh ht
    refine ⟨D,.refl D,hh,?_⟩
    split <;> exact ⟨trivial,trivial⟩
  | iteC step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.1.mono hx,ht.2.2.2.mono hx⟩
  | iteT =>
    intro D hh ht
    exact ⟨D,.refl D,hh,ht.1.2.1,ht.2.2.1⟩
  | iteF =>
    intro D hh ht
    exact ⟨D,.refl D,hh,ht.1.2.2,ht.2.2.2⟩

#print axioms descriptor_unique
#print axioms step_preserves

end Verification.ExperimentState.ObjectCoherence
