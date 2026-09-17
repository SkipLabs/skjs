import Verification.ExperimentState.CallArguments

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

theorem extends_append (D E : Registry) : Extends D (D ++ E) := by
  intro l b hl
  have hlt : l < D.length := List.getElem?_eq_some_iff.mp hl |>.1
  simpa [List.getElem?_append, hlt] using hl

/-- One allocation gives every field of the new object the same descriptor, in
the locations `slots` hands out, so the registry grows by that many copies. -/
theorem registry_alloc {D : Registry} {c : CallCode} {k l : Nat}
    (hl : D.length ≤ l) (hu : l < D.length + k) :
    (D ++ List.replicate k c)[l]? = some c := by
  rw [List.getElem?_append_right hl]
  simp [show l - D.length < k by omega]

/-- The locations an object's fields stand for. Identity is these locations,
so the registry constrains them and nothing else about the map. -/
def locs (fs : List (String × Nat)) : List Nat := fs.map Prod.snd

theorem mem_locs {fs : List (String × Nat)} {l : Nat} :
    l ∈ locs fs ↔ ∃ f, (f, l) ∈ fs := by
  simp only [locs, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.1, by simpa using hp⟩
  · rintro ⟨f, hf⟩; exact ⟨(f, l), hf, rfl⟩

theorem mem_slots {base : Nat} {ns : List String} {p : String × Nat}
    (h : p ∈ slots base ns) : base ≤ p.2 ∧ p.2 < base + ns.length := by
  induction ns generalizing base with
  | nil => simp [slots] at h
  | cons n ns ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h
      simp only [List.length_cons]
      omega

/-! Every object occurrence agrees with its allocation, including inside code. -/
mutual
def Names (D : Registry) : Tm → Prop
  | .objAt fs .absent => ∀ l ∈ locs fs, D[l]? = some .absent
  | .objAt fs (.closure n b) =>
      (∀ l ∈ locs fs, D[l]? = some (.closure n b)) ∧ Scoped n b ∧ Names D b
  | .makeAt (.closure _ b) _ args => Names D b ∧ NamesArgs D args
  | .makeAt .absent _ args => NamesArgs D args
  | .call f args => Names D f ∧ NamesArgs D args
  | .letE a b | .writeAt _ a b | .arith _ a b => Names D a ∧ Names D b
  | .readAt _ a | .test _ a => Names D a
  | .ite c a b => Names D c ∧ Names D a ∧ Names D b
  | _ => True

def NamesArgs (D : Registry) : List Tm → Prop
  | [] => True
  | a :: args => Names D a ∧ NamesArgs D args
end

@[simp] theorem namesArgs_iff (D : Registry) (args : List Tm) :
    NamesArgs D args ↔ ∀ a ∈ args, Names D a := by
  induction args <;> simp_all [NamesArgs]

theorem Names.mono {D E t} (ht : Names D t) (hx : Extends D E) : Names E t := by
  induction t using Tm.induct <;> simp_all [Names]
  case objAbsent fs => exact fun l hl => hx _ _ (ht l hl)
  case objClosure fs n b ih => exact fun l hl => hx _ _ (ht.1 l hl)

theorem Names.descriptor {D fs c} (ht : Names D (.objAt fs c)) :
    ∀ l ∈ locs fs, D[l]? = some c := by
  cases c with
  | absent => exact ht
  | closure n b => exact ht.1

/-- Same identity means exactly the same descriptor, including its body. An
identity is its fields, so this needs one of them to name. -/
theorem descriptor_unique {D fs c c'} {l : Nat} (hl : l ∈ locs fs)
    (h : Names D (.objAt fs c)) (h' : Names D (.objAt fs c')) : c = c' :=
  Option.some.inj ((h.descriptor l hl).symm.trans (h'.descriptor l hl))

theorem Names.subst {D t a} (ht : Names D t) (ha : Names D a) (j : Nat) :
    Names D (subst j a t) := by
  induction t using Tm.induct generalizing j <;> simp only [Names, namesArgs_iff, ExperimentState.subst, substArgs_eq_map] at *
  case var i => split <;> (try split) <;> simp_all [Names]
  case objClosure l n b ih => rw [subst_above ht.2.1 (by omega)]; exact ht
  all_goals simp_all

theorem Names.bindArgs {D t args} (ht : Names D t)
    (ha : ∀ a ∈ args, Names D a) (d : Nat) : Names D (bindArgs d args t) := by
  induction args generalizing d with
  | nil => exact ht
  | cons a args ih =>
    exact (ih (fun v hv => ha v (List.mem_cons_of_mem a hv)) (d + 1)).subst
      (ha a (by simp)) d

theorem Names.bindParameters {D t args} (ht : Names D t)
    (ha : ∀ a ∈ args, Names D a) (arity : Nat) :
    Names D (CallArguments.bindParameters arity args t) :=
  ht.bindArgs (CallArguments.parameters_property (by trivial) ha) 0

theorem Names.instantiate {D t} (ht : Names D t) (ρ : Env)
    (hρ : ∀ i, Names D (ρ i)) (d : Nat) : Names D (instantiate d ρ t) := by
  induction t using Tm.induct generalizing d <;> simp only [Names, namesArgs_iff, ExperimentState.instantiate, instantiateArgs_eq_map] at *
  case var i => split <;> simp_all [Names]
  case objClosure l n b ih => rw [instantiate_above (ht.2.1.mono (by omega))]; exact ht
  all_goals simp_all

/-! Program syntax cannot manufacture an already allocated identity, even in
an unreachable branch or the body of an empty overload. -/
mutual
def sourceTerm : Tm → Bool
  | .objAt .. => false
  | .makeAt (.closure _ b) _ args => sourceTerm b && sourceArgs args
  | .makeAt .absent _ args => sourceArgs args
  | .call f args => sourceTerm f && sourceArgs args
  | .letE a b | .writeAt _ a b | .arith _ a b => sourceTerm a && sourceTerm b
  | .readAt _ a | .test _ a => sourceTerm a
  | .ite c a b => sourceTerm c && sourceTerm a && sourceTerm b
  | _ => true

def sourceArgs : List Tm → Bool
  | [] => true
  | a :: args => sourceTerm a && sourceArgs args
end

@[simp] theorem sourceArgs_iff (args : List Tm) :
    sourceArgs args = true ↔ ∀ a ∈ args, sourceTerm a = true := by
  induction args <;> simp_all [sourceArgs]

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

theorem HeapOk.alloc {D h vs} (hh : HeapOk D h)
    (hv : ∀ v ∈ vs, isVal v = true ∧ TermOk D v) (c : CallCode) :
    HeapOk (D ++ List.replicate vs.length c) (h ++ vs) := by
  refine ⟨by simp [hh.1], ?_⟩
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · have hw := hh.2 w hw
    exact ⟨hw.1, hw.2.mono (extends_append D _)⟩
  · exact ⟨(hv w hw).1, (hv w hw).2.mono (extends_append D _)⟩

/-- Every actual expression step preserves coherence. Only allocation extends
its registry; existing entries are never rewritten. -/
theorem step_preserves {h t h' t'} (step : Step h t h' t') :
    ∀ D, HeapOk D h → TermOk D t →
      ∃ E, Extends D E ∧ HeapOk E h' ∧ TermOk E t' := by
  induction step with
  | callL step ih =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,fun v hv => (ht.2.2 v hv).mono hx⟩
  | callArg hv hg hb step ih =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    have hm := List.mem_of_getElem? hg
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2 _ hm,ht.2.2 _ hm⟩
    refine ⟨E,hx,hh',⟨ht.1.1,?_⟩,ht.2.1.mono hx,?_⟩
    · intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv | rfl
      · exact ht.1.2 v hv
      · exact hs
    · intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv | rfl
      · exact (ht.2.2 v hv).mono hx
      · exact hn
  | letC step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | letV hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,subst_scoped ht.1.2 ht.1.1 (by omega),ht.2.2.subst ht.2.1 0⟩
  | callV hv =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
    refine ⟨D,.refl D,hh,?_,?_⟩
    · exact CallArguments.bound_body_closed (by simpa [Scoped] using ht.1.1)
        ht.1.2
    · exact ht.2.1.2.2.bindParameters ht.2.2 _
  | @makeArg c ns inits i h h' a a' hg hb step ih =>
    intro D hh ht
    have hm := List.mem_of_getElem? hg
    cases c with
    | absent =>
      simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
      obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1 _ hm,ht.2 _ hm⟩
      refine ⟨E,hx,hh',?_,?_⟩
      · intro v hv
        rcases List.mem_or_eq_of_mem_set hv with hv | rfl
        · exact ht.1 v hv
        · exact hs
      · intro v hv
        rcases List.mem_or_eq_of_mem_set hv with hv | rfl
        · exact (ht.2 v hv).mono hx
        · exact hn
    | closure n b =>
      simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
      obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2 _ hm,ht.2.2 _ hm⟩
      refine ⟨E,hx,hh',⟨ht.1.1,?_⟩,ht.2.1.mono hx,?_⟩
      · intro v hv
        rcases List.mem_or_eq_of_mem_set hv with hv | rfl
        · exact ht.1.2 v hv
        · exact hs
      · intro v hv
        rcases List.mem_or_eq_of_mem_set hv with hv | rfl
        · exact (ht.2.2 v hv).mono hx
        · exact hn
  | @makeFields c ns vs h hv hlen =>
    intro D hh ht
    have hx := extends_append D (List.replicate vs.length c)
    have hfield : ∀ l ∈ locs (slots h.length ns),
        (D ++ List.replicate vs.length c)[l]? = some c := by
      intro l hl
      obtain ⟨f,hf⟩ := mem_locs.mp hl
      obtain ⟨hlo,hhi⟩ := mem_slots (p := (f,l)) hf
      have hdl := hh.1
      have hnl := hlen
      exact registry_alloc (by omega) (by omega)
    cases c with
    | absent =>
      simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
      exact ⟨_,hx,hh.alloc (fun v hv' => ⟨hv v hv',ht.1 v hv',ht.2 v hv'⟩) .absent,
        trivial,hfield⟩
    | closure n b =>
      simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
      refine ⟨_,hx,hh.alloc (fun v hv' => ⟨hv v hv',ht.1.2 v hv',ht.2.2 v hv'⟩) _,?_,?_⟩
      · simpa using ht.1.1
      · exact ⟨hfield,by simpa using ht.1.1,ht.2.1.mono hx⟩
  | readC step ih =>
    intro D hh ht
    exact ih D hh ht
  | readField hl hv =>
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
  | writeField hv hl hlt =>
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
  | arithC1 step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | arithC2 hv step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2,ht.2.2⟩
    exact ⟨E,hx,hh',⟨ht.1.1,hs⟩,ht.2.1.mono hx,hn⟩
  | arithV =>
    intro D hh ht
    exact ⟨D,.refl D,hh,trivial,trivial⟩

#print axioms descriptor_unique
#print axioms step_preserves

end Verification.ExperimentState.ObjectCoherence
