import Verification.Model.Semantics.CallArguments

/-!
# Object identity coherence

A ghost registry records the immutable descriptor chosen at each allocation.
It is not another execution machine: preservation below follows `Step` itself.
Objects in terms, nested code, and heap cells must agree with this registry.
An already allocated object's body is closed under its argument binder, even
when that object occurs inside open source code.
-/
namespace Verification.Model.ObjectCoherence

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
def locs (fs : List (PropKey × Nat)) : List Nat := fs.map Prod.snd

theorem mem_locs {fs : List (PropKey × Nat)} {l : Nat} :
    l ∈ locs fs ↔ ∃ f, (f, l) ∈ fs := by
  simp only [locs, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.1, by simpa using hp⟩
  · rintro ⟨f, hf⟩; exact ⟨(f, l), hf, rfl⟩

theorem mem_slots {base : Nat} {ns : List PropKey} {p : PropKey × Nat}
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
  | .objAt fs (.closure n b k) =>
      (∀ l ∈ locs fs, D[l]? = some (.closure n b k)) ∧ Scoped (n + 1) b ∧ Names D b
  | .makeAt (.closure _ b _) _ args => Names D b ∧ NamesArgs D args
  | .objAt fs (.variadic n b) =>
      (∀ l ∈ locs fs, D[l]? = some (.variadic n b)) ∧ Scoped (n + 2) b ∧ Names D b
  | .makeAt (.variadic _ b) _ args => Names D b ∧ NamesArgs D args
  | .objAt fs (.bound t r pre) =>
      (∀ l ∈ locs fs, D[l]? = some (.bound t r pre)) ∧
        (Scoped 0 t ∧ Scoped 0 r ∧ ScopedArgs 0 pre) ∧ Names D t ∧ Names D r ∧ NamesArgs D pre
  | .makeAt (.bound t r pre) _ args =>
      Names D t ∧ Names D r ∧ NamesArgs D pre ∧ NamesArgs D args
  | .makeAt .absent _ args => NamesArgs D args
  | .invoke f r args => Names D f ∧ Names D r ∧ NamesArgs D args
  | .construct f args => Names D f ∧ NamesArgs D args
  | .letE a b | .writeAt _ a b | .arith _ a b | .elemAt a b
  | .indexAt a b => Names D a ∧ Names D b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => Names D a
  | .setElem a b c => Names D a ∧ Names D b ∧ Names D c
  | .arrLit args => NamesArgs D args
  | .arr ls => ∀ l ∈ ls.filterMap id, D[l]? = some .absent
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
  case arr ls => exact fun l hl => hx l _ (ht l hl)
  case objAbsent fs => exact fun l hl => hx _ _ (ht l hl)
  case objClosure fs n b ih => exact fun l hl => hx _ _ (ht.1 l hl)
  case objVariadic fs n b ih => exact fun l hl => hx _ _ (ht.1 l hl)
  case objBound fs t r pre iht ihr ihp => exact fun l hl => hx _ _ (ht.1 l hl)

theorem Names.descriptor {D fs c} (ht : Names D (.objAt fs c)) :
    ∀ l ∈ locs fs, D[l]? = some c := by
  cases c with
  | absent => exact ht
  | closure n b => exact ht.1
  | variadic n b => exact ht.1
  | bound t r pre => exact ht.1

/-- Same identity means exactly the same descriptor, including its body. An
identity is its fields, so this needs one of them to name. -/
theorem descriptor_unique {D fs c c'} {l : Nat} (hl : l ∈ locs fs)
    (h : Names D (.objAt fs c)) (h' : Names D (.objAt fs c')) : c = c' :=
  Option.some.inj ((h.descriptor l hl).symm.trans (h'.descriptor l hl))

theorem Names.subst {D t a} (ht : Names D t) (ha : Names D a) (j : Nat) :
    Names D (subst j a t) := by
  induction t using Tm.induct generalizing j <;> simp only [Names, namesArgs_iff, Model.subst, substArgs_eq_map] at *
  case var i => split <;> (try split) <;> simp_all [Names]
  case objClosure l n b ih => rw [subst_above ht.2.1 (by omega)]; exact ht
  case objVariadic l n b ih => rw [subst_above ht.2.1 (by omega)]; exact ht
  case objBound fs t r pre iht ihr ihp =>
    have hpre : pre.map (Model.subst j a) = pre := by
      simpa using (List.map_congr_left (g := id)
        (fun x hx => subst_above ((scopedArgs_iff _ _).mp ht.2.1.2.2 x hx) (Nat.zero_le j) a))
    rw [subst_above ht.2.1.1 (Nat.zero_le j), subst_above ht.2.1.2.1 (Nat.zero_le j), hpre]
    exact ht
  all_goals simp_all

theorem Names.bindArgs {D t args} (ht : Names D t)
    (ha : ∀ a ∈ args, Names D a) (d : Nat) : Names D (bindArgs d args t) := by
  induction args generalizing d with
  | nil => exact ht
  | cons a args ih =>
    exact (ih (fun v hv => ha v (List.mem_cons_of_mem a hv)) (d + 1)).subst
      (ha a (by simp)) d

theorem Names.bindParameters {D t r args} (ht : Names D t) (hr : Names D r)
    (ha : ∀ a ∈ args, Names D a) (arity : Nat) :
    Names D (CallArguments.bindParameters arity args r t) :=
  ht.bindArgs (fun a hm => (List.mem_cons.mp hm).elim (fun h => h ▸ hr)
    (CallArguments.parameters_property (by trivial) ha a)) 0

theorem Names.instantiate {D t} (ht : Names D t) (ρ : Env)
    (hρ : ∀ i, Names D (ρ i)) (d : Nat) : Names D (instantiate d ρ t) := by
  induction t using Tm.induct generalizing d <;> simp only [Names, namesArgs_iff, Model.instantiate, instantiateArgs_eq_map] at *
  case var i => split <;> simp_all [Names]
  case objClosure l n b ih => rw [instantiate_above (ht.2.1.mono (by omega))]; exact ht
  case objVariadic l n b ih => rw [instantiate_above (ht.2.1.mono (by omega))]; exact ht
  case objBound fs t r pre iht ihr ihp =>
    have hpre : pre.map (Model.instantiate d ρ) = pre := by
      simpa using (List.map_congr_left (g := id)
        (fun x hx => instantiate_above
          (((scopedArgs_iff _ _).mp ht.2.1.2.2 x hx).mono (Nat.zero_le d)) ρ))
    rw [instantiate_above (ht.2.1.1.mono (Nat.zero_le d)),
      instantiate_above (ht.2.1.2.1.mono (Nat.zero_le d)), hpre]
    exact ht
  all_goals simp_all

/-! Program syntax cannot manufacture an already allocated identity, even in
an unreachable branch or the body of an empty overload. -/
mutual
def sourceTerm : Tm → Bool
  | .objAt .. => false
  | .makeAt (.closure _ b _) _ args => sourceTerm b && sourceArgs args
  | .makeAt (.variadic _ b) _ args => sourceTerm b && sourceArgs args
  | .makeAt (.bound t r pre) _ args =>
      sourceTerm t && sourceTerm r && sourceArgs pre && sourceArgs args
  | .makeAt .absent _ args => sourceArgs args
  | .invoke f r args => sourceTerm f && sourceTerm r && sourceArgs args
  | .construct f args => sourceTerm f && sourceArgs args
  | .letE a b | .writeAt _ a b | .arith _ a b | .elemAt a b
  | .indexAt a b => sourceTerm a && sourceTerm b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => sourceTerm a
  | .setElem a b c => sourceTerm a && sourceTerm b && sourceTerm c
  | .arrLit args => sourceArgs args
  | .arr .. => false
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

/-- A makeAt's initializers are coherent whatever its code. -/
theorem termOk_make_arg {D c ns inits a} (ht : TermOk D (.makeAt c ns inits)) (hm : a ∈ inits) :
    TermOk D a := by
  cases c <;> simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
  · exact ⟨ht.1 a hm, ht.2 a hm⟩
  · exact ⟨ht.1.2 a hm, ht.2.2 a hm⟩
  · exact ⟨ht.1.2 a hm, ht.2.2 a hm⟩
  · exact ⟨ht.1.2.2.2 a hm, ht.2.2.2.2 a hm⟩

/-- What a coherent term throws is coherent. -/
theorem raises_termOk {t v} (hr : Raises t v) {D} (ht : TermOk D t) : TermOk D v := by
  induction hr with
  | throwV => simpa [TermOk, Scoped, Names] using ht
  | callArg _ _ hg _ _ ih =>
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
    have hm := List.mem_of_getElem? hg
    exact ih ⟨ht.1.2.2 _ hm, ht.2.2.2 _ hm⟩
  | constructArg _ hg _ _ ih =>
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
    have hm := List.mem_of_getElem? hg
    exact ih ⟨ht.1.2 _ hm, ht.2.2 _ hm⟩
  | makeArg hg _ _ ih => exact ih (termOk_make_arg ht (List.mem_of_getElem? hg))
  | arrArg hg _ _ ih =>
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
    have hm := List.mem_of_getElem? hg
    exact ih ⟨ht.1 _ hm, ht.2 _ hm⟩
  | callL _ ih => exact ih ⟨ht.1.1, ht.2.1⟩
  | callRecv _ _ ih => exact ih ⟨ht.1.2.1, ht.2.2.1⟩
  | constructL _ ih => exact ih ⟨ht.1.1, ht.2.1⟩
  | letC _ ih => exact ih ⟨ht.1.1, ht.2.1⟩
  | indexC1 _ ih | writeC1 _ ih | arithC1 _ ih | elemC1 _ ih | iteC _ ih | setC1 _ ih =>
    exact ih ⟨ht.1.1, ht.2.1⟩
  | indexC2 _ _ ih | writeC2 _ _ ih | arithC2 _ _ ih | elemC2 _ _ ih =>
    exact ih ⟨ht.1.2, ht.2.2⟩
  | setC2 _ _ ih => exact ih ⟨ht.1.2.1, ht.2.2.1⟩
  | setC3 _ _ _ ih => exact ih ⟨ht.1.2.2, ht.2.2.2⟩
  | throwC _ ih | spreadC _ ih | readC _ ih | testC _ ih | lenC _ ih => exact ih ht

/-- Every actual expression step preserves coherence. Only allocation extends
its registry; existing entries are never rewritten. -/
theorem step_preserves {h t h' t'} (step : Step h t h' t') :
    ∀ D, HeapOk D h → TermOk D t →
      ∃ E, Extends D E ∧ HeapOk E h' ∧ TermOk E t' := by
  induction step with
  | constructL step ih =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,fun v hv => (ht.2.2 v hv).mono hx⟩
  | constructArg hv hg hb step ih =>
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
  | constructV hv =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
    refine ⟨D,.refl D,hh,?_,?_⟩
    · exact CallArguments.bound_body_closed (by simpa [Scoped, Nat.add_comm] using ht.1.1)
        (by simp [Scoped]) ht.1.2
    · exact ht.2.1.2.2.bindParameters (by simp [Names]) ht.2.2 _
  | callL step ih =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.1.mono hx,fun v hv => (ht.2.2.2 v hv).mono hx⟩
  | callRecv hv step ih =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2.1,ht.2.2.1⟩
    exact ⟨E,hx,hh',⟨ht.1.1,hs,ht.1.2.2⟩,ht.2.1.mono hx,hn,
      fun v hv => (ht.2.2.2 v hv).mono hx⟩
  | callArg hv hr hg hb step ih =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    have hm := List.mem_of_getElem? hg
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2.2 _ hm,ht.2.2.2 _ hm⟩
    refine ⟨E,hx,hh',⟨ht.1.1,ht.1.2.1,?_⟩,ht.2.1.mono hx,ht.2.2.1.mono hx,?_⟩
    · intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv | rfl
      · exact ht.1.2.2 v hv
      · exact hs
    · intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv | rfl
      · exact (ht.2.2.2 v hv).mono hx
      · exact hn
  | letC step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | letV hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,subst_scoped ht.1.2 ht.1.1 (by omega),ht.2.2.subst ht.2.1 0⟩
  | callV hr hv =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
    refine ⟨D,.refl D,hh,?_,?_⟩
    · exact CallArguments.bound_body_closed (by simpa [Scoped, Nat.add_comm] using ht.1.1)
        ht.1.2.1 ht.1.2.2
    · exact ht.2.1.2.2.bindParameters ht.2.2.1 ht.2.2.2 _
  | @callRest r args _ fs n b hr hv =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht
    refine ⟨D,.refl D,hh,?_,?_⟩
    · exact CallArguments.invoke_closed (CallArguments.Invoke.variadic (fs := fs) hr hv)
        (by simpa [Scoped] using ht.1.1) ht.1.2.1 ht.1.2.2
    · simp only [CallArguments.bindRest, Names, namesArgs_iff,
        List.mem_singleton, forall_eq]
      exact ⟨fun a hm => ht.2.2.2 a (List.mem_of_mem_drop hm),
        ht.2.1.2.2.bindArgs (fun a hm => (List.mem_cons.mp hm).elim (fun h => h ▸ ht.2.2.1)
          (CallArguments.parameters_property (by trivial) ht.2.2.2 a)) 1⟩
  | callBound hr hv =>
    intro D hh ht
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    obtain ⟨⟨_, _, hsa⟩, ⟨_, ⟨hst, hsr, hsp⟩, hnt, hnr, hnp⟩, _, hna⟩ := ht
    refine ⟨D, .refl D, hh, ⟨hst, hsr, fun a hm => ?_⟩, hnt, hnr, fun a hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · exact hsp a hm
      · exact hsa a hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact hnp a hm
      · exact hna a hm
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
    | closure n b | variadic n b =>
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
    | bound t r pre =>
      simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
      obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2.2.2 _ hm,ht.2.2.2.2 _ hm⟩
      refine ⟨E,hx,hh',⟨ht.1.1,ht.1.2.1,ht.1.2.2.1,?_⟩,ht.2.1.mono hx,ht.2.2.1.mono hx,
        fun v hv => (ht.2.2.2.1 v hv).mono hx,?_⟩
      · intro v hv
        rcases List.mem_or_eq_of_mem_set hv with hv | rfl
        · exact ht.1.2.2.2 v hv
        · exact hs
      · intro v hv
        rcases List.mem_or_eq_of_mem_set hv with hv | rfl
        · exact (ht.2.2.2.2 v hv).mono hx
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
    | closure n b | variadic n b =>
      simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
      refine ⟨_,hx,hh.alloc (fun v hv' => ⟨hv v hv',ht.1.2 v hv',ht.2.2 v hv'⟩) _,?_,?_⟩
      · simpa using ht.1.1
      · exact ⟨hfield,by simpa using ht.1.1,ht.2.1.mono hx⟩
    | bound t r pre =>
      simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
      refine ⟨_,hx,hh.alloc (fun v hv' => ⟨hv v hv',ht.1.2.2.2 v hv',ht.2.2.2.2 v hv'⟩) _,
        ⟨ht.1.1,ht.1.2.1,ht.1.2.2.1⟩,hfield,⟨ht.1.1,ht.1.2.1,ht.1.2.2.1⟩,ht.2.1.mono hx,
        ht.2.2.1.mono hx,fun v hv => (ht.2.2.2.1 v hv).mono hx⟩
  | readC step ih =>
    intro D hh ht
    exact ih D hh ht
  | readField hl hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,(hh.lookup hv).2⟩
  | readProto _ _ hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,by simpa [TermOk, Scoped, Names] using (hh.lookup hv).2⟩
  | readMissing _ _ =>
    intro D hh ht
    exact ⟨D,.refl D,hh,by simp [TermOk, Scoped, Names]⟩
  | indexC1 step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | indexC2 hv step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2,ht.2.2⟩
    exact ⟨E,hx,hh',⟨ht.1.1,hs⟩,ht.2.1.mono hx,hn⟩
  | indexField _ hl hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,(hh.lookup hv).2⟩
  | indexProto _ _ _ hv =>
    intro D hh ht
    have hp := (hh.lookup hv).2
    exact ⟨D,.refl D,hh,⟨hp.1,ht.1.2⟩,hp.2,ht.2.2⟩
  | indexMissing _ _ _ =>
    intro D hh ht
    exact ⟨D,.refl D,hh,by simp [TermOk, Scoped, Names]⟩
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
  | arithV hb =>
    intro D hh ht
    rcases (binop_result hb).2.2 with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      exact ⟨D,.refl D,hh,trivial,trivial⟩
  | @arrArg inits i h h' a a' hg hb step ih =>
    intro D hh ht
    have hm := List.mem_of_getElem? hg
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
  | @arrAlloc vs h hv =>
    intro D hh ht
    have hx := extends_append D (List.replicate vs.length .absent)
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    refine ⟨_,hx,hh.alloc (fun v hv' => ⟨hv v hv',ht.1 v hv',ht.2 v hv'⟩) .absent,trivial,?_⟩
    intro l hl
    have hb := mem_elemSlots hl
    have hdl := hh.1
    exact registry_alloc (by omega) (by omega)
  | elemC1 step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.mono hx⟩
  | elemC2 hv step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2,ht.2.2⟩
    exact ⟨E,hx,hh',⟨ht.1.1,hs⟩,ht.2.1.mono hx,hn⟩
  | elemRead hl hv =>
    intro D hh ht
    exact ⟨D,.refl D,hh,(hh.lookup hv).2⟩
  | elemAbsent _ =>
    intro D hh ht
    exact ⟨D,.refl D,hh,trivial,trivial⟩
  | setC1 step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.1,ht.2.1⟩
    exact ⟨E,hx,hh',⟨hs,ht.1.2⟩,hn,ht.2.2.1.mono hx,ht.2.2.2.mono hx⟩
  | setC2 hv step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2.1,ht.2.2.1⟩
    exact ⟨E,hx,hh',⟨ht.1.1,hs,ht.1.2.2⟩,ht.2.1.mono hx,hn,ht.2.2.2.mono hx⟩
  | setC3 hv hi step ih =>
    intro D hh ht
    obtain ⟨E,hx,hh',hs,hn⟩ := ih D hh ⟨ht.1.2.2,ht.2.2.2⟩
    exact ⟨E,hx,hh',⟨ht.1.1,ht.1.2.1,hs⟩,ht.2.1.mono hx,ht.2.2.1.mono hx,hn⟩
  | setPresent hw hl hlt =>
    intro D hh ht
    exact ⟨D,.refl D,hh.write hw ⟨ht.1.2.2,ht.2.2.2⟩,trivial,ht.2.1⟩
  | @setGrow ls b k h v hw hk hn =>
    intro D hh ht
    have hx := extends_append D (List.replicate 1 .absent)
    refine ⟨_,hx,?_,trivial,?_⟩
    · have := hh.alloc (vs := [v]) (fun w hw' => by
        simp only [List.mem_singleton] at hw'; subst hw'; exact ⟨hw,ht.1.2.2,ht.2.2.2⟩) .absent
      simpa using this
    · intro l hl
      rcases mem_placeAt hl with hl | rfl
      · exact hx l _ (ht.2.1 l hl)
      · have hdl := hh.1
        exact registry_alloc (by omega) (by omega)
  | lenC step ih =>
    intro D hh ht
    exact ih D hh ht
  | throwC step ih =>
    intro D hh ht
    exact ih D hh ht
  | arithThrow _ =>
    intro D hh ht
    exact ⟨D,.refl D,hh,by simp [Scoped, thrownError],by simp [Names, thrownError, locs]⟩
  | lenV | lenStr =>
    intro D hh ht
    exact ⟨D,.refl D,hh,trivial,trivial⟩
  | elemStr =>
    intro D hh ht
    unfold codeUnitAt
    split <;> exact ⟨D,.refl D,hh,trivial,trivial⟩
  | spreadC step ih =>
    intro D hh ht
    exact ih D hh ht
  | arrSpread he hp hr =>
    intro D hh ht
    subst he
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    have hvs : ∀ v ∈ _, isVal v = true ∧ TermOk D v := fun v hv =>
      (readElems_mem hr v hv).elim (fun he => he ▸ ⟨rfl, trivial, trivial⟩)
        (fun ⟨_, hl⟩ => hh.lookup hl)
    refine ⟨D,.refl D,hh,?_,?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · exact ht.1 v (by simp [hv])
        · exact (hvs v hv).2.1
      · exact ht.1 v (by simp [hv])
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · exact ht.2 v (by simp [hv])
        · exact (hvs v hv).2.2
      · exact ht.2 v (by simp [hv])
  | callSpread hf hrv he hp hr =>
    intro D hh ht
    subst he
    simp only [TermOk, Scoped, scopedArgs_iff, Names, namesArgs_iff] at ht ⊢
    have hvs : ∀ v ∈ _, isVal v = true ∧ TermOk D v := fun v hv =>
      (readElems_mem hr v hv).elim (fun he => he ▸ ⟨rfl, trivial, trivial⟩)
        (fun ⟨_, hl⟩ => hh.lookup hl)
    refine ⟨D,.refl D,hh,⟨ht.1.1,ht.1.2.1,?_⟩,ht.2.1,ht.2.2.1,?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · exact ht.1.2.2 v (by simp [hv])
        · exact (hvs v hv).2.1
      · exact ht.1.2.2 v (by simp [hv])
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · exact ht.2.2.2 v (by simp [hv])
        · exact (hvs v hv).2.2
      · exact ht.2.2.2 v (by simp [hv])

#print axioms descriptor_unique
#print axioms step_preserves

end Verification.Model.ObjectCoherence
