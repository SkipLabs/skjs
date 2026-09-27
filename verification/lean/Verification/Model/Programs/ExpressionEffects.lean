import Verification.Model.Programs.HeapExpressionRules

/-! Definition-side effect checks over lowered expressions. Safety comes from
ordinary evidence; this layer establishes the additional heap postcondition. -/
namespace Verification.Model.ExpressionEffects
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapObservations

/-- Operands already evaluated by source lowering. -/
def valueTerm : Tm → Bool
  | .var _ => true
  | t => isVal t

theorem valueTerm_instantiate {G : NormalGraph ι} {Γ t ρ n W}
    (hv : valueTerm t = true) (hc : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) : isVal (instantiate 0 ρ t) = true := by
  cases t <;> simp_all [valueTerm, isVal, instantiate, checkScope]
  case objAt fs code => cases code <;> rfl
  case var i =>
    exact (meaning_value (he.2 i Γ[i] (List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩))).1

/-- A required named field, through either an invariant cell or a read view.
The contents contract supplies valuehood; a heap is not assumed to contain
values at every arbitrary, untyped location. -/
def readable (G : NormalGraph ι) (Ref : Ty ι) (fld : PropKey) : Bool :=
  match expand G Ref with
  | [c] => match namedMembers c with
    | some (fs, vs) => (fs ++ vs).any (fun p => p.1 == fld)
    | none => false
  | _ => false

theorem readable_value {G : NormalGraph ι} {Ref fld n W h v}
    (hr : readable G Ref fld = true) (hv : meaning G Ref (n+1) W v)
    (hh : HeapOk (n+1) W h) :
    ∃ u, Step h (.readAt fld v) h u ∧ isVal u = true := by
  unfold readable at hr
  split at hr
  · rename_i c hc
    split at hr
    · rename_i fs vs hm
      obtain ⟨⟨f,A⟩, hf, heq⟩ := List.any_eq_true.mp hr
      have heq : f = fld := by simpa using heq
      subst f
      have hfields := namedMembers_sem hc hm hv
      rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨fields,l,ctr,rfl,hfield,hlookup,hagree⟩ :=
          recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A,hf,rfl⟩) hfields.1
        obtain ⟨u,hu,ht⟩ := hh.2 l ctr hlookup
        exact ⟨u,.readField hfield hu, meaning_valOnly G A 0 _ u
          ((hagree 0 (by omega) _ u).mp (ht 0 (by omega)))⟩
      · obtain ⟨fields,l,ctr,rfl,hfield,hlookup,hbound⟩ :=
          viewT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A,hf,rfl⟩) hfields.2
        obtain ⟨u,hu,ht⟩ := hh.2 l ctr hlookup
        exact ⟨u,.readField hfield hu, meaning_valOnly G A 0 _ u
          (hbound 0 (by omega) _ u (ht 0 (by omega)))⟩
    · contradiction
  · contradiction

/-- Pure computations, required-field reads, and allocations with evaluated
initializers. Invocation requires a separate qualified-call derivation. -/
def check (G : NormalGraph ι) (Γ : List (Ty ι)) (t : Tm) : Bool :=
  Purity.pureTerm t || match t with
  | .readAt f (.var i) => (Γ[i]?).any (fun Ref => readable G Ref f)
  | .makeAt _ _ xs | .arrLit xs => xs.all valueTerm
  | _ => false

/-- A single allocation changes only freshly appended locations. -/
theorem make_preserves {T n W h code fields xs}
    (hv : ∀ v ∈ xs, isVal v = true)
    (hs : Safe T n W h (.makeAt code fields xs)) :
    SafePost T (CallEffects.Effect.preservesInputHeap.post h) n W h (.makeAt code fields xs) := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hb,_⟩ | ⟨v,hr,_⟩) | ⟨U,h',t',hx,hu,st,hh,hs⟩
    · contradiction
    · cases hr with
      | makeArg hg _ hr => exact False.elim (by
          have := hv _ (List.mem_of_getElem? hg)
          rw [raises_not_val hr] at this; contradiction)
    · cases st with
      | makeArg hg _ st => exact False.elim (value_no_step (hv _ (List.mem_of_getElem? hg)) st)
      | makeFields hvs hlen =>
        exact .inr ⟨U,_,_,hx,hu,.makeFields hvs hlen,hh,
          refine_value rfl ⟨xs,rfl⟩ hs⟩

theorem array_preserves {T n W h xs}
    (hv : ∀ v ∈ xs, isVal v = true)
    (hs : Safe T n W h (.arrLit xs)) :
    SafePost T (CallEffects.Effect.preservesInputHeap.post h) n W h (.arrLit xs) := by
  apply one_step rfl rfl (.arrAlloc hv) ⟨xs,rfl⟩ hs

theorem sound {G : NormalGraph ι} {Γ t A ρ n W h}
    (hc : check G Γ t = true) (hscope : checkScope Γ.length t = true)
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hs : Safe (meaning G A) n W h (instantiate 0 ρ t)) :
    SafePost (meaning G A) (CallEffects.Effect.preservesInputHeap.post h)
      n W h (instantiate 0 ρ t) := by
  simp only [check, Bool.or_eq_true] at hc
  rcases hc with hp | hc
  · exact CallEffects.pure_safe (.term (HeapExpressionRules.pure_instantiate hp hscope he)) hs
  · split at hc
    · rename_i t fld i
      simp only [Option.any_eq_true] at hc
      obtain ⟨Ref,hi,hr⟩ := hc
      cases n with
      | zero => trivial
      | succ n =>
        obtain ⟨u,st,hval⟩ := readable_value hr (he.2 i Ref hi) hh
        exact one_step rfl hval st ⟨[],by simp⟩ hs
    · rename_i t code fields xs
      have hscopes : ∀ a ∈ xs, checkScope Γ.length a = true := by
        cases code <;> simp_all [checkScope, checkScopes_iff, List.all_eq_true]
      have hvalues : ∀ v ∈ xs.map (instantiate 0 ρ), isVal v = true := by
        intro v hv
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
        exact valueTerm_instantiate (List.all_eq_true.mp hc a ha) (hscopes a ha) he
      cases code <;> simp only [instantiate, instantiateArgs_eq_map] at hs ⊢ <;>
        exact make_preserves hvalues hs
    · rename_i t xs
      simp only [checkScope, checkScopes_iff, List.all_eq_true] at hscope
      simp only [instantiate, instantiateArgs_eq_map] at hs ⊢
      apply array_preserves _ hs
      intro v hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      exact valueTerm_instantiate (List.all_eq_true.mp hc a ha) (hscope a ha) he
    · contradiction

#print axioms sound
end Verification.Model.ExpressionEffects
