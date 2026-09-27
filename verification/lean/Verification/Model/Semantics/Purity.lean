import Verification.Model.Semantics.CallArguments

/-! Executable purity checks and their operational justification. -/
namespace Verification.Model.Purity

/-- Source lowering inserts variable copies and literal nodes between
operations. These are pure: unlike calls they must not discard cell facts. -/
def pureTerm : Tm → Bool
  | .var _ => true
  | .test _ a => pureTerm a
  | .ite c t e => pureTerm c && pureTerm t && pureTerm e
  | .arith _ a b => pureTerm a && pureTerm b
  | .throw a => pureTerm a
  /- A length reads the store it is given, or a string's code units, and
  gives a number: it changes no heap. -/
  | .lenOf a => pureTerm a
  | t => isVal t

/-- Purity is closed under actual reduction and rules out every heap change.
Stored closure bodies need not be pure: observing an object does not invoke it. -/
theorem pure_step {h t h' t'} (hs : Step h t h' t') (hp : pureTerm t = true) :
    h' = h ∧ pureTerm t' = true := by
  induction hs <;> simp_all [pureTerm,isVal]
  case testV => split <;> simp [pureTerm,isVal]
  case arithV hb =>
    rcases (binop_result hb).2.2 with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  case arithThrow => rfl

/-- Substituting values for all free variables preserves purity. The graph
machine's environment is total, including its default slot. -/
theorem pure_instantiate_values {t : Tm} {ρ : Env}
    (hp : pureTerm t = true) (he : ∀ i, isVal (ρ i) = true) :
    pureTerm (instantiate 0 ρ t) = true := by
  induction t using Tm.induct <;> simp_all [pureTerm, isVal, instantiate]
  case var i =>
    have hv := he i
    cases h : ρ i <;> simp_all [pureTerm, isVal]

theorem pure_value {v : Tm} (hv : isVal v = true) : pureTerm v = true := by
  cases v <;> simp_all [pureTerm, isVal]

/-- The machine states reached by graph code whose node expressions are
pure. Continuations only rearrange values; they do not change the heap. -/
inductive PureRun : Tm → Prop where
  | term : pureTerm t = true → PureRun t
  | goto : (∀ e ∈ E, pureTerm e = true) →
      (∀ v ∈ L, isVal v = true) → isVal d = true → PureRun (.goto E K l L d)
  | frame : (∀ e ∈ E, pureTerm e = true) →
      (∀ v ∈ L, isVal v = true) → isVal d = true → pureTerm t = true →
      PureRun (.frame E K t L d k x)

private theorem env_values {L : List Tm} {d : Tm}
    (hL : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) (i : Nat) :
    isVal (envOf L d i) = true := by
  rcases getD_mem_or L i d with h | h
  · exact hL _ h
  · change isVal (L.getD i d) = true
    rw [h]
    exact hd

private theorem mapped_values {L : List Tm} {d : Tm}
    (hL : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) (m : Option (List Nat)) :
    (∀ v ∈ (envMap m L d).1, isVal v = true) ∧ isVal (envMap m L d).2 = true := by
  have all : ∀ v, v ∈ (envMap m L d).1 ∨ v = (envMap m L d).2 → isVal v = true := by
    intro v hv
    rcases envMap_mem hv with h | rfl
    · exact hL v h
    · exact hd
  exact ⟨fun v hv => all v (.inl hv), all _ (.inr rfl)⟩

private theorem mapped_goto {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm}
    {d : Tm} {l : Nat} {m : Option (List Nat)}
    (hE : ∀ e ∈ E, pureTerm e = true)
    (hL : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) :
    PureRun (.goto E K l (envMap m L d).1 (envMap m L d).2) := by
  obtain ⟨hL', hd'⟩ := mapped_values hL hd m
  exact .goto hE hL' hd'

theorem PureRun.step {h t h' t'} (hp : PureRun t) (hs : Step h t h' t') :
    h' = h ∧ PureRun t' := by
  cases hp with
  | term hp =>
    obtain ⟨rfl, hp'⟩ := pure_step hs hp
    exact ⟨rfl, .term hp'⟩
  | goto hE hL hd =>
    cases hs with
    | gotoEnter he hk =>
      exact ⟨rfl, .frame hE hL hd
        (pure_instantiate_values (hE _ (List.mem_of_getElem? he)) (env_values hL hd))⟩
  | frame hE hL hd ht =>
    cases hs with
    | frameC st =>
      obtain ⟨rfl, ht'⟩ := pure_step st ht
      exact ⟨rfl, .frame hE hL hd ht'⟩
    | frameRet hv => exact ⟨rfl, .term (pure_value hv)⟩
    | frameBind hv =>
      refine ⟨rfl, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all
    | frameEffect hv =>
      refine ⟨rfl, ?_⟩
      exact mapped_goto hE hL hd
    | frameYes | frameNo =>
      refine ⟨rfl, ?_⟩
      exact mapped_goto hE hL hd
    | frameYesBind | frameNoBind =>
      refine ⟨rfl, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all [isVal]
    | frameTag hv =>
      refine ⟨rfl, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all
    | frameHandle hr =>
      have hv := raises_val hr
      refine ⟨rfl, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all
    | frameRaise hr =>
      exact ⟨rfl, .term (by simpa [pureTerm] using pure_value (raises_val hr))⟩

#print axioms PureRun.step

end Verification.Model.Purity
