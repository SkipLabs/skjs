import Verification.ExperimentState.Bindings

/-! Call preparation keeps a callee and an ordered argument list separate from
invocation. It reuses the term machine for operand effects and connects prepared
list preparation and dispatch to native call reduction. Source calling conventions
remain integration work. -/
namespace Verification.ExperimentState.CallArguments

/-- Only the leftmost non-value argument can step. Completed values are retained
in their original positions, including closures with live heap captures. -/
inductive ArgStep : Heap → List Tm → Heap → List Tm → Prop where
  | head : Step h a h' a' → ArgStep h (a::args) h' (a'::args)
  | tail : isVal v = true → ArgStep h args h' args' →
      ArgStep h (v::args) h' (v::args')

def Values (args : List Tm) : Prop := ∀ a ∈ args, isVal a = true

theorem length_preserved (s : ArgStep h args h' args') : args'.length = args.length := by
  induction s with
  | head => rfl
  | tail _ _ ih => simpa using congrArg Nat.succ ih

theorem values_no_step (hv : Values args) : ¬ ArgStep h args h' args' := by
  intro s
  induction s with
  | head hs => exact value_no_step (hv _ (by simp)) hs
  | tail _ _ ih => exact ih (fun a ha => hv a (by simp [ha]))

theorem deterministic (s : ArgStep h args h1 args1) (t : ArgStep h args h2 args2) :
    h1 = h2 ∧ args1 = args2 := by
  induction s generalizing h2 args2 with
  | head hs =>
    cases t with
    | head ht => exact (Step_det hs ht).imp id (congrArg (· :: _))
    | tail hv _ => exact False.elim (value_no_step hv hs)
  | tail hv hs ih =>
    cases t with
    | head ht => exact False.elim (value_no_step hv ht)
    | tail _ ht => exact (ih ht).imp id (congrArg (_ :: ·))

/-- An already evaluated prefix cannot be reordered or evaluated again. -/
theorem keep_prefix (hv : Values vs) (s : ArgStep h args h' args') :
    ArgStep h (vs ++ args) h' (vs ++ args') := by
  induction vs with
  | nil => exact s
  | cons v vs ih =>
    exact .tail (hv v (by simp)) (ih (fun a ha => hv a (by simp [ha])))

/-- Inversion of preparation through completed operands: every possible step
retains the entire prefix, not just the particular step constructed above. -/
theorem prefix_iff (hv : Values vs) :
    ArgStep h (vs ++ args) h' out ↔
      ∃ rest, out = vs ++ rest ∧ ArgStep h args h' rest := by
  constructor
  · intro step
    induction vs generalizing out with
    | nil => exact ⟨out,rfl,step⟩
    | cons v vs ih =>
      cases step with
      | head hs => exact False.elim (value_no_step (hv v (by simp)) hs)
      | tail _ hs =>
        obtain ⟨rest,rfl,hr⟩ := ih (fun a ha => hv a (by simp [ha])) hs
        exact ⟨rest,rfl,hr⟩
  · rintro ⟨rest,rfl,step⟩
    exact keep_prefix hv step

/-- A singleton argument list has exactly the existing argument-step behavior. -/
theorem singleton : ArgStep h [a] h' args' ↔ ∃ a', args' = [a'] ∧ Step h a h' a' := by
  constructor
  · intro s
    cases s with
    | head hs => exact ⟨_,rfl,hs⟩
    | tail _ hs => cases hs
  · rintro ⟨a',rfl,hs⟩
    exact .head hs

/-- Argument preparation selects exactly one position after a completed
prefix. This is the indexed form used by native call reduction. -/
theorem focus_iff : ArgStep h args h' args' ↔
    ∃ i a a', args[i]? = some a ∧
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) ∧
      Step h a h' a' ∧ args' = args.set i a' := by
  constructor
  · intro hs
    induction hs with
    | head hs => exact ⟨0, _, _, rfl, (by intro j hj; omega), hs, rfl⟩
    | @tail v h args h' args' hv hs ih =>
      obtain ⟨i, a, a', hg, hb, ha, he⟩ := ih
      refine ⟨i + 1, a, a', hg, ?_, ha, ?_⟩
      · intro j hj x hx
        cases j with
        | zero => cases hx; exact hv
        | succ j => exact hb j (by omega) x hx
      · exact congrArg (v :: ·) he
  · rintro ⟨i, a, a', hg, hb, hs, rfl⟩
    induction i generalizing args with
    | zero =>
      cases args with
      | nil => simp at hg
      | cons v args => cases hg; exact .head hs
    | succ i ih =>
      cases args with
      | nil => simp at hg
      | cons v args =>
        exact .tail (hb 0 (by omega) v rfl)
          (ih hg (fun j hj x hx => hb (j + 1) (by omega) x hx))

structure Frame where
  callee : Tm
  args : List Tm
  deriving DecidableEq, Repr

/-- Preparation never invokes the callee. No argument effect happens before the
callee is a value, and invocation must wait until every argument is a value. -/
inductive Prepare : Heap → Frame → Heap → Frame → Prop where
  | callee : Step h f h' f' → Prepare h ⟨f,args⟩ h' ⟨f',args⟩
  | args : isVal f = true → ArgStep h args h' args' →
      Prepare h ⟨f,args⟩ h' ⟨f,args'⟩

def Frame.ready (f : Frame) : Prop := isVal f.callee = true ∧ Values f.args

theorem prepare_deterministic (s : Prepare h f h1 f1) (t : Prepare h f h2 f2) :
    h1 = h2 ∧ f1 = f2 := by
  cases s with
  | callee hs =>
    cases t with
    | callee ht => obtain ⟨rfl,rfl⟩ := Step_det hs ht; exact ⟨rfl,rfl⟩
    | args hv _ => exact False.elim (value_no_step hv hs)
  | args hv hs =>
    cases t with
    | callee ht => exact False.elim (value_no_step hv ht)
    | args _ ht => obtain ⟨rfl,rfl⟩ := deterministic hs ht; exact ⟨rfl,rfl⟩

theorem arity_preserved (s : Prepare h f h' f') : f'.args.length = f.args.length := by
  cases s with
  | callee _ => rfl
  | args _ hs => exact length_preserved hs

theorem callee_preserved (hv : isVal f.callee = true) (s : Prepare h f h' f') :
    f'.callee = f.callee := by
  cases s with
  | callee hs => exact False.elim (value_no_step hv hs)
  | args _ _ => rfl

theorem ready_no_prepare (hf : f.ready) : ¬ Prepare h f h' f' := by
  intro s
  cases s with
  | callee hs => exact value_no_step hf.1 hs
  | args _ hs => exact values_no_step hf.2 hs

/-- Current unary evaluation embeds in this preparation interface before beta. -/
theorem unary_step (s : Prepare h ⟨f,[a]⟩ h' frame) :
    ∃ f' a', frame = ⟨f',[a']⟩ ∧ Step h (.app f a) h' (.app f' a') := by
  cases s with
  | callee hs => exact ⟨_,_,rfl,.appL hs⟩
  | args hv hs =>
    obtain ⟨a',rfl,ha⟩ := singleton.mp hs
    exact ⟨_,_,rfl,.appR hv ha⟩

theorem parameters_length (n : Nat) (args : List Tm) :
    (parameters n args).length = n := by
  induction n generalizing args with
  | zero => rfl
  | succ n ih => cases args <;> simp [parameters, ih]

/-- Exact-arity calls preserve the declared argument order without padding. -/
theorem parameters_exact (args : List Tm) : parameters args.length args = args := by
  induction args with
  | nil => rfl
  | cons a args ih => simp [parameters, ih]

/-- Position i receives actual i if present, otherwise undefined. -/
theorem parameter_at (hi : i < n) :
    (parameters n args)[i]? = some (args[i]?.getD .undef) := by
  induction n generalizing args i with
  | zero => omega
  | succ n ih =>
    cases args <;> cases i <;> simp only [parameters, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    · exact ih (by omega)
    · exact ih (by omega)

theorem parameters_property {P : Tm → Prop} (hu : P .undef)
    (ha : ∀ a ∈ args, P a) : ∀ a ∈ parameters n args, P a := by
  induction n generalizing args with
  | zero => simp [parameters]
  | succ n ih =>
    cases args with
    | nil =>
      intro a hm
      simp only [parameters, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hu
      · exact ih (by simp) a hm
    | cons v args =>
      intro a hm
      simp only [parameters, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ha a (by simp)
      · exact ih (fun a h => ha a (by simp [h])) a hm

theorem bound_body_closed (hb : Scoped arity body)
    (ha : ∀ a ∈ args, Scoped 0 a) : Scoped 0 (bindParameters arity args body) := by
  apply bindArgs_scoped
  · simpa [parameters_length] using hb
  · exact parameters_property (by trivial) ha

theorem prepared_parameters_values {frame : Frame} (hf : frame.ready) : Values (parameters arity frame.args) :=
  parameters_property rfl hf.2

/-- The new binding operation recovers the current unary beta substitution. -/
theorem unary_binding (a body : Tm) : bindParameters 1 [a] body = subst 0 a body := rfl

theorem omitted_unary_binding (body : Tm) :
    bindParameters 1 [] body = subst 0 .undef body := rfl

/-- Dispatch a fully evaluated frame to the code on its saved callee. The
descriptor supplies the parameter count; all actuals, including extras,
must be values before normalization. Invocation itself performs no heap effect. -/
inductive Invoke : Frame → Tm → Prop where
  | closure : Values args →
      Invoke ⟨.obj l (.closure arity body), args⟩ (bindParameters arity args body)

theorem invoke_ready (hi : Invoke frame body) : frame.ready := by
  cases hi with
  | closure hv => exact ⟨rfl, hv⟩

theorem invoke_deterministic (hi : Invoke frame body) (hi' : Invoke frame body') :
    body = body' := by
  cases hi
  cases hi'
  rfl

theorem invoke_no_prepare (hi : Invoke frame body) : ¬ Prepare h frame h' frame' :=
  ready_no_prepare (invoke_ready hi)

/-- Readiness is sufficient for dispatch precisely when the saved callee has
invocation code. No scope or type test is added to the untyped machine. -/
theorem invoke_iff : Invoke frame result ↔
    ∃ l arity body, frame.callee = .obj l (.closure arity body) ∧ Values frame.args ∧
      result = bindParameters arity frame.args body := by
  constructor
  · intro hi
    cases hi with
    | closure hv => exact ⟨_, _, _, rfl, hv, rfl⟩
  · rcases frame with ⟨f, args⟩
    rintro ⟨l, arity, body, hf, hv, rfl⟩
    cases hf
    exact .closure hv

theorem invoke_closed (hi : Invoke frame result) (hf : Scoped 0 frame.callee)
    (ha : ∀ a ∈ frame.args, Scoped 0 a) : Scoped 0 result := by
  cases hi with
  | closure _ => exact bound_body_closed (by simpa [Scoped] using hf) ha

/-- Prepared list dispatch is a step of the maintained term machine. -/
theorem Invoke.step (hi : Invoke frame body) (h : Heap) :
    Step h (.call frame.callee frame.args) h body := by
  cases hi with
  | closure hv => exact .callV hv

/-- A ready native call can only dispatch its saved code, without a heap change. -/
theorem ready_step_iff (hf : frame.ready) :
    Step h (.call frame.callee frame.args) h' body ↔ h' = h ∧ Invoke frame body := by
  rcases frame with ⟨f, args⟩
  constructor
  · intro hs
    cases hs with
    | callL hs => exact False.elim (value_no_step hf.1 hs)
    | callArg _ hg _ hs => exact False.elim (value_no_step (hf.2 _ (List.mem_of_getElem? hg)) hs)
    | callV hv => exact ⟨rfl, .closure hv⟩
  · rintro ⟨rfl, hi⟩
    exact hi.step _

/-- Preparation and native operand reduction are the same transition. -/
theorem Prepare.step (hp : Prepare h frame h' frame') :
    Step h (.call frame.callee frame.args) h' (.call frame'.callee frame'.args) := by
  cases hp with
  | callee hs => exact .callL hs
  | args hv hs =>
    obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
    exact .callArg hv hg hb hstep

/-- Every native call step is preparation or dispatch, and both reconstruct
that same machine step. This includes all argument counts. -/
theorem call_step_iff : Step h (.call f args) h' result ↔
    (∃ frame, Prepare h ⟨f, args⟩ h' frame ∧ result = .call frame.callee frame.args) ∨
    (h' = h ∧ Invoke ⟨f, args⟩ result) := by
  constructor
  · intro hs
    cases hs with
    | callL hs => exact Or.inl ⟨_, .callee hs, rfl⟩
    | callArg hv hg hb hs =>
      exact Or.inl ⟨_, .args hv (focus_iff.mpr ⟨_, _, _, hg, hb, hs, rfl⟩), rfl⟩
    | callV hv => exact Or.inr ⟨rfl, .closure hv⟩
  · rintro (⟨frame, hp, rfl⟩ | ⟨rfl, hi⟩)
    · exact hp.step
    · exact hi.step _

/-- The source pipeline's singleton application view is preserved. -/
theorem unary_step_iff : Step h (.app f a) h' result ↔
    (∃ f' a', Prepare h ⟨f, [a]⟩ h' ⟨f', [a']⟩ ∧ result = .app f' a') ∨
    (h' = h ∧ Invoke ⟨f, [a]⟩ result) := by
  rw [call_step_iff]
  constructor
  · rintro (⟨frame, hp, he⟩ | hi)
    · obtain ⟨f', a', rfl, _⟩ := unary_step hp
      exact Or.inl ⟨f', a', hp, he⟩
    · exact Or.inr hi
  · rintro (⟨f', a', hp, he⟩ | hi)
    · exact Or.inl ⟨_, hp, he⟩
    · exact Or.inr hi

#print axioms parameter_at
#print axioms bound_body_closed
#print axioms prefix_iff
#print axioms deterministic
#print axioms prepare_deterministic
#print axioms unary_step
#print axioms invoke_deterministic
#print axioms invoke_no_prepare
#print axioms invoke_iff
#print axioms invoke_closed
#print axioms focus_iff
#print axioms Prepare.step
#print axioms call_step_iff
#print axioms Invoke.step
#print axioms ready_step_iff
#print axioms unary_step_iff
end Verification.ExperimentState.CallArguments
