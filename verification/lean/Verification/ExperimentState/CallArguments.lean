import Verification.ExperimentState.Language

/-! Call preparation keeps a callee and an ordered argument list separate from
invocation. It reuses the term machine for operand effects. This is the
operational interface for argument-list integration, not yet a source calling
convention or a replacement for the current unary beta rule. -/
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

-- A stuck first argument blocks a later write; readiness does not itself
-- assert callability (a primitive callee still has to fail at invocation).
example : ¬ ArgStep [.tru] [.app .nul .nul, .write (.obj 0 .absent) .fls] h' args' := by
  intro s
  cases s with
  | head hs => exact stuck_no_step hs
  | tail hv _ => simp [isVal] at hv

example : (Frame.mk .nul []).ready := ⟨rfl,by simp [Values]⟩

#print axioms prefix_iff
#print axioms deterministic
#print axioms prepare_deterministic
#print axioms unary_step
end Verification.ExperimentState.CallArguments
