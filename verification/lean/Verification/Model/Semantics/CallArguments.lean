import Verification.Model.Semantics.Bindings

/-! Call preparation keeps a callee and an ordered argument list separate from
invocation. It reuses the term machine for operand effects and connects prepared
list preparation and dispatch to native call reduction. Source calling conventions
remain integration work. -/
namespace Verification.Model.CallArguments

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

/-- A call in preparation: the callee, the receiver and the actuals. -/
structure Frame where
  callee : Tm
  recv : Tm
  args : List Tm
  deriving DecidableEq, Repr

/-- Preparation never invokes the callee. No receiver effect happens before the
callee is a value, no argument effect before the receiver is one, and
invocation must wait until every argument is a value. -/
inductive Prepare : Heap → Frame → Heap → Frame → Prop where
  | callee : Step h f h' f' → Prepare h ⟨f,r,args⟩ h' ⟨f',r,args⟩
  | recv : isVal f = true → Step h r h' r' → Prepare h ⟨f,r,args⟩ h' ⟨f,r',args⟩
  | args : isVal f = true → isVal r = true → ArgStep h args h' args' →
      Prepare h ⟨f,r,args⟩ h' ⟨f,r,args'⟩
  /-- A spread whose store is ready, after a completed prefix, becomes the
  store's elements; the heap is only read. -/
  | splice {pre post : List Tm} {ls : List (Option Nat)} {vs : List Tm} :
      isVal f = true → isVal r = true → args = pre ++ .spread (.arr ls) :: post → Values pre →
      readElems h ls = some vs → Prepare h ⟨f,r,args⟩ h ⟨f,r,pre ++ vs ++ post⟩

def Frame.ready (f : Frame) : Prop :=
  isVal f.callee = true ∧ isVal f.recv = true ∧ Values f.args

theorem prepare_deterministic (s : Prepare h f h1 f1) (t : Prepare h f h2 f2) :
    h1 = h2 ∧ f1 = f2 := by
  cases s with
  | callee hs =>
    cases t with
    | callee ht => obtain ⟨rfl,rfl⟩ := Step_det hs ht; exact ⟨rfl,rfl⟩
    | recv hv _ => exact False.elim (value_no_step hv hs)
    | args hv _ _ => exact False.elim (value_no_step hv hs)
    | splice hv _ _ _ _ => exact False.elim (value_no_step hv hs)
  | recv hf hs =>
    cases t with
    | callee ht => exact False.elim (value_no_step hf ht)
    | recv _ ht => obtain ⟨rfl,rfl⟩ := Step_det hs ht; exact ⟨rfl,rfl⟩
    | args _ hr _ => exact False.elim (value_no_step hr hs)
    | splice _ hr _ _ _ => exact False.elim (value_no_step hr hs)
  | args hv hr hs =>
    cases t with
    | callee ht => exact False.elim (value_no_step hv ht)
    | recv _ ht => exact False.elim (value_no_step hr ht)
    | args _ _ ht => obtain ⟨rfl,rfl⟩ := deterministic hs ht; exact ⟨rfl,rfl⟩
    | splice _ _ he hp _ =>
      obtain ⟨i, a, a', hg, hb, ha, -⟩ := focus_iff.mp hs
      exact False.elim (spread_blocks_arg he hp hg hb ha)
  | splice hv hr he hp hre =>
    cases t with
    | callee ht => exact False.elim (value_no_step hv ht)
    | recv _ ht => exact False.elim (value_no_step hr ht)
    | args _ _ ht =>
      obtain ⟨i, a, a', hg, hb, ha, -⟩ := focus_iff.mp ht
      exact False.elim (spread_blocks_arg he hp hg hb ha)
    | splice _ _ he' hp' hre' =>
      obtain ⟨rfl, hx, rfl⟩ := split_unique (he.symm.trans he') hp hp' rfl rfl
      cases hx
      cases Option.some.inj (hre.symm.trans hre')
      exact ⟨rfl, rfl⟩

theorem callee_preserved (hv : isVal f.callee = true) (s : Prepare h f h' f') :
    f'.callee = f.callee := by
  cases s with
  | callee hs => exact False.elim (value_no_step hv hs)
  | recv _ _ => rfl
  | args _ _ _ => rfl
  | splice _ _ _ _ _ => rfl

theorem ready_no_prepare (hf : f.ready) : ¬ Prepare h f h' f' := by
  intro s
  cases s with
  | callee hs => exact value_no_step hf.1 hs
  | recv _ hs => exact value_no_step hf.2.1 hs
  | args _ _ hs => exact values_no_step hf.2.2 hs
  | splice _ _ he _ _ => exact spread_not_values he hf.2.2

/-- Current unary evaluation embeds in this preparation interface before beta,
unless the one actual is a spread, which may stand for any number. -/
theorem unary_step (hn : ∀ x, a ≠ .spread x) (s : Prepare h ⟨f,.undef,[a]⟩ h' frame) :
    ∃ f' a', frame = ⟨f',.undef,[a']⟩ ∧ Step h (.app f a) h' (.app f' a') := by
  cases s with
  | callee hs => exact ⟨_,_,rfl,.appL hs⟩
  | recv _ hs => exact False.elim (value_no_step rfl hs)
  | args hv _ hs =>
    obtain ⟨a',rfl,ha⟩ := singleton.mp hs
    exact ⟨_,_,rfl,.appR hv ha⟩
  | @splice _ _ _ _ pre post ls vs _ _ he _ _ =>
    cases pre with
    | nil => cases he; exact False.elim (hn _ rfl)
    | cons _ pre => cases pre <;> simp at he

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

/-- Trailing `undefined` actuals are exactly what padding already supplies, so a
call that omits them dispatches the same body term as the call that writes them
out. An omitted parameter is therefore not a second binding rule. -/
theorem parameters_pad (n : Nat) (args pad : List Tm) (hp : ∀ a ∈ pad, a = .undef) :
    parameters n (args ++ pad) = parameters n args := by
  induction n generalizing args pad with
  | zero => rfl
  | succ n ih =>
    cases args with
    | nil =>
      cases pad with
      | nil => rfl
      | cons a pad =>
        cases hp a (by simp)
        simp only [List.nil_append, parameters]
        exact congrArg _ (ih [] pad fun v hv => hp v (by simp [hv]))
    | cons a args =>
      simp only [List.cons_append, parameters]
      exact congrArg _ (ih args pad hp)

theorem bindParameters_pad (arity : Nat) (args pad : List Tm) (recv body : Tm)
    (hp : ∀ a ∈ pad, a = .undef) :
    bindParameters arity (args ++ pad) recv body = bindParameters arity args recv body := by
  simp only [bindParameters, parameters_pad arity args pad hp]

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

theorem bound_body_closed (hb : Scoped (arity + 1) body) (hr : Scoped 0 recv)
    (ha : ∀ a ∈ args, Scoped 0 a) : Scoped 0 (bindParameters arity args recv body) := by
  apply bindArgs_scoped
  · simpa [parameters_length, Nat.add_comm] using hb
  · intro a hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hr
    · exact parameters_property (by trivial) ha a hm

theorem prepared_parameters_values {frame : Frame} (hf : frame.ready) : Values (parameters arity frame.args) :=
  parameters_property rfl hf.2.2

/-- The binding operation recovers unary beta substitution, the receiver
bound in slot 0 and the parameter after it. -/
theorem unary_binding (a r body : Tm) :
    bindParameters 1 [a] r body = subst 0 r (subst 1 a body) := rfl

theorem omitted_unary_binding (r body : Tm) :
    bindParameters 1 [] r body = subst 0 r (subst 1 .undef body) := rfl

/-- Initializers of an allocation reduce exactly as actual arguments do. -/
theorem Step.makeArgs {c : CallCode} {ns : List PropKey} {h h' : Heap} {args args' : List Tm}
    (hs : ArgStep h args h' args') : Step h (.makeAt c ns args) h' (.makeAt c ns args') := by
  obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
  exact .makeArg hg hb hstep

/-- The actuals of `new` reduce exactly as a call's do, once the constructor
is a value. -/
theorem Step.constructArgs {h h' : Heap} {f : Tm} {args args' : List Tm} (hf : isVal f = true)
    (hs : ArgStep h args h' args') : Step h (.construct f args) h' (.construct f args') := by
  obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
  exact .constructArg hf hg hb hstep

/-- A store's initializers reduce exactly as actual arguments do. -/
theorem Step.arrArgs {h h' : Heap} {args args' : List Tm}
    (hs : ArgStep h args h' args') : Step h (.arrLit args) h' (.arrLit args') := by
  obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
  exact .arrArg hg hb hstep

/-- Dispatch a fully evaluated frame to the code on its saved callee. The
descriptor supplies the parameter count; the receiver and all actuals,
including extras, must be values before normalization. Invocation itself
performs no heap effect. -/
inductive Invoke : Frame → Tm → Prop where
  | closure : isVal r = true → Values args →
      Invoke ⟨.objAt fs (.closure arity body), r, args⟩ (bindParameters arity args r body)
  | variadic : isVal r = true → Values args →
      Invoke ⟨.objAt fs (.variadic fixed body), r, args⟩ (bindRest fixed args r body)
  /-- A forwarding descriptor yields the target's call: the saved receiver in
  place of this one, the saved prefix before these actuals. -/
  | bound : isVal r = true → Values args →
      Invoke ⟨.objAt fs (.bound target r₀ pre), r, args⟩ (.invoke target r₀ (pre ++ args))

/-- The term each kind of code yields for a ready receiver and argument list. -/
def dispatch : CallCode → Tm → List Tm → Option Tm
  | .closure arity body, r, args => some (bindParameters arity args r body)
  | .variadic fixed body, r, args => some (bindRest fixed args r body)
  | .bound target r₀ pre, _, args => some (.invoke target r₀ (pre ++ args))
  -- A class constructor's plain call throws: nothing runs.
  | .closure _ _ .construct, _, _ => none
  | .absent, _, _ => none

theorem invoke_ready (hi : Invoke frame body) : frame.ready := by
  cases hi with
  | closure hr hv => exact ⟨rfl, hr, hv⟩
  | variadic hr hv => exact ⟨rfl, hr, hv⟩
  | bound hr hv => exact ⟨rfl, hr, hv⟩

theorem invoke_deterministic (hi : Invoke frame body) (hi' : Invoke frame body') :
    body = body' := by
  cases hi <;> cases hi' <;> rfl

theorem invoke_no_prepare (hi : Invoke frame body) : ¬ Prepare h frame h' frame' :=
  ready_no_prepare (invoke_ready hi)

/-- Readiness is sufficient for dispatch precisely when the saved callee has
invocation code. No scope or type test is added to the untyped machine. -/
theorem invoke_iff : Invoke frame result ↔
    ∃ fs code, frame.callee = .objAt fs code ∧ isVal frame.recv = true ∧ Values frame.args ∧
      dispatch code frame.recv frame.args = some result := by
  constructor
  · intro hi
    cases hi with
    | closure hr hv => exact ⟨_, _, rfl, hr, hv, rfl⟩
    | variadic hr hv => exact ⟨_, _, rfl, hr, hv, rfl⟩
    | bound hr hv => exact ⟨_, _, rfl, hr, hv, rfl⟩
  · rcases frame with ⟨f, r, args⟩
    rintro ⟨fs, code, hf, hr, hv, hd⟩
    cases hf
    cases code with
    | absent => cases hd
    | closure arity body kind => cases kind <;> cases hd; exact .closure hr hv
    | variadic fixed body => cases hd; exact .variadic hr hv
    | bound target r₀ pre => cases hd; exact .bound hr hv

theorem invoke_closed (hi : Invoke frame result) (hf : Scoped 0 frame.callee)
    (hr : Scoped 0 frame.recv) (ha : ∀ a ∈ frame.args, Scoped 0 a) : Scoped 0 result := by
  cases hi with
  | closure _ _ => exact bound_body_closed (by simpa [Scoped] using hf) hr ha
  | @variadic r args fs fixed body _ _ =>
    refine ⟨?_, ?_⟩
    · simp only [Scoped, scopedArgs_iff]
      intro a hm
      exact ha a (List.mem_of_mem_drop hm)
    · apply bindArgs_scoped
      · have hb : Scoped (0 + fixed + 2) body := by simpa [Scoped] using hf
        simp only [List.length_cons, parameters_length]
        simpa [Nat.add_comm, Nat.add_left_comm] using hb
      · intro a hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hr
        · exact parameters_property (by trivial) ha a hm
  | bound _ _ =>
    simp only [Scoped, scopedArgs_iff] at hf ⊢
    refine ⟨hf.1, hf.2.1, fun a hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact hf.2.2 a hm
    · exact ha a hm

/-- Prepared list dispatch is a step of the maintained term machine. -/
theorem Invoke.step (hi : Invoke frame body) (h : Heap) :
    Step h (.invoke frame.callee frame.recv frame.args) h body := by
  cases hi with
  | closure hr hv => exact .callV hr hv
  | variadic hr hv => exact .callRest hr hv
  | bound hr hv => exact .callBound hr hv

/-- A ready native call can only dispatch its saved code, without a heap change. -/
theorem ready_step_iff (hf : frame.ready) :
    Step h (.invoke frame.callee frame.recv frame.args) h' body ↔ h' = h ∧ Invoke frame body := by
  rcases frame with ⟨f, r, args⟩
  constructor
  · intro hs
    cases hs with
    | callL hs => exact False.elim (value_no_step hf.1 hs)
    | callRecv _ hs => exact False.elim (value_no_step hf.2.1 hs)
    | callArg _ _ hg _ hs =>
      exact False.elim (value_no_step (hf.2.2 _ (List.mem_of_getElem? hg)) hs)
    | callV hr hv => exact ⟨rfl, .closure hr hv⟩
    | callRest hr hv => exact ⟨rfl, .variadic hr hv⟩
    | callBound hr hv => exact ⟨rfl, .bound hr hv⟩
    | callSpread _ _ he _ _ => exact False.elim (spread_not_values he hf.2.2)
  · rintro ⟨rfl, hi⟩
    exact hi.step _

/-- Preparation and native operand reduction are the same transition. -/
theorem Prepare.step (hp : Prepare h frame h' frame') :
    Step h (.invoke frame.callee frame.recv frame.args) h'
      (.invoke frame'.callee frame'.recv frame'.args) := by
  cases hp with
  | callee hs => exact .callL hs
  | recv hv hs => exact .callRecv hv hs
  | args hv hr hs =>
    obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
    exact .callArg hv hr hg hb hstep
  | splice hv hr he hp hre => exact .callSpread hv hr he hp hre

/-- Every native call step is preparation or dispatch, and both reconstruct
that same machine step. This includes all argument counts. -/
theorem call_step_iff : Step h (.invoke f r args) h' result ↔
    (∃ frame, Prepare h ⟨f, r, args⟩ h' frame ∧
      result = .invoke frame.callee frame.recv frame.args) ∨
    (h' = h ∧ Invoke ⟨f, r, args⟩ result) := by
  constructor
  · intro hs
    cases hs with
    | callL hs => exact Or.inl ⟨_, .callee hs, rfl⟩
    | callRecv hv hs => exact Or.inl ⟨_, .recv hv hs, rfl⟩
    | callArg hv hr hg hb hs =>
      exact Or.inl ⟨_, .args hv hr (focus_iff.mpr ⟨_, _, _, hg, hb, hs, rfl⟩), rfl⟩
    | callV hr hv => exact Or.inr ⟨rfl, .closure hr hv⟩
    | callRest hr hv => exact Or.inr ⟨rfl, .variadic hr hv⟩
    | callBound hr hv => exact Or.inr ⟨rfl, .bound hr hv⟩
    | callSpread hv hr he hp hre => exact Or.inl ⟨_, .splice hv hr he hp hre, rfl⟩
  · rintro (⟨frame, hp, rfl⟩ | ⟨rfl, hi⟩)
    · exact hp.step
    · exact hi.step _

/-- The source pipeline's singleton application view is preserved. -/
theorem unary_step_iff (hn : ∀ x, a ≠ .spread x) : Step h (.app f a) h' result ↔
    (∃ f' a', Prepare h ⟨f, .undef, [a]⟩ h' ⟨f', .undef, [a']⟩ ∧ result = .app f' a') ∨
    (h' = h ∧ Invoke ⟨f, .undef, [a]⟩ result) := by
  rw [call_step_iff]
  constructor
  · rintro (⟨frame, hp, he⟩ | hi)
    · obtain ⟨f', a', rfl, _⟩ := unary_step hn hp
      exact Or.inl ⟨f', a', hp, he⟩
    · exact Or.inr hi
  · rintro (⟨f', a', hp, he⟩ | hi)
    · exact Or.inl ⟨_, hp, he⟩
    · exact Or.inr hi

/-- A forwarding descriptor yields the same term whatever receiver it is
invoked with: the saved one replaces it. -/
theorem bound_ignores_receiver {fs t r₀ pre r r' args result result'}
    (hi : Invoke ⟨.objAt fs (.bound t r₀ pre), r, args⟩ result)
    (hi' : Invoke ⟨.objAt fs (.bound t r₀ pre), r', args⟩ result') :
    result = .invoke t r₀ (pre ++ args) ∧ result' = result := by
  cases hi; cases hi'; exact ⟨rfl, rfl⟩

/-- Binding a bound function keeps the first receiver and both prefixes, in
order: the outer descriptor forwards to the inner one, which supplies its own
saved receiver. -/
theorem rebind_keeps_receiver {h : Heap} {fs gs t r₀ r₁ p₀ p₁ r args}
    (hr : isVal r = true) (hr₁ : isVal r₁ = true) (hv : Values args) (hp₁ : Values p₁) :
    Step h (.invoke (.objAt gs (.bound (.objAt fs (.bound t r₀ p₀)) r₁ p₁)) r args) h
        (.invoke (.objAt fs (.bound t r₀ p₀)) r₁ (p₁ ++ args)) ∧
      Step h (.invoke (.objAt fs (.bound t r₀ p₀)) r₁ (p₁ ++ args)) h
        (.invoke t r₀ (p₀ ++ (p₁ ++ args))) := by
  refine ⟨.callBound hr hv, .callBound hr₁ ?_⟩
  intro a hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hp₁ a hm
  · exact hv a hm

#print axioms bound_ignores_receiver
#print axioms rebind_keeps_receiver
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
end Verification.Model.CallArguments
