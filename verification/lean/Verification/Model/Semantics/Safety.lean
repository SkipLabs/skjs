import Verification.Model.Semantics.CallArguments
import Verification.Model.Semantics.Heaps
/-!
# Safety and function types

`Safe T n W h t` says that running `t` for `n` steps never gets stuck, and that
if it reaches a value with budget left, that value is in `T`. Each step spends a
level and the world drops with it; the world reached after a step must extend the
truncation of the one before, and must itself be admissible.

A function type requires an object with closed invocation code whose substituted body is safe in
every *future* world and every heap satisfying
it, at every strictly smaller budget. Requiring admissibility here is what lets a
function allocate: without it, a world carrying a contract like `badCtr` could be
supplied, and no allocating function would be safe anywhere.

The level a call spends is the level at which the argument's own guarantees are
available. That correspondence is what makes ordinary typing derivations go
through, and it is why the arrow is stated over `Safe` rather than over an
abstract relation from arguments to results.

Since safety consults a type only at the budgets it can still reach, an arrow
reads **both** of its operands strictly below the current budget. So a function
type is a guard in its result as well as its argument, and a recursion may run
through either position.
-/
namespace Verification
namespace Model

/-- Running `t` for `n` steps never gets stuck; each step spends a level, and
the world drops with it. -/
def Safe (T : Fam) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n + 1, W, h, t =>
      (isVal t = true ∧ T (n + 1) W t) ∨
      (∃ (W' : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) W' ∧ WorldAdm W' ∧ Step h t h' t' ∧
          HeapOk n W' h' ∧ Safe T n W' h' t')

theorem Safe_nul : ∀ (n : Nat) (W : WorldT n) (h : Heap), Safe nulT n W h .nul
  | 0, _, _ => trivial
  | _ + 1, _, _ => Or.inl ⟨rfl, rfl⟩

/-- The body executed after a unary call's beta step, whose receiver is
`undefined`. This is a semantic helper, not an additional runtime operation.
Arrow membership separately requires a callable shape, so the fallback branch
is never used for typed application. -/
def callBody (v a : Tm) : Tm := match v with
  | .objAt _ (.closure n b) => CallArguments.bindParameters n [a] .undef b
  | _ => .app .nul .nul

/-- Only an object with closed invocation code is a callable value. The body
is scoped under its parameters and the receiver. -/
def Callable (v : Val) : Prop :=
  ∃ arity b fs, v = .objAt fs (.closure arity b) ∧ Scoped (arity + 1) b

theorem Callable.val {v : Val} (h : Callable v) : isVal v = true := by
  rcases h with ⟨arity, b, l, rfl, _⟩; rfl

theorem Callable.scoped {v : Val} (h : Callable v) : Scoped 0 v := by
  rcases h with ⟨arity, b, l, rfl, hc⟩; simpa [Scoped] using hc

theorem Callable.step {v a : Val} (h : Callable v) (ha : isVal a = true) (heap : Heap) :
    Step heap (.app v a) heap (callBody v a) := by
  rcases h with ⟨arity, b, l, rfl, _⟩
  exact .beta ha

/-- `A → B` contains closed callables whose substituted bodies are safe in every
future world and satisfying heap, at every strictly smaller level. The actual
application pays beta before using this body guarantee. -/
def arrowT (A B : Fam) : Fam := fun k W v =>
  Callable v ∧
    ∀ (j : Nat) (hj : j < k) (W' : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) W' →
      WorldAdm W' → ∀ (h : Heap), HeapOk j W' h → ∀ a, A j W' a → Safe B j W' h (callBody v a)

theorem arrowT_contractive (B : Fam) : Contractive (fun X => arrowT X B) := by
  intro n T U hag W v
  simp only [arrowT]
  constructor <;> rintro ⟨hl, h⟩ <;> refine ⟨hl, ?_⟩ <;>
      intro j hj W' hW hadm hp hok a ha
  · exact h j hj W' hW hadm hp hok a ((hag j hj W' a).mpr ha)
  · exact h j hj W' hW hadm hp hok a ((hag j hj W' a).mp ha)

/-- Safety depends on the type only through its behaviour at the budgets it can
still reach. -/
theorem Safe_congr {B C : Fam} (n : Nat) (hag : Agree B C n) :
    ∀ (j : Nat), j < n → ∀ (W : WorldT j) (h : Heap) (t : Tm),
      Safe B j W h t ↔ Safe C j W h t := by
  intro j
  induction j with
  | zero => intro _ _ _ _; exact Iff.rfl
  | succ p ih =>
    intro hj W h t
    simp only [Safe]
    constructor <;> rintro (⟨hv, hB⟩ | ⟨W', h', t', hx, ha, hs, hok, hsafe⟩)
    · exact Or.inl ⟨hv, (hag (p + 1) hj W t).mp hB⟩
    · exact Or.inr ⟨W', h', t', hx, ha, hs, hok, (ih (by omega) W' h' t').mp hsafe⟩
    · exact Or.inl ⟨hv, (hag (p + 1) hj W t).mpr hB⟩
    · exact Or.inr ⟨W', h', t', hx, ha, hs, hok, (ih (by omega) W' h' t').mpr hsafe⟩

/-- Safety is monotone in the type, at every budget it can still reach. -/
theorem Safe_mono {B C : Fam} : ∀ (j : Nat),
    (∀ m, m ≤ j → ∀ (W : WorldT m) (v : Val), B m W v → C m W v) →
    ∀ (W : WorldT j) (h : Heap) (t : Tm), Safe B j W h t → Safe C j W h t := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _; trivial
  | succ p ih =>
    intro hbc W h t hs
    rcases hs with ⟨hv, hB⟩ | ⟨W', h', t', hx, ha, hst, hok, hsafe⟩
    · exact Or.inl ⟨hv, hbc (p + 1) (Nat.le_refl _) W t hB⟩
    · exact Or.inr ⟨W', h', t', hx, ha, hst, hok,
        ih (fun m hm => hbc m (by omega)) W' h' t' hsafe⟩

/-- An arrow is a guard in its **result** as well as its argument, so a
recursive type may run through either position. -/
theorem arrowT_cod_contractive (A : Fam) : Contractive (fun X => arrowT A X) := by
  intro n T U hag W v
  simp only [arrowT]
  constructor <;> rintro ⟨hl, hh⟩ <;> refine ⟨hl, ?_⟩ <;>
      intro j hj W'' hW hadm hp hok a ha
  · exact (Safe_congr n hag j hj W'' hp _).mp (hh j hj W'' hW hadm hp hok a ha)
  · exact (Safe_congr n hag j hj W'' hp _).mpr (hh j hj W'' hW hadm hp hok a ha)

/-- **Arrow types are admissible.** -/
theorem arrowT_adm (A B : Fam) : Adm (arrowT A B) := by
  constructor
  · rintro n W v ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro j hj W' hW hadm hp hok a ha
    refine h j (by omega) W' ?_ hadm hp hok a ha
    rwa [trunc_trunc] at hW
  · rintro n W W' hx v ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro j hj W'' hW hadm hp hok a ha
    exact h j hj W'' (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hW) hadm hp hok a ha

theorem arrowT_valOnly (A B : Fam) : ValOnly (arrowT A B) := by
  rintro _ _ _ ⟨hc, -⟩; exact hc.val

/-! ## Unions and the arrow

A union in the domain splits into an intersection of arrows. This equation
supports domain normalization. Unrestricted distribution in the result position
is not assumed. -/

theorem arrowT_union_dom (A B C : Fam) (k : Nat) (W : WorldT k) (v : Val) :
    arrowT (unionT A B) C k W v ↔ interT (arrowT A C) (arrowT B C) k W v := by
  simp only [arrowT, interT, unionT]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨⟨hl, ?_⟩, ⟨hl, ?_⟩⟩
    · intro j hj W' hW hadm hp hok a ha
      exact h j hj W' hW hadm hp hok a (Or.inl ha)
    · intro j hj W' hW hadm hp hok a ha
      exact h j hj W' hW hadm hp hok a (Or.inr ha)
  · rintro ⟨⟨hl, hA⟩, ⟨_, hB⟩⟩
    refine ⟨hl, ?_⟩
    intro j hj W' hW hadm hp hok a ha
    rcases ha with h | h
    · exact hA j hj W' hW hadm hp hok a h
    · exact hB j hj W' hW hadm hp hok a h

/-! ## Comparing two runs of one program

Two obligations discharged at the same world and heap are two runs of the *same*
program, so determinism makes them take the same steps. What they force about
the value it may return is then whatever both judgments force at the first
world — and no more, since the worlds diverge as soon as anything is allocated.
The subtype rules use a conservative syntactic sufficient condition for this
property. `ModelBoundaries.lean` records why unrestricted result intersection
is invalid; no decision procedure for exact cross-world compatibility is assumed. -/

def CrossCompatUpTo (n : Nat) (B C D : Fam) : Prop :=
  ∀ (j : Nat), j ≤ n → ∀ (W W' : WorldT j) (h : Heap), HeapOk j W h → HeapOk j W' h →
    ∀ (u : Val), B j W u → C j W' u → D j W u

theorem safe_cross_upto {B C D : Fam} : ∀ (n : Nat), CrossCompatUpTo n B C D →
    ∀ (W W' : WorldT n) (h : Heap) (t : Tm), HeapOk n W h → HeapOk n W' h →
      Safe B n W h t → Safe C n W' h t → Safe D n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _; trivial
  | succ p ih =>
    intro hc W W' h t hok hok'
    rintro (⟨hv1, hBv⟩ | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩)
      (⟨hv2, hCv⟩ | ⟨Z', h2, t2, -, -, hst2, hok2, hcont2⟩)
    · exact Or.inl ⟨hv1, hc (p + 1) (Nat.le_refl _) W W' h hok hok' t hBv hCv⟩
    · exact absurd hst2 (value_no_step hv1)
    · exact absurd hst1 (value_no_step hv2)
    · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
      exact Or.inr ⟨Z, h1, t1, hz, huz, hst1, hok1,
        ih (fun j hj => hc j (by omega)) Z Z' h1 t1 hok1 hok2 hcont1 hcont2⟩

/-! ## Overloaded function types

The intersection of finitely many arrows, with the shared callable-shape
condition factored out. `arrowsT [(A, B)]` is `arrowT A B`, and `arrowsT []` is
the type of all functions. This is the node a representation carrying
intersections has to have, so it comes with the same structural properties the
fixed point needs of `arrowT`. -/

def arrowsT (L : List (Fam × Fam)) : Fam := fun k W v =>
  Callable v ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
    WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' → ∀ (h : Heap), HeapOk j W' h →
      ∀ a, p.1 j W' a → Safe p.2 j W' h (callBody v a)

theorem arrowsT_singleton (A B : Fam) (k : Nat) (W : WorldT k) (v : Val) :
    arrowsT [(A, B)] k W v ↔ arrowT A B k W v := by
  constructor
  · rintro ⟨hl, h⟩
    exact ⟨hl, fun j hj W' hx hu hp hh a ha => h (A, B) (by simp) j hj W' hx hu hp hh a ha⟩
  · rintro ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro p hp
    rw [List.mem_singleton.mp hp]
    exact fun j hj W' hx hu hh hok a ha => h j hj W' hx hu hh hok a ha

/-- Membership in every conjunct is membership in the intersection. -/
theorem arrowsT_of_all {L : List (Fam × Fam)} {k : Nat} {W : WorldT k} {v : Val} {b : Tm}
    {fs : List (PropKey × Nat)}
    (hobj : v = .objAt fs (.closure 1 b)) (hclosed : Scoped 2 b) (h : ∀ p ∈ L, arrowT p.1 p.2 k W v) : arrowsT L k W v :=
  ⟨⟨1, b, fs, hobj, hclosed⟩, fun p hp j hj W' hx hu hp' hok a ha => (h p hp).2 j hj W' hx hu hp' hok a ha⟩

theorem arrowsT_valOnly (L : List (Fam × Fam)) : ValOnly (arrowsT L) := by
  rintro j W a ⟨hc, -⟩
  exact hc.val

/-- Ordered actual-argument contracts. The signature fixes the actual count;
the code's declared parameter count is independent. -/
def ArgsT : List Fam → (k : Nat) → WorldT k → List Tm → Prop
  | [], _, _, [] => True
  | A :: As, k, W, a :: args => A k W a ∧ ArgsT As k W args
  | _, _, _, _ => False

/-- An actual is at its position's contract. -/
theorem ArgsT_getElem? : ∀ {As : List Fam} {k : Nat} {W : WorldT k} {args : List Tm} {i : Nat}
    {A : Fam} {a : Tm}, ArgsT As k W args → As[i]? = some A → args[i]? = some a → A k W a
  | [], _, _, _, _, _, _, _, hA, _ => by simp at hA
  | _ :: _, _, _, [], _, _, _, h, _, _ => h.elim
  | _ :: _, _, _, _ :: _, 0, _, _, h, hA, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hA ha
    subst hA; subst ha; exact h.1
  | _ :: _, _, _, _ :: _, i + 1, _, _, h, hA, ha => by
    simp only [List.getElem?_cons_succ] at hA ha
    exact ArgsT_getElem? h.2 hA ha

/-- Actuals at their positions' contracts, as many as the positions, are
admitted position by position. -/
theorem ArgsT_of_getElem? : ∀ {As : List Fam} {k : Nat} {W : WorldT k} {args : List Tm},
    As.length = args.length →
    (∀ (i : Nat) (A : Fam) (a : Tm), As[i]? = some A → args[i]? = some a → A k W a) →
    ArgsT As k W args
  | [], _, _, [], _, _ => trivial
  | [], _, _, _ :: _, hl, _ => by simp at hl
  | _ :: _, _, _, [], hl, _ => by simp at hl
  | A :: As, _, _, a :: args, hl, h =>
    ⟨h 0 A a rfl rfl, ArgsT_of_getElem? (by simpa using hl) fun i B b hB hb => h (i + 1) B b hB hb⟩

theorem ArgsT_singleton (A : Fam) (k : Nat) (W : WorldT k) (args : List Tm) :
    ArgsT [A] k W args ↔ ∃ a, args = [a] ∧ A k W a := by
  cases args with
  | nil => simp [ArgsT]
  | cons a args =>
    cases args <;> simp [ArgsT]

theorem ArgsT_length {As k W args} (h : ArgsT As k W args) :
    args.length = As.length := by
  induction As generalizing args with
  | nil => cases args <;> simp_all [ArgsT]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args => exact congrArg Nat.succ (ih h.2)

theorem ArgsT_append {As Bs : List Fam} {k W args brgs}
    (h : ArgsT As k W args) (h' : ArgsT Bs k W brgs) :
    ArgsT (As ++ Bs) k W (args ++ brgs) := by
  induction As generalizing args with
  | nil => cases args with
    | nil => exact h'
    | cons a args => exact False.elim h
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args => exact ⟨h.1, ih h.2⟩

/-- Contracts that admit `undefined` are satisfied by the slots a short call
leaves for the machine to pad. -/
theorem ArgsT_undef {Us : List Fam} {k W} (h : ∀ A ∈ Us, A k W .undef) :
    ArgsT Us k W (List.replicate Us.length .undef) := by
  induction Us with
  | nil => trivial
  | cons A Us ih =>
    exact ⟨h A (by simp), ih fun B hB => h B (by simp [hB])⟩

/-- Argument membership is covariant pointwise. This is the list-shaped
premise used by callable subtyping: an implementation accepting `Bs` can be
used where callers supply the narrower `As` when every `A ≤ B`. -/
inductive ArgsLe : List Fam → List Fam → Prop where
  | nil : ArgsLe [] []
  | cons : FamLe A B → ArgsLe As Bs → ArgsLe (A :: As) (B :: Bs)

theorem ArgsT_mono {As Bs : List Fam} (h : ArgsLe As Bs) {k W args}
    (ha : ArgsT As k W args) : ArgsT Bs k W args := by
  induction h generalizing args with
  | nil =>
    cases args <;> exact ha
  | cons hab _ ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args => exact ⟨hab k W a ha.1, ih ha.2⟩

/-- Position by position, which is what an allocation needs. -/
theorem ArgsT_zip {As k W args} (h : ArgsT As k W args) :
    ∀ p ∈ As.zip args, p.1 k W p.2 := by
  induction As generalizing args with
  | nil =>
    cases args <;> simp_all [ArgsT]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args =>
      intro p hp
      rw [List.zip_cons_cons] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h.1
      · exact ih h.2 p hp

/-- Typed actuals are ready for binding when their domains contain only values. -/
theorem ArgsT_values {As k W args} (hA : ∀ A ∈ As, ValOnly A)
    (h : ArgsT As k W args) : CallArguments.Values args := by
  induction As generalizing args with
  | nil =>
    cases args with
    | nil => intro a ha; cases ha
    | cons a args => exact False.elim h
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hA A (by simp) k W _ h.1
      · exact ih (fun B hb => hA B (List.mem_cons_of_mem A hb)) h.2 v hv

/-- Saved actual values retain their domains as evaluation spends budget and
extends the heap world. No argument is re-evaluated during this transfer. -/
theorem ArgsT_transfer {As n W args} (hA : ∀ A ∈ As, Adm A)
    (ha : ArgsT As n W args) (j : Nat) (hj : j ≤ n) (U : WorldT j)
    (hx : WExt (trunc j hj W) U) : ArgsT As j U args := by
  induction As generalizing args with
  | nil => cases args <;> exact ha
  | cons A As ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args =>
      have hadm := hA A (by simp)
      exact ⟨hadm.mono j _ U hx a (hadm.down_le n j hj W a ha.1),
        ih (fun B hb => hA B (List.mem_cons_of_mem A hb)) ha.2⟩

inductive ArgsAgree (n : Nat) : List Fam → List Fam → Prop where
  | nil : ArgsAgree n [] []
  | cons : Agree A B n → ArgsAgree n As Bs → ArgsAgree n (A :: As) (B :: Bs)

/-- Agreement follows argument positions, including the actual-list length. -/
theorem ArgsT_congr {As Bs : List Fam} {n : Nat}
    (h : ArgsAgree n As Bs)
    {j : Nat} (hj : j < n) (W : WorldT j) (args : List Tm) :
    ArgsT As j W args ↔ ArgsT Bs j W args := by
  induction h generalizing args with
  | nil => rfl
  | cons hd ht ih =>
    cases args with
    | nil => rfl
    | cons a args => exact and_congr (hd j hj W a) (ih args)

/-- A code contract checks the normalized parameter list and the receiver
after they have been evaluated. Each signature admits its own receiver
contract and list of actual argument types. -/
def InvocationSpec (arity : Nat) (L : List (Fam × List Fam × Fam))
    (k : Nat) (W : WorldT k) (b : Tm) : Prop :=
  Scoped (arity + 1) b ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
    WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' → ∀ (h : Heap), HeapOk j W' h →
      ∀ r, p.1 j W' r → ∀ args, ArgsT p.2.1 j W' args →
        Safe p.2.2 j W' h (CallArguments.bindParameters arity args r b)

theorem InvocationSpec.down {arity L n W b} (h : InvocationSpec arity L (n + 1) W b) :
    InvocationSpec arity L n (trunc n (Nat.le_succ n) W) b := by
  refine ⟨h.1, ?_⟩
  intro p hp j hj U hx hu heap hh r hr args ha
  exact h.2 p hp j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh r hr args ha

theorem InvocationSpec.mono {arity L n W W' b} (hx : WExt W W')
    (h : InvocationSpec arity L n W b) : InvocationSpec arity L n W' b := by
  refine ⟨h.1, ?_⟩
  intro p hp j hj U hy hu heap hh r hr args ha
  exact h.2 p hp j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh r hr args ha

/-- Dispatch realizes the code contract in a future world. The actual list
can be empty or differ in length from the declared parameters, provided
the selected signature admits it. Operand effects have finished before dispatch. -/
theorem InvocationSpec.invoke {arity L k W b} (hs : InvocationSpec arity L k W b)
    {p : Fam × List Fam × Fam} (hp : p ∈ L) {j : Nat} (hj : j < k) {U : WorldT j}
    (hx : WExt (trunc j (Nat.le_of_lt hj) W) U) (hu : WorldAdm U)
    {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : p.1 j U r)
    {args : List Tm} (ha : ArgsT p.2.1 j U args)
    {fs : List (PropKey × Nat)} {result : Tm}
    (hi : CallArguments.Invoke ⟨.objAt fs (.closure arity b), r, args⟩ result) :
    Safe p.2.2 j U heap result := by
  cases hi
  exact hs.2 p hp j hj U hx hu heap hh r hr args ha

/-- Callable values with ordered argument-list signatures. The descriptor's
parameter count is independent of every overload's admitted actual count. -/
def codeCallsT (L : List (Fam × List Fam × Fam)) : Fam := fun k W v =>
  ∃ arity b fs, v = .objAt fs (.closure arity b) ∧ InvocationSpec arity L k W b

theorem codeCallsT_code_iff (L : List (Fam × List Fam × Fam)) (arity : Nat)
    (fs : List (PropKey × Nat)) (b : Tm) (n W) :
    codeCallsT L n W (.objAt fs (.closure arity b)) ↔ InvocationSpec arity L n W b := by
  constructor
  · rintro ⟨arity', b', fs', he, hs⟩
    cases he
    exact hs
  · intro hs
    exact ⟨arity, b, fs, rfl, hs⟩

theorem codeCallsT_callable {L n W v} (h : codeCallsT L n W v) : Callable v := by
  obtain ⟨arity, b, l, hv, hs⟩ := h
  exact ⟨arity, b, l, hv, hs.1⟩

/-- Collect signature obligations on the same immutable callable descriptor. -/
theorem codeCallsT_of_signatures {L n W v} (hc : Callable v)
    (hs : ∀ p ∈ L, codeCallsT [p] n W v) : codeCallsT L n W v := by
  obtain ⟨arity, body, loc, rfl, hscope⟩ := hc
  refine ⟨arity, body, loc, rfl, hscope, ?_⟩
  intro p hp
  exact ((codeCallsT_code_iff [p] arity loc body n W).mp (hs p hp)).2 p (by simp)

theorem codeCallsT_select {L n W v p} (hf : codeCallsT L n W v) (hp : p ∈ L) :
    codeCallsT [p] n W v := by
  obtain ⟨arity, body, loc, he, hc, hs⟩ := hf
  refine ⟨arity, body, loc, he, hc, ?_⟩
  intro q hq; cases List.mem_singleton.mp hq; exact hs p hp

theorem codeCallsT_adm (L : List (Fam × List Fam × Fam)) : Adm (codeCallsT L) := by
  constructor
  · rintro n W v ⟨arity, b, l, hv, hs⟩
    exact ⟨arity, b, l, hv, hs.down⟩
  · rintro n W U hx v ⟨arity, b, l, hv, hs⟩
    exact ⟨arity, b, l, hv, hs.mono hx⟩

/-- A callable signature is contravariant in its receiver and its ordered
arguments and covariant in its result. This is semantic inclusion,
independently of any syntactic subtype checker that may use it. -/
theorem codeCallsT_single_mono {Rc Qc : Fam} {Ps Qs : List Fam} {R T : Fam}
    (hrecv : FamLe Qc Rc) (hdom : ArgsLe Qs Ps) (hresult : FamLe R T) :
    FamLe (codeCallsT [(Rc, Ps, R)]) (codeCallsT [(Qc, Qs, T)]) := by
  intro k W v hv
  obtain ⟨arity, body, fields, heq, hscope, hcall⟩ := hv
  refine ⟨arity, body, fields, heq, hscope, ?_⟩
  intro signature hsignature j hj U hx hu heap hh r hr args hargs
  have hs : signature = (Qc, Qs, T) := List.mem_singleton.mp hsignature
  subst signature
  have source := hcall (Rc, Ps, R) (by simp) j hj U hx hu heap hh r (hrecv j U r hr) args
    (ArgsT_mono hdom hargs)
  exact Safe_mono j (fun m _ => hresult m) U heap _ source

/-- List signatures guard the receiver, every domain position and the result.
This is the congruence needed to interpret recursive call types in the
existing tower. -/
theorem codeCallsT_congr {α : Type} (l : List α) (f g : α → Fam × List Fam × Fam) {n : Nat}
    (h : ∀ x ∈ l, Agree (f x).1 (g x).1 n ∧
      ArgsAgree n (f x).2.1 (g x).2.1 ∧ Agree (f x).2.2 (g x).2.2 n)
    (W : WorldT n) (v : Val) : codeCallsT (l.map f) n W v ↔ codeCallsT (l.map g) n W v := by
  constructor <;> rintro ⟨arity, b, loc, hv, hc, hs⟩ <;>
    refine ⟨arity, b, loc, hv, hc, ?_⟩ <;> intro p hp j hj U hx hu heap hh r hr args ha
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hrc, hd, hres⟩ := h x hm
    have hr' : Agree (f x).2.2 (g x).2.2 (j + 1) := fun k hk V a => hres k (by omega) V a
    exact (Safe_congr (j + 1) hr' j (by omega) U heap _).mp
      (hs (f x) (List.mem_map_of_mem hm) j hj U hx hu heap hh r ((hrc j hj U r).mpr hr) args
        ((ArgsT_congr hd hj U args).mpr ha))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hrc, hd, hres⟩ := h x hm
    have hr' : Agree (f x).2.2 (g x).2.2 (j + 1) := fun k hk V a => hres k (by omega) V a
    exact (Safe_congr (j + 1) hr' j (by omega) U heap _).mpr
      (hs (g x) (List.mem_map_of_mem hm) j hj U hx hu heap hh r ((hrc j hj U r).mp hr) args
        ((ArgsT_congr hd hj U args).mp ha))

/-- Typed callable values dispatch to a safe body at the next observation
budget. Readiness follows from the argument domains containing only values. -/
theorem codeCallsT_invoke {L k W v} (hf : codeCallsT L k W v)
    {p : Fam × List Fam × Fam} (hp : p ∈ L) {j : Nat} (hj : j < k) {U : WorldT j}
    (hx : WExt (trunc j (Nat.le_of_lt hj) W) U) (hu : WorldAdm U)
    {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hrv : isVal r = true) (hr : p.1 j U r)
    {args : List Tm} (hA : ∀ A ∈ p.2.1, ValOnly A) (ha : ArgsT p.2.1 j U args) :
    ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧ Safe p.2.2 j U heap result := by
  obtain ⟨arity, b, fs, rfl, hs⟩ := hf
  have hi := CallArguments.Invoke.closure (fs := fs) (body := b) (arity := arity) hrv
    (ArgsT_values hA ha)
  exact ⟨_, hi, hs.invoke hp hj hx hu hh hr ha hi⟩

/-- A call may omit trailing actuals. The selected signature still covers the
list padded with `undefined`, and the dispatched body is the same term, because
`parameters` already supplies `undefined` for every slot the call does not
write. Omission is therefore not a second binding rule. -/
theorem codeCallsT_invoke_short {L k W v} (hf : codeCallsT L k W v)
    {p : Fam × List Fam × Fam} (hp : p ∈ L) {j : Nat} (hj : j < k) {U : WorldT j}
    (hx : WExt (trunc j (Nat.le_of_lt hj) W) U) (hu : WorldAdm U)
    {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hrv : isVal r = true) (hr : p.1 j U r)
    {args pad : List Tm} (hpad : ∀ a ∈ pad, a = .undef)
    (hA : ∀ A ∈ p.2.1, ValOnly A) (ha : ArgsT p.2.1 j U (args ++ pad)) :
    ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧ Safe p.2.2 j U heap result := by
  obtain ⟨arity, b, fs, rfl, hs⟩ := hf
  have hvals := ArgsT_values hA ha
  refine ⟨_, CallArguments.Invoke.closure (fs := fs) (body := b) (arity := arity) hrv
    (fun a hm => hvals a (List.mem_append_left pad hm)), ?_⟩
  have hsafe := hs.invoke hp hj hx hu hh hr ha
    (CallArguments.Invoke.closure (fs := fs) (body := b) (arity := arity) hrv hvals)
  rwa [CallArguments.bindParameters_pad arity args pad r b hpad] at hsafe

/-- The existing unary judgment is a specialization of list invocation whose
receiver is `undefined`. -/
def CodeSpec (L : List (Fam × Fam)) (k : Nat) (W : WorldT k) (b : Tm) : Prop :=
  InvocationSpec 1 (L.map fun p => (undefT, [p.1], p.2)) k W b

theorem InvocationSpec_unary_iff (arity : Nat) (L : List (Fam × Fam))
    (k : Nat) (W : WorldT k) (b : Tm) :
    InvocationSpec arity (L.map fun p => (undefT, [p.1], p.2)) k W b ↔
      Scoped (arity + 1) b ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
        WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' →
        ∀ (h : Heap), HeapOk j W' h →
          ∀ a, p.1 j W' a → Safe p.2 j W' h (CallArguments.bindParameters arity [a] .undef b) := by
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ?_⟩
    intro p hp j hj U hx hu heap hh a ha
    exact hs (undefT, [p.1], p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      j hj U hx hu heap hh .undef rfl [a] ⟨ha, trivial⟩
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ?_⟩
    intro p hp j hj U hx hu heap hh r hr args ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hr' : r = .undef := hr
    subst hr'
    obtain ⟨a, rfl, harg⟩ := (ArgsT_singleton q.1 j U args).mp ha
    exact hs q hq j hj U hx hu heap hh a harg

theorem CodeSpec_iff (L : List (Fam × Fam)) (k : Nat) (W : WorldT k) (b : Tm) :
    CodeSpec L k W b ↔
      Scoped 2 b ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
        WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' →
        ∀ (h : Heap), HeapOk j W' h →
          ∀ a, p.1 j W' a → Safe p.2 j W' h (subst 0 .undef (subst 1 a b)) :=
  InvocationSpec_unary_iff 1 L k W b

/-- Unary arrow domains describe actual calls, independently of the code's
parameter count. The descriptor controls padding and truncation. -/
theorem arrowsT_invocation_iff (arity : Nat) (L : List (Fam × Fam))
    (fs : List (PropKey × Nat)) (b : Tm) (n W) :
    arrowsT L n W (.objAt fs (.closure arity b)) ↔
      InvocationSpec arity (L.map fun p => (undefT, [p.1], p.2)) n W b := by
  rw [InvocationSpec_unary_iff]
  constructor
  · rintro ⟨⟨arity', b', fs', he, hc⟩, hs⟩
    cases he
    exact ⟨hc, hs⟩
  · rintro ⟨hc, hs⟩
    exact ⟨⟨arity, b, fs, rfl, hc⟩, hs⟩

/-- Existing unary overloads are exactly singleton-domain list signatures
whose receiver is `undefined`. -/
theorem arrowsT_callsT (L : List (Fam × Fam)) (n W v) :
    arrowsT L n W v ↔ codeCallsT (L.map fun p => (undefT, [p.1], p.2)) n W v := by
  constructor
  · intro h
    obtain ⟨arity, b, l, rfl, hc⟩ := h.1
    exact ⟨arity, b, l, rfl, (arrowsT_invocation_iff arity L l b n W).mp h⟩
  · rintro ⟨arity, b, l, rfl, hs⟩
    exact (arrowsT_invocation_iff arity L l b n W).mpr hs

theorem arrowsT_adm (L : List (Fam × Fam)) : Adm (arrowsT L) := by
  constructor
  · intro n W v h
    exact (arrowsT_callsT L n _ v).mpr ((codeCallsT_adm _).down n W v ((arrowsT_callsT L _ W v).mp h))
  · intro n W U hx v h
    exact (arrowsT_callsT L n U v).mpr ((codeCallsT_adm _).mono n W U hx v ((arrowsT_callsT L n W v).mp h))

theorem arrowsT_congr {α : Type} (l : List α) (f g : α → Fam × Fam) {n : Nat}
    (h : ∀ x ∈ l, Agree (f x).1 (g x).1 n ∧ Agree (f x).2 (g x).2 n)
    (W : WorldT n) (v : Val) : arrowsT (l.map f) n W v ↔ arrowsT (l.map g) n W v := by
  rw [arrowsT_callsT, arrowsT_callsT, List.map_map, List.map_map]
  apply codeCallsT_congr
  intro x hx
  exact ⟨fun _ _ _ _ => Iff.rfl, .cons (h x hx).1 .nil, (h x hx).2⟩

theorem arrowsT_code_iff (L : List (Fam × Fam)) (fs : List (PropKey × Nat)) (b : Tm) (n W) :
    arrowsT L n W (.objAt fs (.closure 1 b)) ↔ CodeSpec L n W b :=
  arrowsT_invocation_iff 1 L fs b n W

theorem CodeSpec.down {L n W b} (h : CodeSpec L (n + 1) W b) :
    CodeSpec L n (trunc n (Nat.le_succ n) W) b :=
  InvocationSpec.down h

theorem CodeSpec.mono {L n W W' b} (hx : WExt W W') (h : CodeSpec L n W b) :
    CodeSpec L n W' b :=
  InvocationSpec.mono hx h

#print axioms ArgsT_transfer
#print axioms codeCallsT_code_iff
#print axioms codeCallsT_of_signatures
#print axioms codeCallsT_select
#print axioms codeCallsT_adm
#print axioms codeCallsT_congr
#print axioms codeCallsT_invoke
#print axioms arrowsT_callsT
#print axioms ArgsT_length
#print axioms ArgsT_values
#print axioms ArgsT_mono
#print axioms codeCallsT_single_mono
#print axioms InvocationSpec.down
#print axioms InvocationSpec.mono
#print axioms InvocationSpec.invoke
#print axioms arrowsT_invocation_iff
#print axioms CodeSpec_iff

theorem omega_safe (B : Fam) : ∀ (n : Nat) (W : WorldT n) (h : Heap),
    WorldAdm W → HeapOk n W h → Safe B n W h omegaTm := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h ha hh
    exact Or.inr ⟨trunc n (Nat.le_succ n) W, h, omegaTm, WExt_refl _,
      WorldAdm_trunc _ ha, omega_step h, HeapOk_trunc n W h hh,
      ih _ h (WorldAdm_trunc _ ha) (HeapOk_trunc n W h hh)⟩

theorem value_safe (B : Fam) (n : Nat) (U : WorldT n) (h : Heap) (v : Val)
    (hv : isVal v = true) (hb : B n U v) : Safe B n U h v := by
  cases n with
  | zero => trivial
  | succ n => exact Or.inl ⟨hv, hb⟩

theorem safe_value_mem {B : Fam} {n : Nat} {U : WorldT (n+1)} {h : Heap} {v : Val}
    (hv : isVal v = true) (hs : Safe B (n+1) U h v) : B (n+1) U v := by
  rcases hs with ⟨_, hb⟩ | ⟨_, _, _, _, _, hs, _, _⟩
  · exact hb
  · exact False.elim (value_no_step hv hs)

/-! ## Call contracts

A function type says which actual lists a caller may write and what the call
then guarantees; it does not say how the callee binds them. Padding an omitted
parameter, collecting a rest array or dropping an extra actual is the code's
business, proved once where the code is created (`callsT_of_invocationSpec`,
and `RestCalls.restsT_of_restSpec` for variadic code). So a variadic value can
meet a fixed signature, and one value can carry fixed and variadic signatures
at once. -/

/-- Values with invocation code: closed objects whose descriptor is not absent. -/
def Invocable (v : Val) : Prop :=
  ∃ fs code, v = .objAt fs code ∧ code.callable = true ∧ Scoped 0 v

theorem Invocable.val {v : Val} (h : Invocable v) : isVal v = true := by
  obtain ⟨fs, code, rfl, -, -⟩ := h; rfl

/-- Code with `[[Call]]` has a call for every ready receiver and list. -/
theorem Invocable.invoke {v r : Tm} {args : List Tm} (h : Invocable v) (hr : isVal r = true)
    (ha : CallArguments.Values args) : ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result := by
  obtain ⟨fs, code, rfl, hc, -⟩ := h
  cases code with
  | absent => simp [CallCode.callable] at hc
  | closure arity body kind =>
    cases kind
    · exact ⟨_, .closure hr ha⟩
    · simp [CallCode.callable] at hc
  | variadic fixed body => exact ⟨_, .variadic hr ha⟩
  | bound target r₀ pre => exact ⟨_, .bound hr ha⟩

theorem Invocable.scoped {v : Val} (h : Invocable v) : Scoped 0 v := by
  obtain ⟨fs, code, rfl, -, hs⟩ := h; exact hs

theorem Callable.invocable {v : Val} (h : Callable v) : Invocable v := by
  obtain ⟨arity, b, fs, rfl, hs⟩ := h
  exact ⟨fs, _, rfl, rfl, by simpa [Scoped, Nat.add_comm] using hs⟩

/-- The actual lists a fixed signature admits: a prefix of its positions, each
written at its contract, every omitted position admitting `undefined`. -/
def ArgsShort (Ps : List Fam) (j : Nat) (W : WorldT j) (args : List Tm) : Prop :=
  args.length ≤ Ps.length ∧ ArgsT (Ps.take args.length) j W args ∧
    ∀ A ∈ Ps.drop args.length, A j W .undef

/-- The actual lists a variadic signature admits: its fixed parameters admit
the first actuals, as a fixed signature's do, and the actuals past them, as
one argument list, are at the rest contract. -/
def ArgsRest (Ps : List Fam) (E : ArgFam) (j : Nat) (W : WorldT j) (args : List Tm) : Prop :=
  ArgsShort Ps j W (args.take Ps.length) ∧ E j W (args.drop Ps.length)

/-- A promise: every receiver value at `Rc` with every admitted list of values
invokes the value, at every future world and satisfying heap below the budget,
safely at `R`. The receiver is not an actual: `Acc` never sees it. -/
def Promise (Acc : (j : Nat) → WorldT j → List Tm → Prop) (Rc R : Fam)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → ∀ r, isVal r = true → Rc j U r →
      ∀ args, CallArguments.Values args →
      Acc j U args → ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧ Safe R j U heap result

theorem Promise.down {Acc Rc R n W v} (h : Promise Acc Rc R (n + 1) W v) :
    Promise Acc Rc R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh r hrv hr args hv ha

theorem Promise.mono {Acc Rc R n W W' v} (hx : WExt W W') (h : Promise Acc Rc R n W v) :
    Promise Acc Rc R n W' v := by
  intro j hj U hy hu heap hh r hrv hr args hv ha
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh r hrv hr args hv ha

/-- Fewer admitted receivers and lists and a weaker result is a weaker promise. -/
theorem Promise.weaken {Acc Acc' : (j : Nat) → WorldT j → List Tm → Prop} {Rc Rc' R T : Fam}
    {k W v}
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ m, m < k → ∀ U u, R m U u → T m U u)
    (h : Promise Acc Rc R k W v) : Promise Acc' Rc' T k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨result, hi, hs⟩ :=
    h j hj U hx hu heap hh r hrv (hrecv j hj U r hr) args hv (hacc j hj U args ha)
  exact ⟨result, hi, Safe_mono j (fun m hm V u hu => hres m (by omega) V u hu) U heap _ hs⟩

/-- A promise holds for the receivers of a narrower family, which need only be
within the wider one in worlds extending the current one: a promise is only
ever used in those. -/
theorem Promise.weaken_recv {Acc : (j : Nat) → WorldT j → List Tm → Prop} {Rc Rc' R : Fam}
    {k W v}
    (hrecv : ∀ j (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ r, Rc' j U r → Rc j U r)
    (h : Promise Acc Rc R k W v) : Promise Acc Rc' R k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  exact h j hj U hx hu heap hh r hrv (hrecv j hj U hx r hr) args hv ha

/-- Agreement of the receivers, the admitted lists and the result below the
budget. -/
theorem Promise.congr {Acc Acc' : (j : Nat) → WorldT j → List Tm → Prop} {Rc Rc' R T : Fam}
    {n W v} (hrecv : Agree Rc Rc' n)
    (hacc : ∀ j, j < n → ∀ U args, Acc j U args ↔ Acc' j U args) (hres : Agree R T n) :
    Promise Acc Rc R n W v ↔ Promise Acc' Rc' T n W v := by
  constructor <;> intro h j hj U hx hu heap hh r hrv hr args hv ha
  · obtain ⟨result, hi, hs⟩ := h j hj U hx hu heap hh r hrv ((hrecv j hj U r).mpr hr) args hv
      ((hacc j hj U args).mpr ha)
    have hr' : Agree R T (j + 1) := fun k hk V a => hres k (by omega) V a
    exact ⟨result, hi, (Safe_congr (j + 1) hr' j (by omega) U heap _).mp hs⟩
  · obtain ⟨result, hi, hs⟩ := h j hj U hx hu heap hh r hrv ((hrecv j hj U r).mp hr) args hv
      ((hacc j hj U args).mp ha)
    have hr' : Agree R T (j + 1) := fun k hk V a => hres k (by omega) V a
    exact ⟨result, hi, (Safe_congr (j + 1) hr' j (by omega) U heap _).mpr hs⟩

/-- Values meeting every fixed signature `(receiver, parameters, result)`:
each receiver at its contract with each admitted actual list, including one
omitting trailing positions that admit `undefined`. -/
def callsT (L : List (Fam × List Fam × Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ p ∈ L, Promise (ArgsShort p.2.1) p.1 p.2.2 k W v

/-- Values meeting every variadic signature `(receiver, fixed parameters,
element, result)`: the contract of each further actual is the element's. -/
def restsT (S : List (Fam × List Fam × ArgFam × Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ S, Promise (ArgsRest s.2.1 s.2.2.1) s.1 s.2.2.2 k W v

/-! ### Construct signatures -/

/-- A class value: an object whose code is construct-only and closed. -/
def Constructible (v : Val) : Prop :=
  ∃ fs arity b, v = .objAt fs (.closure arity b .construct) ∧ Scoped 0 v

/-- What `new v(args)` runs, in one step: a class value's body, with
`undefined` for its receiver and the actuals for its parameters. -/
def ConstructsTo (v : Val) (args : List Tm) (result : Tm) : Prop :=
  ∃ fs arity b, v = .objAt fs (.closure arity b .construct) ∧
    result = CallArguments.bindParameters arity args .undef b

/-- The common constructor promise, independent of argument-list syntax. -/
def ConstructPromise (P : ArgFam) (R : Fam) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j),
    WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U → ∀ (heap : Heap), HeapOk j U heap →
      ∀ args, CallArguments.Values args → P j U args →
        ∃ result, ConstructsTo v args result ∧ Safe R j U heap result

/-- **Construct signatures.** Values meeting every signature `(parameters,
result)` under `new`: constructing the value, in any strictly future world,
with values at the parameters, runs a body safe at the result. The code is
construct-only, so a plain call cannot run it, and no code without
`[[Construct]]` is one. As for call signatures, the promise is about the term
after the step, which is what lets the signature's variance be used only
below the current level. -/
def ctorsT (L : List (List Fam × Fam)) : Fam := fun k W v =>
  Constructible v ∧ ∀ p ∈ L, ConstructPromise (ArgsT p.1) p.2 k W v

theorem ctorsT_adm (L : List (List Fam × Fam)) : Adm (ctorsT L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp j hj U hx hu heap hh args hv ha =>
      h.2 p hp j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh args hv ha⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp j hj U hy hu heap hh args hv ha =>
      h.2 p hp j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh args hv ha⟩⟩

theorem ctorsT_valOnly (L : List (List Fam × Fam)) : ValOnly (ctorsT L) := by
  intro _ _ _ h
  obtain ⟨fs, arity, b, rfl, -⟩ := h.1
  rfl

/-- **A class value.** An object with construct-only code whose body, with
`undefined` for its receiver, is safe at each signature's result for every
admitted actual list meets the signatures. -/
theorem ctorsT_of_body {L : List (List Fam × Fam)} {k : Nat} {W : WorldT k}
    {fs : List (PropKey × Nat)} {arity : Nat} {b : Tm}
    (hs : Scoped 0 (.objAt fs (.closure arity b .construct)))
    (hb : ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U → ∀ (heap : Heap), HeapOk j U heap →
        ∀ args, ArgsT p.1 j U args →
          Safe p.2 j U heap (CallArguments.bindParameters arity args .undef b)) :
    ctorsT L k W (.objAt fs (.closure arity b .construct)) :=
  ⟨⟨fs, arity, b, rfl, hs⟩, fun p hp j hj U hx hu heap hh args _ ha =>
    ⟨_, ⟨fs, arity, b, rfl, rfl⟩, hb p hp j hj U hx hu heap hh args ha⟩⟩

/-- The actual lists a variadic construct signature admits: its fixed
parameters' actuals exactly, then, as one argument pack, the rest. -/
def CtorRest (Ps : List Fam) (P : ArgFam) (j : Nat) (W : WorldT j) (args : List Tm) : Prop :=
  Ps.length ≤ args.length ∧ ArgsT Ps j W (args.take Ps.length) ∧
    P j W (args.drop Ps.length)

/-- **Variadic construct signatures** `(parameters, rest, result)`: as
`ctorsT`, for the lists `CtorRest` admits. -/
def ctorRestsT (S : List (List Fam × ArgFam × Fam)) : Fam := fun k W v =>
  Constructible v ∧ ∀ s ∈ S, ConstructPromise (CtorRest s.1 s.2.1) s.2.2 k W v

theorem ctorRestsT_adm (S : List (List Fam × ArgFam × Fam)) : Adm (ctorRestsT S) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp j hj U hx hu heap hh args hv ha =>
      h.2 p hp j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh args hv ha⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp j hj U hy hu heap hh args hv ha =>
      h.2 p hp j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh args hv ha⟩⟩

theorem ctorRestsT_append (S T : List (List Fam × ArgFam × Fam)) (k : Nat) (W : WorldT k) (v : Val) :
    ctorRestsT (S ++ T) k W v ↔ ctorRestsT S k W v ∧ ctorRestsT T k W v := by
  simp only [ctorRestsT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨hc, hl, hm⟩; exact ⟨⟨hc, hl⟩, hc, hm⟩
  · rintro ⟨⟨hc, hl⟩, -, hm⟩; exact ⟨hc, hl, hm⟩

/-- A class value with no variadic construct signature meets the empty list of
them. -/
theorem ctorRestsT_nil {k W v} (h : Constructible v) : ctorRestsT [] k W v :=
  ⟨h, fun _ hs => by cases hs⟩

theorem ctorsT_select {L n W v p} (hf : ctorsT L n W v) (hp : p ∈ L) : ctorsT [p] n W v :=
  ⟨hf.1, fun q hq => by cases List.mem_singleton.mp hq; exact hf.2 p hp⟩

theorem ctorsT_append (L M : List (List Fam × Fam)) (k : Nat) (W : WorldT k) (v : Val) :
    ctorsT (L ++ M) k W v ↔ ctorsT L k W v ∧ ctorsT M k W v := by
  simp only [ctorsT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨hc, hl, hm⟩; exact ⟨⟨hc, hl⟩, hc, hm⟩
  · rintro ⟨⟨hc, hl⟩, -, hm⟩; exact ⟨hc, hl, hm⟩

/-! ### Argument packs -/

/-- Tuple shape and position membership, independent of approximation policy:
the interpretation of an element is supplied. -/
def TupleFits (member : Fam → Val → Prop) (T : TupleF) (vs : List Val) : Prop :=
  T.required.length ≤ vs.length ∧
    (T.rest = none → vs.length ≤ T.required.length + T.optional.length) ∧
    ∀ i v A, vs[i]? = some v → positionFam T i = some A → member A v

theorem TupleFits.map {P Q : Fam → Val → Prop} {T : TupleF} {vs : List Val}
    (h : TupleFits P T vs) (hm : ∀ i A, positionFam T i = some A →
      ∀ v, P A v → Q A v) : TupleFits Q T vs :=
  ⟨h.1, h.2.1, fun i v A hv hA => hm i A hA v (h.2.2 i v A hv hA)⟩

/-- Equal shapes with equivalent position predicates admit the same lists.
-/
theorem TupleFits.congr {P Q : Fam → Val → Prop} {T T' : TupleF} {vs}
    (hreq : T.required.length = T'.required.length) (hopt : T.optional.length = T'.optional.length)
    (hrest : T.rest = none ↔ T'.rest = none)
    (hpos : ∀ i, (positionFam T i = none ↔ positionFam T' i = none) ∧
      ∀ A B, positionFam T i = some A → positionFam T' i = some B → ∀ v, P A v ↔ Q B v) :
    TupleFits P T vs ↔ TupleFits Q T' vs := by
  unfold TupleFits
  rw [hreq, hopt, hrest]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h i u B hu hB => ?_,
    fun h i u A hu hA => ?_⟩)
  · cases hA : positionFam T i with
    | none => rw [(hpos i).1.mp hA] at hB; cases hB
    | some A => exact ((hpos i).2 A B hA hB u).mp (h i u A hu hA)
  · cases hB : positionFam T' i with
    | none => rw [(hpos i).1.mpr hB] at hA; cases hA
    | some B => exact ((hpos i).2 A B hA hB u).mpr (h i u B hu hB)

theorem positionFam_elem (E : Fam) (i : Nat) :
    positionFam ⟨[], [], some E, false⟩ i = some E := by
  simp [positionFam]

theorem callsT_adm (L : List (Fam × List Fam × Fam)) : Adm (callsT L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

theorem restsT_adm (S : List (Fam × List Fam × ArgFam × Fam)) : Adm (restsT S) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

theorem callsT_valOnly (L : List (Fam × List Fam × Fam)) : ValOnly (callsT L) :=
  fun _ _ _ h => h.1.val

theorem callsT_select {L n W v p} (hf : callsT L n W v) (hp : p ∈ L) : callsT [p] n W v :=
  ⟨hf.1, fun q hq => by cases List.mem_singleton.mp hq; exact hf.2 p hp⟩

theorem restsT_select {S n W v s} (hf : restsT S n W v) (hs : s ∈ S) : restsT [s] n W v :=
  ⟨hf.1, fun q hq => by cases List.mem_singleton.mp hq; exact hf.2 s hs⟩

theorem callsT_of_signatures {L n W v} (hc : Invocable v)
    (hs : ∀ p ∈ L, callsT [p] n W v) : callsT L n W v :=
  ⟨hc, fun p hp => (hs p hp).2 p (by simp)⟩

theorem restsT_of_signatures {S n W v} (hc : Invocable v)
    (hs : ∀ s ∈ S, restsT [s] n W v) : restsT S n W v :=
  ⟨hc, fun s hsm => (hs s hsm).2 s (by simp)⟩

/-! ### Admitted lists -/

theorem ArgsT_take_drop {Ps : List Fam} {j W} : ∀ {args : List Tm} (m : Nat),
    ArgsT Ps j W args → ArgsT (Ps.take m) j W (args.take m) ∧ ArgsT (Ps.drop m) j W (args.drop m) := by
  induction Ps with
  | nil => intro args m h; cases args <;> cases m <;> simp_all [ArgsT]
  | cons A Ps ih =>
    intro args m h
    cases args with
    | nil => exact False.elim h
    | cons a args =>
      cases m with
      | zero => exact ⟨trivial, h⟩
      | succ m => exact ⟨⟨h.1, (ih m h.2).1⟩, (ih m h.2).2⟩

theorem ArgsT_all_undef {As : List Fam} {j W} : ∀ {pad : List Tm}, (∀ a ∈ pad, a = .undef) →
    ArgsT As j W pad → ∀ A ∈ As, A j W .undef := by
  induction As with
  | nil => intro _ _ _ A hA; cases hA
  | cons B As ih =>
    intro pad hp h A hA
    cases pad with
    | nil => exact False.elim h
    | cons a pad =>
      rcases List.mem_cons.mp hA with rfl | hA
      · have : a = .undef := hp a (by simp)
        subst this; exact h.1
      · exact ih (fun x hx => hp x (by simp [hx])) h.2 A hA

/-- Every member of a list typed position by position is in any family all
the positions are within. -/
theorem ArgsT_all_le {As : List Fam} {E : Fam} {j W}
    (hle : ∀ A ∈ As, ∀ u, A j W u → E j W u) :
    ∀ {xs : List Tm}, ArgsT As j W xs → ∀ e ∈ xs, E j W e := by
  induction As with
  | nil => intro xs h e he; cases xs <;> simp_all [ArgsT]
  | cons A As ih =>
    intro xs h e he
    cases xs with
    | nil => cases he
    | cons x xs =>
      rcases List.mem_cons.mp he with rfl | he
      · exact hle A (by simp) e h.1
      · exact ih (fun B hB => hle B (by simp [hB])) h.2 e he

/-- An exact list is admitted. -/
theorem ArgsShort_of_exact {Ps j W args} (h : ArgsT Ps j W args) : ArgsShort Ps j W args := by
  have hl := ArgsT_length h
  refine ⟨by omega, by rw [hl, List.take_length]; exact h, ?_⟩
  rw [hl, List.drop_length]; simp

/-- A list padded with `undefined` to a signature's length admits the prefix. -/
theorem ArgsShort_of_pad {Ps j W args pad} (hp : ∀ a ∈ pad, a = .undef)
    (h : ArgsT Ps j W (args ++ pad)) : ArgsShort Ps j W args := by
  have hl := ArgsT_length h
  obtain ⟨ht, hd⟩ := ArgsT_take_drop args.length h
  simp only [List.take_left, List.drop_left] at ht hd
  exact ⟨by simp at hl; omega, ht, ArgsT_all_undef hp hd⟩

/-- An admitted list, padded with `undefined`, is an exact list. -/
theorem ArgsShort_pad {Ps j W args} (h : ArgsShort Ps j W args) :
    ArgsT Ps j W (args ++ List.replicate (Ps.length - args.length) .undef) := by
  obtain ⟨hl, ht, hd⟩ := h
  have := ArgsT_append ht (ArgsT_undef (Us := Ps.drop args.length) hd)
  rwa [List.take_append_drop, List.length_drop] at this

theorem ArgsLe_take_drop {As Bs : List Fam} (h : ArgsLe As Bs) : ∀ m : Nat,
    ArgsLe (As.take m) (Bs.take m) ∧ ArgsLe (As.drop m) (Bs.drop m) := by
  induction h with
  | nil => intro m; simp only [List.take_nil, List.drop_nil]; exact ⟨.nil, .nil⟩
  | cons hab ht ih =>
    intro m
    cases m with
    | zero => exact ⟨.nil, .cons hab ht⟩
    | succ m => exact ⟨.cons hab (ih m).1, (ih m).2⟩

theorem ArgsLe_length {As Bs : List Fam} (h : ArgsLe As Bs) : As.length = Bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ArgsLe_all {As Bs : List Fam} (h : ArgsLe As Bs) {j W u}
    (ha : ∀ A ∈ As, A j W u) : ∀ B ∈ Bs, B j W u := by
  induction h with
  | nil => intro B hB; cases hB
  | cons hab _ ih =>
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hab j W u (ha _ (by simp))
    · exact ih (fun A hA => ha A (by simp [hA])) B hB

/-- Pointwise wider positions admit every list the narrower ones do. -/
theorem ArgsShort_mono {Qs Ps : List Fam} (h : ArgsLe Qs Ps) {j W args}
    (ha : ArgsShort Qs j W args) : ArgsShort Ps j W args := by
  obtain ⟨hl, ht, hd⟩ := ha
  have hlen := ArgsLe_length h
  obtain ⟨htk, hdr⟩ := ArgsLe_take_drop h args.length
  exact ⟨by omega, ArgsT_mono htk ht, ArgsLe_all hdr hd⟩

theorem ArgsAgree_take_drop {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) : ∀ m : Nat,
    ArgsAgree n (As.take m) (Bs.take m) ∧ ArgsAgree n (As.drop m) (Bs.drop m) := by
  induction h with
  | nil => intro m; simp only [List.take_nil, List.drop_nil]; exact ⟨.nil, .nil⟩
  | cons hab ht ih =>
    intro m
    cases m with
    | zero => exact ⟨.nil, .cons hab ht⟩
    | succ m => exact ⟨.cons hab (ih m).1, (ih m).2⟩

theorem ArgsAgree_length {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) :
    As.length = Bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ArgsAgree_all {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) {j : Nat} (hj : j < n)
    {W u} : (∀ A ∈ As, A j W u) ↔ ∀ B ∈ Bs, B j W u := by
  induction h with
  | nil => simp
  | cons hab _ ih => simp only [List.mem_cons, forall_eq_or_imp]; exact and_congr (hab j hj W u) ih

theorem ArgsShort_congr {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) {j : Nat} (hj : j < n)
    (W : WorldT j) (args : List Tm) : ArgsShort As j W args ↔ ArgsShort Bs j W args := by
  have hlen := ArgsAgree_length h
  obtain ⟨htk, hdr⟩ := ArgsAgree_take_drop h args.length
  unfold ArgsShort
  rw [hlen, ArgsT_congr htk hj W args, ArgsAgree_all hdr hj]

theorem ArgsRest_congr {n : Nat} {As Bs : List Fam} {E E' : ArgFam} (h : ArgsAgree n As Bs)
    (he : Agree E E' n) {j : Nat} (hj : j < n) (W : WorldT j) (args : List Tm) :
    ArgsRest As E j W args ↔ ArgsRest Bs E' j W args := by
  unfold ArgsRest
  rw [ArgsShort_congr h hj W _, ArgsAgree_length h]
  exact and_congr Iff.rfl (he j hj W _)

/-! ### Admitted lists, position by position -/

theorem ArgsShort_nil_args {Ps : List Fam} {j W} :
    ArgsShort Ps j W [] ↔ ∀ A ∈ Ps, A j W .undef := by
  simp [ArgsShort, ArgsT]

theorem ArgsShort_nil_params {j W} {args : List Tm} : ArgsShort [] j W args ↔ args = [] := by
  cases args <;> simp [ArgsShort, ArgsT]

theorem ArgsShort_cons {P : Fam} {Ps : List Fam} {j W a args} :
    ArgsShort (P :: Ps) j W (a :: args) ↔ P j W a ∧ ArgsShort Ps j W args := by
  simp only [ArgsShort, List.length_cons, List.take_succ_cons, List.drop_succ_cons, ArgsT]
  constructor
  · rintro ⟨hl, ⟨ha, ht⟩, hd⟩; exact ⟨ha, by omega, ht, hd⟩
  · rintro ⟨ha, hl, ht, hd⟩; exact ⟨by omega, ⟨ha, ht⟩, hd⟩

theorem ArgsRest_nil_args {Ps : List Fam} {E : ArgFam} {j W} :
    ArgsRest Ps E j W [] ↔ (∀ A ∈ Ps, A j W .undef) ∧ E j W [] := by
  simp only [ArgsRest, List.take_nil, List.drop_nil, ArgsShort_nil_args]

theorem ArgsRest_nil_params {E : ArgFam} {j W} {args : List Tm} :
    ArgsRest [] E j W args ↔ E j W args := by
  simp [ArgsRest, ArgsShort_nil_params]

theorem ArgsRest_cons {P : Fam} {Ps : List Fam} {E : ArgFam} {j W a args} :
    ArgsRest (P :: Ps) E j W (a :: args) ↔ P j W a ∧ ArgsRest Ps E j W args := by
  simp only [ArgsRest, List.length_cons, List.take_succ_cons, List.drop_succ_cons, ArgsShort_cons,
    and_assoc]

theorem ArgsRest_of_exact_extra {Ps : List Fam} {E : ArgFam} {j W args extra}
    (ha : ArgsT Ps j W args) (he : E j W extra) : ArgsRest Ps E j W (args ++ extra) := by
  have hl := ArgsT_length ha
  refine ⟨?_, ?_⟩
  · rw [← hl, List.take_left]; exact ArgsShort_of_exact ha
  · rw [← hl, List.drop_left]; exact he

/-! ### Invocation -/

/-- **Code meets signatures from its body.** The one place a body's safety
becomes a code contract. A signature may offer more parameters than the code
takes: binding reads the first `arity` actuals and discards the rest, as
JavaScript does, so the body is checked with the receiver and those actuals
substituted, whatever follows them. This holds of the code, not of any value
at a shorter signature: variadic code collects extra actuals and a bound
function forwards them. -/
theorem invocationSpec_of_instantiated {arity : Nat} {L : List (Fam × List Fam × Fam)}
    {n : Nat} {W : WorldT n} {ρ : Env} {b : Tm} (hρ : ∀ i, Scoped 0 (ρ i))
    (hlen : ∀ p ∈ L, arity ≤ p.2.1.length)
    (hval : ∀ p ∈ L, ∀ j (U : WorldT j) r args, p.1 j U r → ArgsT (p.2.1.take arity) j U args →
      ∀ a ∈ r :: args, Scoped 0 a)
    (hb : ∀ p ∈ L, ∀ (j : Nat) (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U → ∀ (heap : Heap), HeapOk j U heap →
        ∀ r args, p.1 j U r → ArgsT (p.2.1.take arity) j U args →
          Safe p.2.2 j U heap (instantiate 0 (prependArgs (r :: args) ρ) b)) :
    InvocationSpec arity L n W (instantiate (arity + 1) ρ b) := by
  refine ⟨instantiate_scoped ρ hρ b (arity + 1), ?_⟩
  intro p hp j hj U hx hu heap hok r hr args ha
  have ht := (ArgsT_take_drop arity ha).1
  have hlength : (args.take arity).length = arity := by
    rw [ArgsT_length ht, List.length_take, Nat.min_eq_left (hlen p hp)]
  have hexact := CallArguments.parameters_exact (args.take arity)
  rw [hlength] at hexact
  rw [← CallArguments.bindParameters_take]
  unfold CallArguments.bindParameters
  rw [hexact, show arity + 1 = 0 + (r :: args.take arity).length by simp [hlength],
    instantiate_args ρ hρ (hval p hp j U r _ hr ht)]
  exact hb p hp j hj U hx hu heap hok r _ hr ht

/-- Closure code meeting its code contract meets the signatures: a shorter
list binds as the padded one does, since `parameters` pads with `undefined`. -/
theorem callsT_of_invocationSpec {arity L k W b} (fs : List (PropKey × Nat))
    (hs : InvocationSpec arity L k W b) : callsT L k W (.objAt fs (.closure arity b)) := by
  refine ⟨⟨fs, _, rfl, rfl, by simpa [Scoped, Nat.add_comm] using hs.1⟩, ?_⟩
  intro p hp j hj U hx hu heap hh r hrv hr args hvals ha
  have hsafe := hs.2 p hp j hj U hx hu heap hh r hr _ (ArgsShort_pad ha)
  rw [CallArguments.bindParameters_pad arity args _ r b
    (fun a hm => List.eq_of_mem_replicate hm)] at hsafe
  exact ⟨_, .closure hrv hvals, hsafe⟩

/-- A callable signature is contravariant in its receiver and ordered
arguments and covariant in its result. -/
theorem callsT_single_mono {Rc Qc : Fam} {Ps Qs : List Fam} {R T : Fam}
    (hrecv : FamLe Qc Rc) (hdom : ArgsLe Qs Ps) (hresult : FamLe R T) :
    FamLe (callsT [(Rc, Ps, R)]) (callsT [(Qc, Qs, T)]) := by
  intro k W v hv
  refine ⟨hv.1, fun q hq => ?_⟩
  cases List.mem_singleton.mp hq
  exact (hv.2 (Rc, Ps, R) (by simp)).weaken (fun _ _ U r hr => hrecv _ U r hr)
    (fun _ _ _ _ ha => ArgsShort_mono hdom ha) (fun m _ U u hu => hresult m U u hu)

/-- List signatures guard the receiver, every domain position and the result:
the congruence recursive call types need. -/
theorem callsT_congr {α : Type} (l : List α) (f g : α → Fam × List Fam × Fam) {n : Nat}
    (h : ∀ x ∈ l, Agree (f x).1 (g x).1 n ∧ ArgsAgree n (f x).2.1 (g x).2.1 ∧
      Agree (f x).2.2 (g x).2.2 n)
    (W : WorldT n) (v : Val) : callsT (l.map f) n W v ↔ callsT (l.map g) n W v := by
  unfold callsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    exact (Promise.congr (h x hm).1 (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mp (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    exact (Promise.congr (h x hm).1 (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mpr (hs (g x) (List.mem_map_of_mem hm))

theorem ctorsT_congr {α : Type} (l : List α) (f g : α → List Fam × Fam) {n : Nat}
    (h : ∀ x ∈ l, ArgsAgree n (f x).1 (g x).1 ∧ Agree (f x).2 (g x).2 n)
    (W : WorldT n) (v : Val) : ctorsT (l.map f) n W v ↔ ctorsT (l.map g) n W v := by
  unfold ctorsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩ <;>
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp <;>
    intro j hj U hx hu heap hh args hv ha
  · obtain ⟨result, hc, hsafe⟩ := hs (f x) (List.mem_map_of_mem hm) j hj U hx hu heap hh args hv
      ((ArgsT_congr (h x hm).1 hj U args).mpr ha)
    exact ⟨result, hc, (Safe_congr n (h x hm).2 j hj U heap _).mp hsafe⟩
  · obtain ⟨result, hc, hsafe⟩ := hs (g x) (List.mem_map_of_mem hm) j hj U hx hu heap hh args hv
      ((ArgsT_congr (h x hm).1 hj U args).mp ha)
    exact ⟨result, hc, (Safe_congr n (h x hm).2 j hj U heap _).mpr hsafe⟩

theorem ctorRestsT_congr {α : Type} (l : List α) (f g : α → List Fam × ArgFam × Fam) {n : Nat}
    (h : ∀ x ∈ l, ArgsAgree n (f x).1 (g x).1 ∧ Agree (f x).2.1 (g x).2.1 n ∧
      Agree (f x).2.2 (g x).2.2 n)
    (W : WorldT n) (v : Val) : ctorRestsT (l.map f) n W v ↔ ctorRestsT (l.map g) n W v := by
  unfold ctorRestsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩ <;>
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp <;>
    intro j hj U hx hu heap hh args hv ha
  · have hl := ArgsAgree_length (h x hm).1
    obtain ⟨result, hc, hsafe⟩ := hs (f x) (List.mem_map_of_mem hm) j hj U hx hu heap hh args hv
      (by
        obtain ⟨hlen, hfix, hpack⟩ := ha
        refine ⟨by rw [hl]; exact hlen, ?_, ?_⟩
        · rw [hl]; exact (ArgsT_congr (h x hm).1 hj U _).mpr hfix
        · rw [hl]; exact ((h x hm).2.1 j hj U _).mpr hpack)
    exact ⟨result, hc, (Safe_congr n (h x hm).2.2 j hj U heap _).mp hsafe⟩
  · have hl := ArgsAgree_length (h x hm).1
    obtain ⟨result, hc, hsafe⟩ := hs (g x) (List.mem_map_of_mem hm) j hj U hx hu heap hh args hv
      (by
        obtain ⟨hlen, hfix, hpack⟩ := ha
        refine ⟨by rw [← hl]; exact hlen, ?_, ?_⟩
        · rw [← hl]; exact (ArgsT_congr (h x hm).1 hj U _).mp hfix
        · rw [← hl]; exact ((h x hm).2.1 j hj U _).mp hpack)
    exact ⟨result, hc, (Safe_congr n (h x hm).2.2 j hj U heap _).mpr hsafe⟩

theorem restsT_congr {α : Type} (l : List α) (f g : α → Fam × List Fam × ArgFam × Fam) {n : Nat}
    (h : ∀ x ∈ l, Agree (f x).1 (g x).1 n ∧ ArgsAgree n (f x).2.1 (g x).2.1 ∧
      Agree (f x).2.2.1 (g x).2.2.1 n ∧ Agree (f x).2.2.2 (g x).2.2.2 n)
    (W : WorldT n) (v : Val) : restsT (l.map f) n W v ↔ restsT (l.map g) n W v := by
  unfold restsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    exact (Promise.congr (h x hm).1
      (fun j hj U args => ArgsRest_congr (h x hm).2.1 (h x hm).2.2.1 hj U args)
      (h x hm).2.2.2).mp (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    exact (Promise.congr (h x hm).1
      (fun j hj U args => ArgsRest_congr (h x hm).2.1 (h x hm).2.2.1 hj U args)
      (h x hm).2.2.2).mpr (hs (g x) (List.mem_map_of_mem hm))

/-- A closure's unary arrow meets the list signature with its one domain and
the `undefined` receiver its calls pass. -/
theorem callsT_of_arrowsT {L : List (Fam × Fam)} {n W v} (h : arrowsT L n W v) :
    callsT (L.map fun p => (undefT, [p.1], p.2)) n W v := by
  obtain ⟨arity, b, fs, rfl, hc⟩ := h.1
  exact callsT_of_invocationSpec fs ((arrowsT_invocation_iff arity L fs b n W).mp h)

/-! ### Bound functions

`.bind` allocates a forwarding descriptor. Its promise is the target's, with
the prefix taken off the front of the parameters and any receiver admitted:
invocation drops the receiver it is given and supplies the saved one. -/

/-- A saved exact prefix followed by an admitted list is admitted by the
target's parameters. -/
theorem ArgsShort_prefix {Ps Ds : List Fam} {j W pre args}
    (hp : ArgsT Ps j W pre) (ha : ArgsShort Ds j W args) :
    ArgsShort (Ps ++ Ds) j W (pre ++ args) := by
  obtain ⟨hlen, htake, hdrop⟩ := ha
  have hpl := ArgsT_length hp
  refine ⟨by simp; omega, ?_, ?_⟩
  · have ht : (Ps ++ Ds).take (pre ++ args).length = Ps ++ Ds.take args.length := by
      rw [List.length_append, hpl, List.take_append, List.take_of_length_le (by omega)]
      congr 2
      omega
    rw [ht]
    exact ArgsT_append hp htake
  · intro A hA
    have hd : (Ps ++ Ds).drop (pre ++ args).length = Ds.drop args.length := by
      rw [List.length_append, hpl, List.drop_append, List.drop_of_length_le (by omega)]
      simp
    rw [hd] at hA
    exact hdrop A hA

/-- An admitted list stays admitted as the budget drops and the world grows. -/
theorem ArgsShort_transfer {Ps : List Fam} (hA : ∀ A ∈ Ps, Adm A) {n W args}
    (ha : ArgsShort Ps n W args) (j : Nat) (hj : j ≤ n) (U : WorldT j)
    (hx : WExt (trunc j hj W) U) : ArgsShort Ps j U args := by
  obtain ⟨hlen, htake, hdrop⟩ := ha
  refine ⟨hlen, ArgsT_transfer (fun A hm => hA A (List.mem_of_mem_take hm)) htake j hj U hx, ?_⟩
  intro A hm
  have hadm := hA A (List.mem_of_mem_drop hm)
  exact hadm.mono j _ U hx _ (hadm.down_le n j hj W _ (hdrop A hm))

/-- **A bound function meets the residual signature.** The target meets
`(Rt, Ps ++ Ds, R)`, the saved receiver is at `Rt` and the saved prefix at
`Ps`; the object then meets `(Rc, Ds, R)` for any receiver contract `Rc`. -/
theorem callsT_bound {Rt R Rc : Fam} {Ps Ds : List Fam} {k : Nat} {W : WorldT k}
    {fs : List (PropKey × Nat)} {tv rv : Val} {pvs : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hDs : ∀ A ∈ Ds, Adm A)
    (ht : callsT [(Rt, Ps ++ Ds, R)] k W tv) (hrv : isVal rv = true) (hsr : Scoped 0 rv)
    (hr : Rt k W rv) (hpv : ArgsT Ps k W pvs) (hvs : CallArguments.Values pvs)
    (hsp : ∀ a ∈ pvs, Scoped 0 a) :
    callsT [(Rc, Ds, R)] k W (.objAt fs (.bound tv rv pvs)) := by
  refine ⟨⟨fs, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hp
    cases List.mem_singleton.mp hp
    intro j hj U hx hu heap hh r hrv' _ args hargs hacc
    refine ⟨_, .bound hrv' hargs, ?_⟩
    cases j with
    | zero => trivial
    | succ i =>
      have hi : i < k := by omega
      have hxU : WExt (trunc i (Nat.le_of_lt hi) W) (trunc i (Nat.le_succ i) U) := by
        have hx' := WExt_trunc (Nat.le_succ i) hx
        rwa [trunc_trunc] at hx'
      have hu' := WorldAdm_trunc (Nat.le_succ i) hu
      have hh' := HeapOk_trunc i U heap hh
      have hr' := hRt.mono i _ _ hxU rv (hRt.down_le k i (Nat.le_of_lt hi) W rv hr)
      have hpre := ArgsT_transfer hPs hpv i (Nat.le_of_lt hi) _ hxU
      have hrest := ArgsShort_transfer hDs hacc i (Nat.le_succ i) _ (WExt_refl _)
      have hall : CallArguments.Values (pvs ++ args) := by
        intro a hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hvs a hm
        · exact hargs a hm
      obtain ⟨res, hinv, hsafe⟩ := ht.2 _ (List.mem_singleton_self _) i hi _ hxU hu' heap hh'
        rv hrv hr' (pvs ++ args) hall (ArgsShort_prefix hpre hrest)
      exact Or.inr ⟨_, heap, res, WExt_refl _, hu', hinv.step heap, hh', hsafe⟩

/-- Every actual typed position by position at one element contract is in it. -/
theorem ArgsT_replicate_all {E : Fam} {j W} : ∀ {m : Nat} {xs : List Tm},
    ArgsT (List.replicate m E) j W xs → ∀ x ∈ xs, E j W x
  | 0, [], _, x, hx => by cases hx
  | 0, _ :: _, h, _, _ => by cases h
  | m + 1, [], h, _, _ => by cases h
  | m + 1, y :: ys, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ArgsT_replicate_all h.2 x hx

/-- A saved prefix covering the first positions of a variadic signature,
followed by a list the rest of the signature admits, is admitted by the whole
signature, when the rest contract admits the prefix's values past the fixed
positions in front of any pack it admits. -/
theorem ArgsRest_prefix {Ps : List Fam} {E : ArgFam} {j W pre args}
    (hp : ArgsT (Ps.take pre.length) j W (pre.take Ps.length))
    (hext : ∀ ys, E j W ys → E j W (pre.drop Ps.length ++ ys))
    (ha : ArgsRest (Ps.drop pre.length) E j W args) : ArgsRest Ps E j W (pre ++ args) := by
  by_cases hk : pre.length ≤ Ps.length
  · rw [List.take_of_length_le hk] at hp
    obtain ⟨hs, he⟩ := ha
    have hdl : (Ps.drop pre.length).length = Ps.length - pre.length := by simp
    refine ⟨?_, ?_⟩
    · have htk : (pre ++ args).take Ps.length = pre ++ args.take (Ps.drop pre.length).length := by
        rw [List.take_append, List.take_of_length_le hk, hdl]
      rw [htk]
      have h := ArgsShort_prefix hp hs
      rwa [List.take_append_drop] at h
    · have hdr : (pre ++ args).drop Ps.length = args.drop (Ps.drop pre.length).length := by
        rw [List.drop_append, List.drop_of_length_le hk, hdl]
        simp
      rw [hdr]; exact he
  · have hdrop : Ps.drop pre.length = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop, ArgsRest_nil_params] at ha
    rw [List.take_of_length_le (show Ps.length ≤ pre.length by omega)] at hp
    refine ⟨?_, ?_⟩
    · have : (pre ++ args).take Ps.length = pre.take Ps.length := by
        rw [List.take_append]; simp [show Ps.length - pre.length = 0 by omega]
      rw [this]; exact ArgsShort_of_exact hp
    · have hd : (pre ++ args).drop Ps.length = pre.drop Ps.length ++ args := by
        rw [List.drop_append]; simp [show Ps.length - pre.length = 0 by omega]
      rw [hd]; exact hext args ha

/-- An admitted variadic list stays admitted as the budget drops and the world
grows. -/
theorem ArgsRest_transfer {Ps : List Fam} {E : ArgFam} (hA : ∀ A ∈ Ps, Adm A) (hE : Adm E)
    {n W args} (ha : ArgsRest Ps E n W args) (j : Nat) (hj : j ≤ n) (U : WorldT j)
    (hx : WExt (trunc j hj W) U) : ArgsRest Ps E j U args :=
  ⟨ArgsShort_transfer hA ha.1 j hj U hx, hE.mono j _ U hx _ (hE.down_le n j hj W _ ha.2)⟩

/-- **A bound variadic function meets the residual variadic signature**: the
positions the prefix did not take, then the rest contract, at any receiver,
when that contract admits the prefix's values past the fixed positions in front
of any pack it admits, as an element rest does. -/
theorem restsT_bound {Rt R Rc : Fam} {E : ArgFam} {Ps : List Fam} {k : Nat} {W : WorldT k}
    {fs : List (PropKey × Nat)} {tv rv : Val} {pvs : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hE : Adm E)
    (ht : restsT [(Rt, Ps, E, R)] k W tv) (hrv : isVal rv = true) (hsr : Scoped 0 rv)
    (hr : Rt k W rv)
    (hpv : ArgsT (Ps.take pvs.length) k W (pvs.take Ps.length))
    (hext : ∀ j (hj : j ≤ k) (U : WorldT j), WExt (trunc j hj W) U →
      ∀ ys, E j U ys → E j U (pvs.drop Ps.length ++ ys))
    (hvs : CallArguments.Values pvs) (hsp : ∀ a ∈ pvs, Scoped 0 a) :
    restsT [(Rc, Ps.drop pvs.length, E, R)] k W (.objAt fs (.bound tv rv pvs)) := by
  refine ⟨⟨fs, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hp
    cases List.mem_singleton.mp hp
    intro j hj U hx hu heap hh r hrv' _ args hargs hacc
    refine ⟨_, .bound hrv' hargs, ?_⟩
    cases j with
    | zero => trivial
    | succ i =>
      have hi : i < k := by omega
      have hxU : WExt (trunc i (Nat.le_of_lt hi) W) (trunc i (Nat.le_succ i) U) := by
        have hx' := WExt_trunc (Nat.le_succ i) hx
        rwa [trunc_trunc] at hx'
      have hu' := WorldAdm_trunc (Nat.le_succ i) hu
      have hh' := HeapOk_trunc i U heap hh
      have hr' := hRt.mono i _ _ hxU rv (hRt.down_le k i (Nat.le_of_lt hi) W rv hr)
      have hpre := ArgsT_transfer (fun A hA => hPs A (List.mem_of_mem_take hA)) hpv i
        (Nat.le_of_lt hi) _ hxU
      have hrest := ArgsRest_transfer (fun A hA => hPs A (List.mem_of_mem_drop hA)) hE hacc i
        (Nat.le_succ i) _ (WExt_refl _)
      have hall : CallArguments.Values (pvs ++ args) := by
        intro a hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hvs a hm
        · exact hargs a hm
      obtain ⟨res, hinv, hsafe⟩ := ht.2 _ (List.mem_singleton_self _) i hi _ hxU hu' heap hh'
        rv hrv hr' (pvs ++ args) hall (ArgsRest_prefix hpre (hext i (Nat.le_of_lt hi) _ hxU) hrest)
      exact Or.inr ⟨_, heap, res, WExt_refl _, hu', hinv.step heap, hh', hsafe⟩

#print axioms callsT_bound
#print axioms restsT_bound
#print axioms callsT_of_invocationSpec
#print axioms callsT_congr
#print axioms restsT_congr

end Model
end Verification
