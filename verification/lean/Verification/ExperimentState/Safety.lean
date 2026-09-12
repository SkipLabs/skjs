import Verification.ExperimentState.CallArguments
import Verification.ExperimentState.Heaps
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
namespace ExperimentState

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

/-- The body executed after a call's beta step. This is a semantic helper,
not an additional runtime operation. Arrow membership separately requires a
callable shape, so the fallback branch is never used for typed application. -/
def callBody (v a : Tm) : Tm := match v with
  | .obj _ (.closure n b) => CallArguments.bindParameters n [a] b
  | _ => .app .nul .nul

/-- Only an object with closed invocation code is a callable value. -/
def Callable (v : Val) : Prop :=
  ∃ arity b l, v = .obj l (.closure arity b) ∧ Scoped arity b

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
theorem arrowsT_of_all {L : List (Fam × Fam)} {k : Nat} {W : WorldT k} {v : Val} {b : Tm} {l : Nat}
    (hobj : v = .obj l (.closure 1 b)) (hclosed : Scoped 1 b) (h : ∀ p ∈ L, arrowT p.1 p.2 k W v) : arrowsT L k W v :=
  ⟨⟨1, b, l, hobj, hclosed⟩, fun p hp j hj W' hx hu hp' hok a ha => (h p hp).2 j hj W' hx hu hp' hok a ha⟩

theorem arrowsT_valOnly (L : List (Fam × Fam)) : ValOnly (arrowsT L) := by
  rintro j W a ⟨hc, -⟩
  exact hc.val

/-- Ordered actual-argument contracts. The signature fixes the actual count;
the code's declared parameter count is independent. -/
def ArgsT : List Fam → (k : Nat) → WorldT k → List Tm → Prop
  | [], _, _, [] => True
  | A :: As, k, W, a :: args => A k W a ∧ ArgsT As k W args
  | _, _, _, _ => False

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

/-- A code contract checks the normalized parameter list after actuals have
been evaluated. Each overload admits its own list of actual argument types. -/
def InvocationSpec (arity : Nat) (L : List (List Fam × Fam))
    (k : Nat) (W : WorldT k) (b : Tm) : Prop :=
  Scoped arity b ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
    WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' → ∀ (h : Heap), HeapOk j W' h →
      ∀ args, ArgsT p.1 j W' args →
        Safe p.2 j W' h (CallArguments.bindParameters arity args b)

theorem InvocationSpec.down {arity L n W b} (h : InvocationSpec arity L (n + 1) W b) :
    InvocationSpec arity L n (trunc n (Nat.le_succ n) W) b := by
  refine ⟨h.1, ?_⟩
  intro p hp j hj U hx hu heap hh args ha
  exact h.2 p hp j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh args ha

theorem InvocationSpec.mono {arity L n W W' b} (hx : WExt W W')
    (h : InvocationSpec arity L n W b) : InvocationSpec arity L n W' b := by
  refine ⟨h.1, ?_⟩
  intro p hp j hj U hy hu heap hh args ha
  exact h.2 p hp j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh args ha

/-- Dispatch realizes the code contract in a future world. The actual list
can be empty or differ in length from the declared parameters, provided
the selected signature admits it. Operand effects have finished before dispatch. -/
theorem InvocationSpec.invoke {arity L k W b} (hs : InvocationSpec arity L k W b)
    {p : List Fam × Fam} (hp : p ∈ L) {j : Nat} (hj : j < k) {U : WorldT j}
    (hx : WExt (trunc j (Nat.le_of_lt hj) W) U) (hu : WorldAdm U)
    {heap : Heap} (hh : HeapOk j U heap) {args : List Tm} (ha : ArgsT p.1 j U args)
    {l : Nat} {result : Tm}
    (hi : CallArguments.Invoke ⟨.obj l (.closure arity b), args⟩ result) :
    Safe p.2 j U heap result := by
  cases hi
  exact hs.2 p hp j hj U hx hu heap hh args ha

/-- Callable values with ordered argument-list signatures. The descriptor's
parameter count is independent of every overload's admitted actual count. -/
def callsT (L : List (List Fam × Fam)) : Fam := fun k W v =>
  ∃ arity b l, v = .obj l (.closure arity b) ∧ InvocationSpec arity L k W b

theorem callsT_code_iff (L : List (List Fam × Fam)) (arity l : Nat) (b : Tm) (n W) :
    callsT L n W (.obj l (.closure arity b)) ↔ InvocationSpec arity L n W b := by
  constructor
  · rintro ⟨arity', b', l', he, hs⟩
    cases he
    exact hs
  · intro hs
    exact ⟨arity, b, l, rfl, hs⟩

theorem callsT_callable {L n W v} (h : callsT L n W v) : Callable v := by
  obtain ⟨arity, b, l, hv, hs⟩ := h
  exact ⟨arity, b, l, hv, hs.1⟩

theorem callsT_adm (L : List (List Fam × Fam)) : Adm (callsT L) := by
  constructor
  · rintro n W v ⟨arity, b, l, hv, hs⟩
    exact ⟨arity, b, l, hv, hs.down⟩
  · rintro n W U hx v ⟨arity, b, l, hv, hs⟩
    exact ⟨arity, b, l, hv, hs.mono hx⟩

/-- List signatures guard every domain position and the result. This is the
congruence needed to interpret recursive call types in the existing tower. -/
theorem callsT_congr {α : Type} (l : List α) (f g : α → List Fam × Fam) {n : Nat}
    (h : ∀ x ∈ l,
      ArgsAgree n (f x).1 (g x).1 ∧ Agree (f x).2 (g x).2 n)
    (W : WorldT n) (v : Val) : callsT (l.map f) n W v ↔ callsT (l.map g) n W v := by
  constructor <;> rintro ⟨arity, b, loc, hv, hc, hs⟩ <;>
    refine ⟨arity, b, loc, hv, hc, ?_⟩ <;> intro p hp j hj U hx hu heap hh args ha
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hd, hr⟩ := h x hm
    have hr' : Agree (f x).2 (g x).2 (j + 1) := fun k hk V a => hr k (by omega) V a
    exact (Safe_congr (j + 1) hr' j (by omega) U heap _).mp
      (hs (f x) (List.mem_map_of_mem hm) j hj U hx hu heap hh args
        ((ArgsT_congr hd hj U args).mpr ha))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hd, hr⟩ := h x hm
    have hr' : Agree (f x).2 (g x).2 (j + 1) := fun k hk V a => hr k (by omega) V a
    exact (Safe_congr (j + 1) hr' j (by omega) U heap _).mpr
      (hs (g x) (List.mem_map_of_mem hm) j hj U hx hu heap hh args
        ((ArgsT_congr hd hj U args).mp ha))

/-- Typed callable values dispatch to a safe body at the next observation
budget. Readiness follows from the argument domains containing only values. -/
theorem callsT_invoke {L k W v} (hf : callsT L k W v)
    {p : List Fam × Fam} (hp : p ∈ L) {j : Nat} (hj : j < k) {U : WorldT j}
    (hx : WExt (trunc j (Nat.le_of_lt hj) W) U) (hu : WorldAdm U)
    {heap : Heap} (hh : HeapOk j U heap) {args : List Tm}
    (hA : ∀ A ∈ p.1, ValOnly A) (ha : ArgsT p.1 j U args) :
    ∃ result, CallArguments.Invoke ⟨v, args⟩ result ∧ Safe p.2 j U heap result := by
  obtain ⟨arity, b, l, rfl, hs⟩ := hf
  have hi := CallArguments.Invoke.closure (l := l) (body := b) (arity := arity) (ArgsT_values hA ha)
  exact ⟨_, hi, hs.invoke hp hj hx hu hh ha hi⟩

/-- The existing unary judgment is a specialization of list invocation. -/
def CodeSpec (L : List (Fam × Fam)) (k : Nat) (W : WorldT k) (b : Tm) : Prop :=
  InvocationSpec 1 (L.map fun p => ([p.1], p.2)) k W b

theorem InvocationSpec_unary_iff (arity : Nat) (L : List (Fam × Fam))
    (k : Nat) (W : WorldT k) (b : Tm) :
    InvocationSpec arity (L.map fun p => ([p.1], p.2)) k W b ↔
      Scoped arity b ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
        WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' →
        ∀ (h : Heap), HeapOk j W' h →
          ∀ a, p.1 j W' a → Safe p.2 j W' h (CallArguments.bindParameters arity [a] b) := by
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ?_⟩
    intro p hp j hj U hx hu heap hh a ha
    exact hs ([p.1], p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      j hj U hx hu heap hh [a] ⟨ha, trivial⟩
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ?_⟩
    intro p hp j hj U hx hu heap hh args ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, rfl, harg⟩ := (ArgsT_singleton q.1 j U args).mp ha
    exact hs q hq j hj U hx hu heap hh a harg

theorem CodeSpec_iff (L : List (Fam × Fam)) (k : Nat) (W : WorldT k) (b : Tm) :
    CodeSpec L k W b ↔
      Scoped 1 b ∧ ∀ p ∈ L, ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
        WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' →
        ∀ (h : Heap), HeapOk j W' h →
          ∀ a, p.1 j W' a → Safe p.2 j W' h (subst 0 a b) :=
  InvocationSpec_unary_iff 1 L k W b

/-- Unary arrow domains describe actual calls, independently of the code's
parameter count. The descriptor controls padding and truncation. -/
theorem arrowsT_invocation_iff (arity : Nat) (L : List (Fam × Fam))
    (l : Nat) (b : Tm) (n W) :
    arrowsT L n W (.obj l (.closure arity b)) ↔
      InvocationSpec arity (L.map fun p => ([p.1], p.2)) n W b := by
  rw [InvocationSpec_unary_iff]
  constructor
  · rintro ⟨⟨arity', b', l', he, hc⟩, hs⟩
    cases he
    exact ⟨hc, hs⟩
  · rintro ⟨hc, hs⟩
    exact ⟨⟨arity, b, l, rfl, hc⟩, hs⟩

/-- Existing unary overloads are exactly singleton-domain list signatures. -/
theorem arrowsT_callsT (L : List (Fam × Fam)) (n W v) :
    arrowsT L n W v ↔ callsT (L.map fun p => ([p.1], p.2)) n W v := by
  constructor
  · intro h
    obtain ⟨arity, b, l, rfl, hc⟩ := h.1
    exact ⟨arity, b, l, rfl, (arrowsT_invocation_iff arity L l b n W).mp h⟩
  · rintro ⟨arity, b, l, rfl, hs⟩
    exact (arrowsT_invocation_iff arity L l b n W).mpr hs

theorem arrowsT_adm (L : List (Fam × Fam)) : Adm (arrowsT L) := by
  constructor
  · intro n W v h
    exact (arrowsT_callsT L n _ v).mpr ((callsT_adm _).down n W v ((arrowsT_callsT L _ W v).mp h))
  · intro n W U hx v h
    exact (arrowsT_callsT L n U v).mpr ((callsT_adm _).mono n W U hx v ((arrowsT_callsT L n W v).mp h))

theorem arrowsT_congr {α : Type} (l : List α) (f g : α → Fam × Fam) {n : Nat}
    (h : ∀ x ∈ l, Agree (f x).1 (g x).1 n ∧ Agree (f x).2 (g x).2 n)
    (W : WorldT n) (v : Val) : arrowsT (l.map f) n W v ↔ arrowsT (l.map g) n W v := by
  rw [arrowsT_callsT, arrowsT_callsT, List.map_map, List.map_map]
  apply callsT_congr
  intro x hx
  exact ⟨.cons (h x hx).1 .nil, (h x hx).2⟩

theorem arrowsT_code_iff (L : List (Fam × Fam)) (l : Nat) (b : Tm) (n W) :
    arrowsT L n W (.obj l (.closure 1 b)) ↔ CodeSpec L n W b :=
  arrowsT_invocation_iff 1 L l b n W

theorem CodeSpec.down {L n W b} (h : CodeSpec L (n + 1) W b) :
    CodeSpec L n (trunc n (Nat.le_succ n) W) b :=
  InvocationSpec.down h

theorem CodeSpec.mono {L n W W' b} (hx : WExt W W') (h : CodeSpec L n W b) :
    CodeSpec L n W' b :=
  InvocationSpec.mono hx h

#print axioms ArgsT_transfer
#print axioms callsT_code_iff
#print axioms callsT_adm
#print axioms callsT_congr
#print axioms callsT_invoke
#print axioms arrowsT_callsT
#print axioms ArgsT_length
#print axioms ArgsT_values
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

end ExperimentState
end Verification
