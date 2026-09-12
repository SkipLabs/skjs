import Verification.ExperimentState.ProgramTyping

namespace Verification.ExperimentState.ProgramTypingTests
open PositiveNormalization PositiveGraphs PositiveRules PositiveCertificates ProgramTyping

def G : NormalGraph (Fin 6) := fun i => match i.val with
  | 0 => [.nul]
  | 1 => [.bool]
  | 2 => [.refs [1] []]
  | 3 => [.arrs [([0], [1]), ([1], [0])]]
  | 4 => [.arrs [([0, 1], [0, 1])]]
  | _ => [.arrs [([3], [1])]]

/-- A single closure implements both signatures. `var 1` is the captured cell. -/
def dispatch : Tm := .lam (.ite (.test .isNul (.var 0)) (.read (.var 1)) .nul)

theorem dispatch_typed : HasTy G [[2]] dispatch [3] := by
  apply HasTy.lam (by rfl)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · apply HasTy.ifTag (q := true) (by rfl) (by intro c hc; simp [expand, G] at hc; subst c; rfl)
    · intro _; exact .read (.var rfl) (by rfl)
    · intro h; cases h
  · apply HasTy.ifTag (q := false) (by rfl) (by intro c hc; simp [expand, G] at hc; subst c; rfl)
    · intro h; cases h
    · intro _; exact .nul (by rfl)

/-- Genuine overload subsumption: splitting a union domain across two signatures. -/
def widenCert : Proof (Fin 6) := .core
  ⟨[([3], [4]), ([0], [0]), ([1], [1]), ([0], [0, 1]), ([1], [0, 1])],
    [([([0], [1]), ([1], [0])], (([0, 1], [0, 1]),
      .union [0] [1] (.source ([0], [1])) (.source ([1], [0]))))]⟩

#guard check G [3] [4] widenCert
#guard !(check G [4] [3] widenCert)

theorem dispatch_widened : HasTy G [[2]] dispatch [4] :=
  .sub dispatch_typed (by decide : check G [3] [4] widenCert = true)

/-- Lambda introduction also accepts function-valued parameters. -/
theorem higher_order_typed : HasTy G [] (.lam (.app (.var 0) .nul)) [5] := by
  apply HasTy.lam (by rfl)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst p
  exact .app (A := [0]) (.var rfl) (by rfl) (by simp) (.nul (by rfl))

theorem higher_order_safe (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G [5]) n W h (.lam (.app (.var 0) .nul)) :=
  higher_order_typed.closed_safe (by simp [Scoped]) n W h hw hh

/-- A lambda with a free variable is excluded even at budget zero. -/
theorem open_lambda_excluded (A B : Fam) (n W) :
    ¬ arrowT A B n W (.lam (.var 1)) := by
  rintro ⟨⟨b, hb, hc⟩, _⟩
  rcases hb with hb | ⟨l, hb⟩
  · cases hb; exact Nat.lt_irrefl 1 hc
  · cases hb

/--
let r = alloc true;
let f = (x => if isNull x then read r else null);
let alias = r;
let _ = write alias false;
let _ = f true;
f null
-/
def program : Tm :=
  .app (.lam (.app (.lam (.app (.lam (.app (.lam
    (.app (.lam (.app (.var 3) .nul)) (.app (.var 2) .tru)))
    (.write (.var 0) .fls))) (.var 1))) dispatch)) (.alloc .tru)

theorem program_typed : HasTy G [] program [0, 1] := by
  apply HasTy.letE (A := [2]) (.alloc (A := [1]) (.tru (by rfl)) (by rfl))
  apply HasTy.letE (A := [3]) dispatch_typed
  apply HasTy.letE (A := [2]) (.var rfl)
  apply HasTy.letE (A := [0]) (.write (.var rfl) (by rfl) (.fls (by rfl)) (by rfl))
  apply HasTy.letE (A := [0])
    (.app (A := [1]) (.var rfl) (by rfl) (by simp) (.tru (by rfl)))
  exact .app (A := [0, 1])
    (.sub (.var rfl) (by decide : check G [3] [4] widenCert = true)) (by rfl) (by simp)
    (.sub (.nul (by rfl)) (by decide : check G [0] [0, 1] .subset = true))

theorem program_safe (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G [0, 1]) n W h program :=
  program_typed.closed_safe
    (by simp [program, dispatch, Scoped]) n W h hw hh

/-- Reflexive transitive execution, used only to check observable behavior.
The safety theorem above does not use this trace. -/
inductive Runs : Heap → Tm → Heap → Tm → Prop where
  | done : Runs h t h t
  | next : Step h t h' t' → Runs h' t' h'' t'' → Runs h t h'' t''

theorem program_returns_false : Runs [] program [.fls] .fls := by
  apply Runs.next (.appR rfl (.allocV rfl))
  apply Runs.next (.beta rfl)
  apply Runs.next (.beta rfl)
  apply Runs.next (.beta rfl)
  apply Runs.next (.appR rfl (.writeV rfl (by decide)))
  apply Runs.next (.beta rfl)
  apply Runs.next (.appR rfl (.beta rfl))
  apply Runs.next (.appR rfl (.iteC (.testV rfl)))
  apply Runs.next (.appR rfl .iteF)
  apply Runs.next (.beta rfl)
  apply Runs.next (.beta rfl)
  apply Runs.next (.iteC (.testV rfl))
  apply Runs.next .iteT
  apply Runs.next (.readV rfl)
  exact .done

/-- A stuck application cannot receive a derivation, even with subsumption. -/
theorem stuck_not_typable (A : Ty (Fin 6)) : ¬ HasTy G [] (.app .nul .nul) A := by
  intro ht
  exact stuck_not_safe (meaning G A) 0 (ofList []) []
    (ht.closed_safe (by trivial) 1 _ [] WorldAdm_nil (emptyHeapOk 1))

#print axioms higher_order_safe
#print axioms program_safe
#print axioms program_returns_false
#print axioms stuck_not_typable
end Verification.ExperimentState.ProgramTypingTests
