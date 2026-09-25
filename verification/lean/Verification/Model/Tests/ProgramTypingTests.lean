import Verification.Model.Programs.ProgramTyping

namespace Verification.Model.ProgramTypingTests
open PositiveNormalization PositiveGraphs PositiveRules PositiveCertificates ProgramTyping

/-- Label 6 is `undefined`, the receiver every signature here is called with. -/
def G : NormalGraph (Fin 7) := .ofRows fun i => match i.val with
  | 0 => [.nul]
  | 1 => [.bool]
  | 2 => [.refs [(valueField, [1])] [] []]
  | 3 => [.arrs [([6], [[0]], [1]), ([6], [[1]], [0])] []]
  | 4 => [.arrs [([6], [[0, 1]], [0, 1])] []]
  | 5 => [.arrs [([6], [[3]], [1])] []]
  | _ => [.undef]

/-- A single closure implements both signatures. `var 0` is its receiver,
`var 1` its parameter and `var 2` the captured cell. -/
def dispatch : Tm := .funE (.ite (.test .isNul (.var 1)) (.read (.var 2)) .nul)

theorem dispatch_typed : HasTy G [[2]] dispatch [3] := by
  apply HasTy.funE (by rfl) (by decide)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · apply HasTy.ifTag (q := true) (by rfl) ⟨rfl, by intro c hc; simp [expand, clausesOf, G] at hc; subst c; rfl⟩
    · intro _; exact .read (.var rfl) (by rfl) (by simp)
    · intro h; cases h
  · apply HasTy.ifTag (q := false) (by rfl) ⟨rfl, by intro c hc; simp [expand, clausesOf, G] at hc; subst c; rfl⟩
    · intro h; cases h
    · intro _; exact .nul (by rfl)

/-- Genuine overload subsumption: splitting a union domain across two signatures. -/
def widenCert : Proof (Fin 7) := .core
  ⟨[([3], [4]), ([0], [0]), ([1], [1]), ([0], [0, 1]), ([1], [0, 1]), ([6], [6])],
    [([([6], [[0]], [1]), ([6], [[1]], [0])], (([6], [[0, 1]], [0, 1]),
      .union [] [0] [1] [] (.source ([6], [[0]], [1])) (.source ([6], [[1]], [0]))))]⟩

#guard check G [3] [4] widenCert
#guard !(check G [4] [3] widenCert)

theorem dispatch_widened : HasTy G [[2]] dispatch [4] :=
  .sub dispatch_typed (by decide : check G [3] [4] widenCert = true)

/-- Lambda introduction also accepts function-valued parameters. -/
theorem higher_order_typed : HasTy G [] (.funE (.app (.var 1) .nul)) [5] := by
  apply HasTy.funE (by rfl) (by decide)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst p
  exact .app (Rt := [6]) (xs := [([0],.nul)]) (Us := []) (.var rfl) (by rfl) (by simp) (.undef (by rfl))
    (by intro p hp; cases List.mem_singleton.mp hp; exact .nul (by rfl)) (by simp)

theorem higher_order_safe (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G [5]) n W h (.funE (.app (.var 1) .nul)) :=
  higher_order_typed.closed_safe (by simp [Scoped]) n W h hw hh

/-- A lambda with a free variable is excluded even at budget zero. Slot 0 is
its receiver and slot 1 its parameter; slot 2 is free. -/
theorem open_lambda_excluded (A B : Fam) (n W) :
    ¬ arrowT A B n W (.fn 0 (.var 2)) := by
  rintro ⟨⟨arity, b, l, he, hc⟩, _⟩
  cases he
  exact Nat.lt_irrefl 2 hc

/--
let r = alloc true;
let f = (x => if isNull x then read r else null);
let alias = r;
let _ = write alias false;
let _ = f true;
f null
-/
def program : Tm :=
  .letE (.alloc .tru)
    (.letE dispatch
      (.letE (.var 1)
        (.letE (.write (.var 0) .fls)
          (.letE (.app (.var 2) .tru) (.app (.var 3) .nul)))))

theorem program_typed : HasTy G [] program [0, 1] := by
  apply HasTy.letE (A := [2]) (.alloc (parts := [(valueField, [1], .tru)]) (by simp)
    (by intro p hp; cases List.mem_singleton.mp hp; exact .tru (by rfl)) (by rfl) (by simp))
  apply HasTy.letE (A := [3]) dispatch_typed
  apply HasTy.letE (A := [2]) (.var rfl)
  apply HasTy.letE (A := [0]) (.write (A := [1]) (.var rfl) (by rfl) (by simp) (.fls (by rfl)) (by rfl))
  apply HasTy.letE (A := [0])
    (.app (Rt := [6]) (xs := [([1],.tru)]) (Us := []) (.var rfl) (by rfl) (by simp) (.undef (by rfl))
      (by intro p hp; cases List.mem_singleton.mp hp; exact .tru (by rfl)) (by simp))
  exact .app (Rt := [6]) (xs := [([0,1],.nul)]) (Us := [])
    (.sub (.var rfl) (by decide : check G [3] [4] widenCert = true)) (by rfl) (by simp)
    (.undef (by rfl))
    (by intro p hp; cases List.mem_singleton.mp hp
        exact .sub (.nul (by rfl)) (by decide : check G [0] [0, 1] .subset = true)) (by simp)

theorem program_safe (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G [0, 1]) n W h program :=
  program_typed.closed_safe
    (by simp [program, dispatch, Scoped]) n W h hw hh

/-- Reflexive transitive execution, used only to check observable behavior.
The safety theorem above does not use this trace. -/
inductive Runs : Heap → Tm → Heap → Tm → Prop where
  | done : Runs h t h t
  | next : Step h t h' t' → Runs h' t' h'' t'' → Runs h t h'' t''

theorem program_returns_false : Runs [] program [.fls,.nul] .fls := by
  apply Runs.next (.letC (.makeV rfl))
  apply Runs.next (.letV rfl)
  apply Runs.next (.letC (.makeV rfl))
  apply Runs.next (.letV rfl)
  apply Runs.next (.letV rfl)
  apply Runs.next (.letC (.writeV rfl (by decide)))
  apply Runs.next (.letV rfl)
  apply Runs.next (.letC (.beta rfl))
  apply Runs.next (.letC (.iteC (.testV rfl)))
  apply Runs.next (.letC .iteF)
  apply Runs.next (.letV rfl)
  apply Runs.next (.beta rfl)
  apply Runs.next (.iteC (.testV rfl))
  apply Runs.next .iteT
  apply Runs.next (.readV rfl)
  exact .done

/-- A stuck application cannot receive a derivation, even with subsumption. -/
theorem stuck_not_typable (A : Ty (Fin 7)) : ¬ HasTy G [] (.app .nul .nul) A := by
  intro ht
  exact stuck_not_safe (meaning G A) 0 (ofList []) []
    (ht.closed_safe (by trivial) 1 _ [] WorldAdm_nil (emptyHeapOk 1))

#print axioms higher_order_safe
#print axioms program_safe
#print axioms program_returns_false
#print axioms stuck_not_typable
end Verification.Model.ProgramTypingTests
