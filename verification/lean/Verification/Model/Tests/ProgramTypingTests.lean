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

/-- A single closure implementing both signatures of label 3: `var 0` is its
receiver, `var 1` its parameter and `var 2` the captured cell. Its code is a
term here, run below by the machine; the checked closures are graph code
(`GraphCode`), whose rules the source pipeline exercises. -/
def dispatch : Tm := .funE (.ite (.test .isNul (.var 1)) (.read (.var 2)) .nul)

/-- Genuine overload subsumption: splitting a union domain across two signatures. -/
def widenCert : Proof (Fin 7) := .core
  ⟨[([3], [4]), ([0], [0]), ([1], [1]), ([0], [0, 1]), ([1], [0, 1]), ([6], [6])],
    [([([6], [[0]], [1]), ([6], [[1]], [0])], (([6], [[0, 1]], [0, 1]),
      .union [] [0] [1] [] (.source ([6], [[0]], [1])) (.source ([6], [[1]], [0]))))]⟩

#guard check G [3] [4] widenCert
#guard !(check G [4] [3] widenCert)

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

/-- The program's body, with `f` a slot of its context at label 3: allocation,
aliasing, a write through the alias and two calls, the second through the
widened signature. -/
def programBody : Tm :=
  .letE (.alloc .tru)
    (.letE (.var 0)
      (.letE (.write (.var 0) .fls)
        (.letE (.app (.var 3) .tru) (.app (.var 4) .nul))))

theorem program_typed : HasTy G [[3]] programBody [0, 1] := by
  apply HasTy.letE (A := [2]) (.alloc (parts := [(valueField, [1], .tru)]) (by simp)
    (by intro p hp; cases List.mem_singleton.mp hp; exact .tru (by rfl)) (by rfl) (by simp) (by decide))
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

#print axioms program_typed
#print axioms program_returns_false
#print axioms stuck_not_typable
end Verification.Model.ProgramTypingTests
