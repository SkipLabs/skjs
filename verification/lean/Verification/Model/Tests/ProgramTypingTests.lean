import Verification.Model.Programs.ProgramTyping

namespace Verification.Model.ProgramTypingTests
open PositiveNormalization PositiveGraphs PositiveRules PositiveCertificates ProgramTyping

/-- Label 6 is `undefined`, the receiver every signature here is called with. -/
def G : NormalGraph (Fin 7) := .ofRows fun i => match i.val with
  | 0 => [.nul]
  | 1 => [.bool]
  | 2 => [.refs [(valueField, [1])] [] []]
  | 3 => [.arrs [⟨[6], [[0]], [1], .unrestricted⟩, ⟨[6], [[1]], [0], .unrestricted⟩] []]
  | 4 => [.arrs [⟨[6], [[0, 1]], [0, 1], .unrestricted⟩] []]
  | 5 => [.arrs [⟨[6], [[3]], [1], .unrestricted⟩] []]
  | _ => [.undef]

/-- A single closure implementing both signatures of label 3: graph code of one
node, run from the frame of its receiver (`var 0`), its parameter (`var 1`) and
the captured cell (`var 2`). -/
def dispatch : Tm :=
  .make (.graph 1 [.ite (.test .isNul (.var 1)) (.read (.var 2)) .nul] [(.ret, none)] 0 [.var 0]) .nul

/-- Genuine overload subsumption: splitting a union domain across two signatures. -/
def widenCert : Proof (Fin 7) := .core
  ⟨[([3], [4]), ([0], [0]), ([1], [1]), ([0], [0, 1]), ([1], [0, 1]), ([6], [6])],
    [([⟨[6], [[0]], [1], .unrestricted⟩, ⟨[6], [[1]], [0], .unrestricted⟩], (⟨[6], [[0, 1]], [0, 1], .unrestricted⟩,
      .union [] [0] [1] [] (.source ⟨[6], [[0]], [1], .unrestricted⟩) (.source ⟨[6], [[1]], [0], .unrestricted⟩)))]⟩

#guard check G [3] [4] widenCert
#guard !(check G [4] [3] widenCert)

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
  apply HasTyUsing.letE (A := [2]) (.alloc (parts := [(valueField, [1], .tru)]) (by simp)
    (by intro p hp; cases List.mem_singleton.mp hp; exact .tru (by rfl)) (by rfl) (by simp) (by decide))
  apply HasTyUsing.letE (A := [2]) (.var rfl)
  apply HasTyUsing.letE (A := [0]) (.write (A := [1]) (.var rfl) (by rfl) (by simp) (.fls (by rfl)) (by rfl))
  apply HasTyUsing.letE (A := [0])
    (.app (effect := .unrestricted) (Rt := [6]) (xs := [([1],.tru)]) (Us := []) (.var rfl) (by rfl) (by simp) (.undef (by rfl))
      (by intro p hp; cases List.mem_singleton.mp hp; exact .tru (by rfl)) (by simp))
  exact .app (effect := .unrestricted) (Rt := [6]) (xs := [([0,1],.nul)]) (Us := [])
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
  apply Runs.next (.letC (.callGraph rfl (by decide)))
  apply Runs.next (.letC (.gotoEnter rfl rfl))
  apply Runs.next (.letC (.frameC (.iteC (.testV rfl))))
  apply Runs.next (.letC (.frameC .iteF))
  apply Runs.next (.letC (.frameRet rfl))
  apply Runs.next (.letV rfl)
  apply Runs.next (.callGraph rfl (by decide))
  apply Runs.next (.gotoEnter rfl rfl)
  apply Runs.next (.frameC (.iteC (.testV rfl)))
  apply Runs.next (.frameC .iteT)
  apply Runs.next (.frameC (.readV rfl))
  apply Runs.next (.frameRet rfl)
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
