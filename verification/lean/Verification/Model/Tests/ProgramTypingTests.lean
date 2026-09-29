import Verification.Model.Programs.ProgramTyping

/-! The program-typing fixtures the program tests share: an overloaded graph,
a closure implementing it, and a program using it through a widened
signature. -/
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
def widenCert : Proof (Fin 7) := .family
  { entries := [{ source := [3], target := [4], table := [([3], [4]), ([0], [0, 1]), ([1], [0, 1])] }],
    arrows := [([⟨[6], [[0]], [1], .unrestricted⟩, ⟨[6], [[1]], [0], .unrestricted⟩], (⟨[6], [[0, 1]], [0, 1], .unrestricted⟩,
      .union [] [0] [1] [] (.source ⟨[6], [[0]], [1], .unrestricted⟩) (.source ⟨[6], [[1]], [0], .unrestricted⟩)))] }

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

end Verification.Model.ProgramTypingTests
