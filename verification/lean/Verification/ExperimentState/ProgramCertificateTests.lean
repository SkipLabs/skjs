import Verification.ExperimentState.ProgramCertificates
import Verification.ExperimentState.ProgramTypingTests

namespace Verification.ExperimentState.ProgramCertificateTests
open ProgramTyping ProgramTypingTests ProgramCertificates

private def leaf (Γ : List (Ty (Fin 6))) (t : Tm) (A : Ty (Fin 6)) (r : Rule (Fin 6)) : Evidence (Fin 6) :=
  .node ⟨Γ, t, A⟩ r []
private def varE (Γ : List (Ty (Fin 6))) (i : Nat) (A : Ty (Fin 6)) := leaf Γ (.var i) A .var
private def subE (e : Evidence (Fin 6)) (B : Ty (Fin 6)) (p : PositiveCertificates.Proof (Fin 6)) : Evidence (Fin 6) :=
  .node ⟨(claim e).context, (claim e).term, B⟩ (.sub p) [e]
private def appE (f a : Evidence (Fin 6)) (B : Ty (Fin 6)) : Evidence (Fin 6) :=
  .node ⟨(claim f).context, .app (claim f).term (claim a).term, B⟩ .app [f,a]
private def letE (a b : Evidence (Fin 6)) : Evidence (Fin 6) :=
  .node ⟨(claim a).context, .letE (claim a).term (claim b).term, (claim b).type⟩ .letE [a,b]

def dispatchEvidence : Evidence (Fin 6) :=
  .node ⟨[[2]], dispatch, [3]⟩ .funE
    [.node ⟨[[0],[2]], .ite (.test .isNul (.var 0)) (.read (.var 1)) .nul, [1]⟩ .ifTrue
      [.node ⟨[[0],[2]], .read (.var 1), [1]⟩ .read [varE [[0],[2]] 1 [2]]],
     .node ⟨[[1],[2]], .ite (.test .isNul (.var 0)) (.read (.var 1)) .nul, [0]⟩ .ifFalse
      [leaf [[1],[2]] .nul [0] .nul]]

/-- Explicit data, with no embedded Lean typing proof. -/
def programEvidence : Evidence (Fin 6) :=
  letE (.node ⟨[], .alloc .tru, [2]⟩ .alloc [leaf [] .tru [1] .tru])
    (letE dispatchEvidence
      (letE (varE [[3],[2]] 1 [2])
        (letE (.node ⟨[[2],[3],[2]], .write (.var 0) .fls, [0]⟩ .write
          [varE [[2],[3],[2]] 0 [2], leaf [[2],[3],[2]] .fls [1] .fls])
          (letE (appE (varE [[0],[2],[3],[2]] 2 [3])
            (leaf [[0],[2],[3],[2]] .tru [1] .tru) [0])
            (appE (subE (varE [[0],[0],[2],[3],[2]] 3 [3]) [4] widenCert)
              (subE (leaf [[0],[0],[2],[3],[2]] .nul [0] .nul) [0,1] .subset) [0,1])))))

#guard check G program [0,1] programEvidence
#guard !(check G .nul [0,1] programEvidence)
#guard !(check G program [1] programEvidence)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
/-- The consumer obtains safety directly from the executable check. -/
theorem checked_program_safe (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (PositiveRules.meaning G [0,1]) n W h program :=
  accepted_safe (by cbv : check G program [0,1] programEvidence = true) n W h hw hh

private def dropPremise : Evidence ι → Evidence ι
  | .node j r ps => .node j r ps.tail
private def wrongRule (r : Rule ι) : Evidence ι → Evidence ι
  | .node j _ ps => .node j r ps
private def wrongContext (Γ : List (Ty ι)) : Evidence ι → Evidence ι
  | .node j r ps => .node {j with context := Γ} r ps

-- Every overload must be checked, with its own parameter and captured context.
#guard !(checkTree G (dropPremise dispatchEvidence))
#guard !(checkTree G (wrongContext [[1]] dispatchEvidence))
#guard !(checkTree G (wrongRule .ifFalse
  (.node ⟨[[0],[2]], .ite (.test .isNul (.var 0)) (.read (.var 1)) .nul, [1]⟩ .ifTrue
    [.node ⟨[[0],[2]], .read (.var 1), [1]⟩ .read [varE [[0],[2]] 1 [2]]])))

-- An invented write or subtype fact cannot be supplied as evidence.
#guard !(checkTree G (.node ⟨[[2]], .write (.var 0) .nul, [0]⟩ .write
  [varE [[2]] 0 [2], leaf [[2]] .nul [0] .nul]))
#guard !(checkTree G (subE dispatchEvidence [4] (.core ⟨[],[]⟩)))
#guard !(checkTree G (.node ⟨[[0]], .var 0, [0]⟩ .var [varE [[0]] 0 [0]]))

-- The empty overload imposes no body obligations, but cannot bypass scope.
private def EmptyG : PositiveGraphs.NormalGraph (Fin 1) := fun _ => [.arrs []]
private def openEvidence : Evidence (Fin 1) := .node ⟨[], .funE (.var 1), [0]⟩ .funE []
#guard checkTree EmptyG openEvidence
#guard !(check EmptyG (.funE (.var 1)) [0] openEvidence)

#print axioms checked_program_safe
end Verification.ExperimentState.ProgramCertificateTests
