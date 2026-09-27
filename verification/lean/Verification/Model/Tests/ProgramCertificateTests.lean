import Verification.Model.Programs.ProgramCertificates
import Verification.Model.Tests.ProgramTypingTests

namespace Verification.Model.ProgramCertificateTests
open ProgramTyping ProgramTypingTests ProgramCertificates

private def leaf (Γ : List (Ty (Fin 7))) (t : Tm) (A : Ty (Fin 7)) (r : Rule (Fin 7)) : Evidence (Fin 7) :=
  .node ⟨Γ, t, A⟩ r []
private def varE (Γ : List (Ty (Fin 7))) (i : Nat) (A : Ty (Fin 7)) := leaf Γ (.var i) A .var
private def subE (e : Evidence (Fin 7)) (B : Ty (Fin 7)) (p : PositiveCertificates.Proof (Fin 7)) : Evidence (Fin 7) :=
  .node ⟨(claim e).context, (claim e).term, B⟩ (.sub p) [e]
/-- A plain call: the callee, the `undefined` receiver at label 6, the actual. -/
private def appE (f a : Evidence (Fin 7)) (B : Ty (Fin 7)) : Evidence (Fin 7) :=
  .node ⟨(claim f).context, .app (claim f).term (claim a).term, B⟩ (.app .unrestricted)
    [f, .node ⟨(claim f).context, .undef, [6]⟩ .undef [], a]
private def letE (a b : Evidence (Fin 7)) : Evidence (Fin 7) :=
  .node ⟨(claim a).context, .letE (claim a).term (claim b).term, (claim b).type⟩ .letE [a,b]

/-- Explicit data, with no embedded Lean typing proof: the program's body, with
the dispatching function in slot 0 of its context. -/
def programEvidence : Evidence (Fin 7) :=
  letE (.node ⟨[[3]], .alloc .tru, [2]⟩ .alloc [leaf [[3]] .tru [1] .tru])
    (letE (varE [[2],[3]] 0 [2])
      (letE (.node ⟨[[2],[2],[3]], .write (.var 0) .fls, [0]⟩ .write
        [varE [[2],[2],[3]] 0 [2], leaf [[2],[2],[3]] .fls [1] .fls])
        (letE (appE (varE [[0],[2],[2],[3]] 3 [3]) (leaf [[0],[2],[2],[3]] .tru [1] .tru) [0])
          (appE (subE (varE [[0],[0],[2],[2],[3]] 4 [3]) [4] widenCert)
            (subE (leaf [[0],[0],[2],[2],[3]] .nul [0] .nul) [0,1] .subset) [0,1]))))

#guard checkTree G programEvidence && claim programEvidence == ⟨[[3]], programBody, [0,1]⟩

private def dropPremise : Evidence ι → Evidence ι
  | .node j r ps => .node j r ps.tail
private def wrongRule (r : Rule ι) : Evidence ι → Evidence ι
  | .node j _ ps => .node j r ps
private def wrongResult (A : Ty ι) : Evidence ι → Evidence ι
  | .node j r ps => .node {j with type := A} r ps
#guard !(checkTree G (wrongResult [1] programEvidence))
private def wrongContext (Γ : List (Ty ι)) : Evidence ι → Evidence ι
  | .node j r ps => .node {j with context := Γ} r ps

-- A premise dropped, a rule changed or a context changed is refused.
private def writeEvidence : Evidence (Fin 7) :=
  .node ⟨[[2]], .write (.var 0) .fls, [0]⟩ .write [varE [[2]] 0 [2], leaf [[2]] .fls [1] .fls]
#guard checkTree G writeEvidence
#guard !(checkTree G (dropPremise writeEvidence))
#guard !(checkTree G (wrongRule .read writeEvidence))
#guard !(checkTree G (wrongContext [[1]] writeEvidence))

-- An invented write or subtype fact cannot be supplied as evidence.
#guard !(checkTree G (.node ⟨[[2]], .write (.var 0) .nul, [0]⟩ .write
  [varE [[2]] 0 [2], leaf [[2]] .nul [0] .nul]))
#guard !(checkTree G (subE (varE [[3]] 0 [3]) [4] (.core ⟨[],[]⟩)))
#guard !(checkTree G (.node ⟨[[0]], .var 0, [0]⟩ .var [varE [[0]] 0 [0]]))

-- The empty overload names no code of the table, but its captures cannot
-- bypass scope: each is a slot of the context.
private def EmptyG : PositiveGraphs.NormalGraph (Fin 1) := .ofRows fun _ => [.arrs [] []]
private def openCode : Tm := .make (.graph 1 [] [] 0 [.var 2]) .nul
private def openEvidence : Evidence (Fin 1) :=
  .node ⟨[], openCode, [0]⟩ (.funGraph []) [.node ⟨[], .var 2, [0]⟩ .var []]
#guard !checkTree EmptyG openEvidence
#guard !(check EmptyG openCode [0] openEvidence)
#guard checkTree EmptyG (.node ⟨[], .make (.graph 1 [] [] 0 []) .nul, [0]⟩ (.funGraph []) [])

end Verification.Model.ProgramCertificateTests
