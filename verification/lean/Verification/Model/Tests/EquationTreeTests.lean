import Verification.Model.Types.EquationValidator
import Verification.Model.Types.EquationJson

/-! The tree codec's one spelling per tree, and the validator's refusal of a
nested meet. -/
namespace Verification.Model.EquationTreeTests
open Lean Verification.Model.EquationGraphs PositiveGraphs PositiveNormalization CallEffects

private def union (ts : List Tree) : Types := Types.ofList ts

private def refused (s : String) : Bool :=
  match Json.parse s with
  | .ok j => (Tree.fromJson j).toOption.isNone
  | .error _ => false

-- One spelling each.
#guard refused "{\"app\": 3, \"args\": []}"
#guard refused "{\"app\": 3}"
#guard refused "{\"bound\": 3, \"args\": [], \"slot\": 0}"
#guard refused "{\"arg\": 0, \"extra\": 1}"
#guard refused "{\"var\": 0, \"owner\": 1, \"kind\": \"pack\"}"
#guard refused "-1"
#guard refused "[3]"

/-! A head `Box<T>` whose body is a record with a field of type `T & Box<T>`,
next to `Unit`, a nullary head. -/
private def boxHeader : Header := { parameters := 1, binders := [], kinds := [.value] }
private def unitHeader : Header := { parameters := 0, binders := [] }
private def field (T : List Tree) : Clause (List Tree) := .refs [(.str "v", T)] [] []

private def box (T : List Tree) : RawHead :=
  { name := "Box", header := boxHeader, body := .clauses [field T] }
private def unit : RawHead := { name := "Unit", header := unitHeader, body := .clauses [.nul] }

private def accepted (heads : List RawHead) : Bool := (Equations.ofRaw heads).toOption.isSome

-- Meets in normal form only: flat.
#guard !accepted [box [.meet (union [.app 1 .nil, .meet (union [.app 1 .nil, .argument 0])])], unit]
end Verification.Model.EquationTreeTests
