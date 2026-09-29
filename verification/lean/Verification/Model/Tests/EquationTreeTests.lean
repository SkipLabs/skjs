import Verification.Model.Types.EquationValidator
import Verification.Model.Types.EquationJson

/-! Checks of the equation validator and the tree codec, which no request
reaches yet: representative round trips, one spelling per tree, and located
refusals of ill-formed heads and labels. -/
namespace Verification.Model.EquationTreeTests
open Lean Verification.Model.EquationGraphs PositiveGraphs PositiveNormalization CallEffects

private def union (ts : List Tree) : Types := Types.ofList ts
private def args (as : List (List Tree)) : Args := Args.ofList (as.map union)

private def roundTrip (t : Tree) : Bool :=
  match Tree.fromJson t.toJson with
  | .ok t' => t' == t
  | .error _ => false

private def refused (s : String) : Bool :=
  match Json.parse s with
  | .ok j => (Tree.fromJson j).toOption.isNone
  | .error _ => false

-- Round trips: every tree form, nested unions and arguments.
#guard roundTrip (.app 3 .nil)
#guard roundTrip (.app 7 (args [[.argument 0, .app 2 .nil], []]))
#guard roundTrip (.bound 4 .nil 1)
#guard roundTrip (.bound 4 (args [[.local 0]]) 2)
#guard roundTrip (.local 3)
#guard roundTrip (.var 9 1 .arguments)
#guard roundTrip (.meet (union [.app 1 .nil, .bound 4 (args [[.app 0 .nil]]) 0]))
#guard roundTrip (.app 5 (args [[.meet (union [.argument 0, .app 1 (args [[.var 2 0 .value]])])]]))

-- One spelling each.
#guard (Json.parse "3").toOption.map (fun j => (Tree.fromJson j).toOption) == some (some (.app 3 .nil))
#guard refused "{\"app\": 3, \"args\": []}"
#guard refused "{\"app\": 3}"
#guard refused "{\"bound\": 3, \"args\": [], \"slot\": 0}"
#guard refused "{\"arg\": 0, \"extra\": 1}"
#guard refused "{\"var\": 0, \"owner\": 1, \"kind\": \"pack\"}"
#guard refused "-1"
#guard refused "[3]"

/-! A head `Box<T>` whose body is a record with a field of type `T & Box<T>`,
next to `Unit`, a nullary head. -/
private def boxHeader : Header := { parameters := 1, binders := [], variance := [(.value, .co)] }
private def unitHeader : Header := { parameters := 0, binders := [] }
private def field (T : List Tree) : Clause (List Tree) := .refs [(.str "v", T)] [] []

private def box (T : List Tree) : RawHead :=
  { name := "Box", header := boxHeader, body := .clauses [field T] }
private def unit : RawHead := { name := "Unit", header := unitHeader, body := .clauses [.nul] }

private def accepted (heads : List RawHead) : Bool := (Equations.ofRaw heads).toOption.isSome

private def reason (heads : List RawHead) : String :=
  match Equations.ofRaw heads with
  | .ok _ => ""
  | .error e => e

#guard accepted [box [.meet (union [.app 0 (args [[.argument 0]]), .argument 0])], unit]
-- Meets in normal form only: two parts at least, flat, in canonical order.
#guard reason [box [.meet (union [.argument 0])], unit] ==
  "head 0 (Box): clause 0 operand 0 label 0: meet of 1 parts: at least two"
#guard !accepted [box [.meet (union [.argument 0, .app 0 (args [[.argument 0]])])], unit]
#guard !accepted [box [.meet (union [.app 1 .nil, .meet (union [.app 1 .nil, .argument 0])])], unit]
-- Scope, arity and lexicality.
#guard reason [box [.argument 1], unit] ==
  "head 0 (Box): clause 0 operand 0 label 0: arg 1 out of range: 1 parameters"
#guard reason [box [.app 0 .nil], unit] ==
  "head 0 (Box): clause 0 operand 0 label 0: head 0 takes 1 arguments, given 0"
#guard !accepted [box [.bound 0 (args [[.argument 0]]) 0], unit]
#guard !accepted [box [.var 0 0 .value], unit]
#guard !accepted [box [.local 0], unit]
-- Variance declared per parameter.
#guard reason [{ (box [.argument 0]) with header := { boxHeader with variance := [] } }, unit] ==
  "head 0 (Box): 0 variance declarations for 1 parameters"
-- Constructor-headed templates; a scheme binds exactly its locals.
#guard !accepted [{ name := "P", header := unitHeader, body := .param (.local 0) "T" .value }]
private def idHeader : Header := { parameters := 0, binders := [⟨"U", .value⟩] }
private def idArrow : Arrow (List Tree) := ⟨[], [[.local 0]], [.local 0], .unrestricted⟩
private def scheme (body : GraphRow Tree (List Tree)) : RawHead :=
  { name := "Id", header := idHeader, body := body }

#guard accepted [scheme (.scheme [.local 0] [idArrow] [] [])]
#guard !accepted [scheme (.scheme [] [idArrow] [] [])]
#guard !accepted [scheme (.scheme [.local 0] [] [(.local 0, [.local 0])] [])]

-- Kernel meets are canonical: flattened and sorted, so the validator reads
-- them back.
private def kernelMeet : Tree :=
  canonMeet [.app 1 .nil, .meet (union [.app 0 (args [[.app 1 .nil]]), .app 1 .nil]), .var 0 0 .value]
#guard (kernelMeet.meetParts).length == 4 && canonicalOrder kernelMeet.meetParts
#guard (Label.ofTree? (sig := [boxHeader, unitHeader]) kernelMeet).isSome
#guard kernelMeet == kernelMeet && !(kernelMeet == .app 1 .nil)

-- Closed labels.
private def sig : Signature := [boxHeader, unitHeader]
#guard (Label.ofTree? (sig := sig) (.app 0 (args [[.app 1 .nil]]))).isSome
#guard (Label.ofTree? (sig := sig) (.argument 0)).isNone
#guard (Label.ofTree? (sig := sig) (.meet (union [.app 1 .nil, .bound 0 (args [[.app 1 .nil]]) 0]))).isNone
#guard (Label.ofTree? (sig := sig) (.meet (union [.app 0 (args [[.app 1 .nil]]), .app 1 .nil]))).isSome

end Verification.Model.EquationTreeTests
