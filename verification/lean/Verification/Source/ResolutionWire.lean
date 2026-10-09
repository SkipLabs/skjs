import Verification.Types.Decode
import Verification.Types.PositiveGraphs

/- Strict finite resolution metadata. The wire records a proposal; its
semantic qualifications are established by the source certificate checker. -/
namespace Verification.ResolutionWire
open Lean

structure Slots where
  observation : String
  result : String
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson Slots where
  fromJson? j := do
    fieldsExactly j ["observation", "result"]
    let observation ← jStr (← jField j "observation")
    let result ← jStr (← jField j "result")
    if observation.isEmpty || result.isEmpty || observation == result then
      throw "resolution slots need distinct nonempty names"
    return ⟨observation, result⟩

/-- Names owned by a source binder, including its hidden projections. -/
def ownedNames (name : String) (resolution : Option Slots) : List String :=
  name :: (resolution.map fun r => [r.observation, r.result]).getD []

/-- Each projection belongs to one binder and shadows no other binder in
this signature. Lexical binding against an enclosing scope is checked there. -/
def validateOwnership (parameters : List (String × Option Slots)) : Except String Unit := do
  let names := parameters.flatMap fun (name, resolution) => ownedNames name resolution
  if names.any String.isEmpty || names.eraseDups.length != names.length then
    throw "duplicate or overlapping resolution binder names"

/-- Positional descriptor groups in the expanded signature binder list. -/
def groups (parameters : List (String × Option Slots)) : List PositiveGraphs.ResolutionSlots :=
  (parameters.foldl (fun (state : Nat × List PositiveGraphs.ResolutionSlots) p =>
    match p.2 with
    | none => (state.1 + 1, state.2)
    | some _ => (state.1 + 3, state.2 ++ [⟨state.1, state.1 + 1, state.1 + 2⟩])) (0, [])).2

structure Binder (T : Type) where
  name : String
  bound : Option T
  resolution : Option Slots
  deriving Repr, BEq, Inhabited

def Binder.ownedNames (b : Binder T) : List String := ResolutionWire.ownedNames b.name b.resolution

inductive Certificate where
  | stable
  | native (child : Certificate)
  | union (arms : List Certificate)
  | binder (name : String)
  deriving Repr, BEq, Inhabited

private partial def Certificate.encode : Certificate → Json
  | .stable => Json.mkObj [("k", toJson "stable")]
  | .native child => Json.mkObj [("k", toJson "native"), ("child", Certificate.encode child)]
  | .union arms => Json.mkObj [("k", toJson "union"), ("arms", toJson (arms.map Certificate.encode))]
  | .binder name => Json.mkObj [("k", toJson "binder"), ("binder", toJson name)]

instance : ToJson Certificate := ⟨Certificate.encode⟩

private partial def Certificate.fromJson (j : Json) : Except String Certificate := do
  match ← jStr (← jField j "k") with
  | "stable" =>
    fieldsExactly j ["k"]
    return .stable
  | "native" =>
    fieldsExactly j ["k", "child"]
    return .native (← Certificate.fromJson (← jField j "child"))
  | "union" =>
    fieldsExactly j ["k", "arms"]
    let arms ← jArr j "arms"
    if arms.isEmpty then throw "a resolution union needs an arm"
    return .union (← arms.mapM Certificate.fromJson)
  | "binder" =>
    fieldsExactly j ["k", "binder"]
    let name ← jStr (← jField j "binder")
    if name.isEmpty then throw "empty resolution certificate binder"
    return .binder name
  | _ => throw "unknown resolution certificate constructor"

instance : FromJson Certificate := ⟨Certificate.fromJson⟩

structure Instance where
  certificate : Certificate
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson Instance where
  fromJson? j := do
    fieldsExactly j ["certificate"]
    return ⟨← fromJson? (← jField j "certificate")⟩

end Verification.ResolutionWire
