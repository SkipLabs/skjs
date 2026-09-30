import Verification.Model.Source.RequestJson

namespace Verification.Model.RequestJsonTests
open Lean ProgramTyping ControlFlow RequestJson PositiveNormalization

def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

-- A string key keeps its JSON string; a symbol key is `{"symbol": id}`, and
-- the two never decode to each other.
#guard (fromJson? (Json.str "3") : Except String PropKey).toOption == some (.str "3")
#guard !(ok (fromJson? (Json.mkObj [("symbol", toJson (3 : Nat)), ("x", Json.null)]) : Except String PropKey))

-- Defaults and unsupported source refinements cannot silently enter the format.
#guard !(ok (decodeStrict (α := Target) (Json.mkObj [("label",toJson (0 : Nat))])))

end Verification.Model.RequestJsonTests
