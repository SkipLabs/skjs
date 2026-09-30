import Verification.Model.Source.RequestJson

namespace Verification.Model.RequestJsonTests
open Lean ProgramTyping ControlFlow RequestJson PositiveNormalization

def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

-- A string key keeps its JSON string; a symbol key is `{"symbol": id}`, and
-- the two never decode to each other.
#guard toJson (PropKey.str "a") == Json.str "a"
#guard toJson (PropKey.sym 3) == Json.mkObj [("symbol", toJson (3 : Nat))]
#guard (fromJson? (toJson (PropKey.sym 3)) : Except String PropKey).toOption == some (.sym 3)
#guard (fromJson? (Json.str "3") : Except String PropKey).toOption == some (.str "3")
#guard !(ok (fromJson? (Json.mkObj [("symbol", toJson (3 : Nat)), ("x", Json.null)]) : Except String PropKey))

-- Defaults and unsupported source refinements cannot silently enter the format.
#guard !(ok (decodeStrict (α := Target) (Json.mkObj [("label",toJson (0 : Nat))])))

-- Field order is immaterial, but a missing or extra field is a difference.
#guard !(sameJson (Json.mkObj [("x",toJson (0 : Nat))])
  (Json.mkObj [("x",toJson (0 : Nat)),("y",toJson (1 : Nat))]))

-- Graph code's kind and rest are spelled only when not `call` and `false`.
#guard !((toJson (Tm.objAt [] (.graph 1 [] [] 0 []))).compress.contains "kind")
#guard !((toJson (Tm.objAt [] (.graph 1 [] [] 0 []))).compress.contains "rest")
#guard (fromJson? (toJson (Tm.objAt [] (.graph 1 [] [] 0 [] .construct))) : Except String Tm).toOption ==
  some (Tm.objAt [] (.graph 1 [] [] 0 [] .construct))
#guard (fromJson? (toJson (Tm.objAt [] (.graph 1 [] [] 0 [] .call true))) : Except String Tm).toOption ==
  some (Tm.objAt [] (.graph 1 [] [] 0 [] .call true))
#guard (fromJson? (toJson (Tm.construct (.var 0) [.tru])) : Except String Tm).toOption ==
  some (Tm.construct (.var 0) [.tru])
#guard (fromJson? (toJson ([Clause.ctors [([[1, 2]], [1, 2])]] : List (Clause (List Nat))))
  : Except String (List (Clause (List Nat)))).toOption == some [Clause.ctors [([[1, 2]], [1, 2])]]

end Verification.Model.RequestJsonTests
