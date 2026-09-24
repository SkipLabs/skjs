import Verification.Model.Source.DeclarationGraph

/-! Binder-role classification is structural and lexical. Inner binders must
not turn an outer pack into a mixed value/pack parameter. -/
namespace Verification.Model.DeclarationBinderTests
open Lean DeclarationGraph

private def binder (name : String) : Json :=
  Json.mkObj [("k", .str "binder"), ("name", .str name)]

private def pack (name : String) : Json :=
  Json.mkObj [("k", .str "pack"), ("of", binder name)]

private def nested : Json := Json.mkObj [
  ("k", .str "scheme"),
  ("binders", .arr #[Json.mkObj [("name", .str "P")]]),
  ("signatures", .arr #[binder "P", binder "Outer"])]

-- The inner P is a value parameter; the outer P is used only as a pack.
#guard binderUse "P" (.arr #[pack "P", nested]) == ⟨false, true⟩
-- A differently named outer binder remains free inside that inner scheme.
#guard binderUse "Outer" nested == ⟨true, false⟩
-- Real mixed use is retained, so the lowering can keep refusing it explicitly.
#guard binderUse "P" (.arr #[pack "P", binder "P"]) == ⟨true, true⟩
-- Printed data is not a binder occurrence.
#guard binderUse "P" (.str (binder "P").compress) == ⟨false, false⟩

end Verification.Model.DeclarationBinderTests
