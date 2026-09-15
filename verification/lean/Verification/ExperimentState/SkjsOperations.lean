import Verification.ExperimentState.CertificateProducer
import Verification.ExperimentState.Fragment
import Verification.ExperimentState.CellClaims

/-! Independent checking of SKJS's closed subtype and expansion judgments.
Each operation is serialized under the substitution in force at the judgment.
Types that do not lower into the source fragment are skipped; a translated
inclusion is accepted only when the existing subtype consumer accepts a
derivation. Failure to find a derivation is not a semantic disproof. -/
namespace Verification.ExperimentState.SkjsOperations
open Lean CertificateProducer PositiveCertificates SourceTypes ProgramTyping

inductive Outcome where
  | skipped (reason : String)
  | checked
  | unproved
  deriving Repr, DecidableEq

def inclusion (A B : Ty Nat) (T : Table) : Outcome :=
  let G := graph T
  let pool := (A :: B :: (List.range T.length).map (fun i => [i])).eraseDups
  match subtype G pool A B with
  | some p => if check G A B p then .checked else .unproved
  | none => .unproved

def pair (kind : String) (source target : Json) : Except String Outcome := do
  match kind with
  | "subtype" | "expand" => pure ()
  | other => throw s!"unknown operation kind '{other}'"
  match (Fragment.translate source).run initial with
  | .error e => return .skipped e
  | .ok (A, T₁) =>
    match (Fragment.translate target).run T₁ with
    | .error e => return .skipped e
    | .ok (B, T) =>
      let forward := inclusion A B T
      if kind == "subtype" then return forward
      -- Exact expansion: the clause view must denote the same type.
      match forward, inclusion B A T with
      | .checked, .checked => return .checked
      | .skipped r, _ => return .skipped r
      | _, .skipped r => return .skipped r
      | _, _ => return .unproved

def operation (j : Json) : Except String Outcome := do
  CellClaims.fieldsExactly j ["kind", "source", "target"]
  pair (← jStr (← jField j "kind")) (← jField j "source") (← jField j "target")

structure Report where
  checked : Nat := 0
  skipped : Nat := 0
  unproved : Nat := 0

def add (r : Report) : Outcome → Report
  | .checked => { r with checked := r.checked + 1 }
  | .skipped _ => { r with skipped := r.skipped + 1 }
  | .unproved => { r with unproved := r.unproved + 1 }

def functionOps (j : Json) : Except String (List Json) :=
  jArr j "operations"

def document (j : Json) : Except String Report := do
  let files ← j.getArr?
  files.toList.foldlM (fun acc file => do
    (← jArr file "functions").foldlM (fun acc f => do
      (← functionOps f).foldlM (fun acc op => do return add acc (← operation op)) acc)
      acc) {}

def checkJson (j : Json) : Except String Report := do
  let r ← document j
  if r.unproved != 0 then
    throw s!"unproved closed operation ({r.checked} checked, {r.skipped} skipped, {r.unproved} unproved)"
  return r

private def trueTy : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "booleanlit"), ("v", toJson "true")]])]
private def falseTy : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "booleanlit"), ("v", toJson "false")]])]
private def boolTy : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "boolean")]])]

#guard (match pair "subtype" trueTy boolTy with | .ok .checked => true | _ => false)
#guard (match pair "subtype" trueTy falseTy with | .ok .unproved => true | _ => false)
#guard (match pair "expand" boolTy boolTy with | .ok .checked => true | _ => false)
private def numTy : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "number")]])]

private def oneTy : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "numberlit"), ("v", toJson "1")]])]

-- Numbers are in the slice now, so this is decided rather than skipped: no
-- number is a boolean, and the judgment is refused on the merits.
#guard (match pair "subtype" numTy boolTy with | .ok .unproved => true | _ => false)
-- A numeric singleton is below the family, and distinct singletons are not
-- comparable. `1.0` is `1`: the literal's identity is the double it denotes.
#guard (match pair "subtype" oneTy numTy with | .ok .checked => true | _ => false)
#guard (match pair "subtype" numTy oneTy with | .ok .unproved => true | _ => false)
#guard (match pair "expand" numTy numTy with | .ok .checked => true | _ => false)

end Verification.ExperimentState.SkjsOperations
