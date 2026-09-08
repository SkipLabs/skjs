import Verification.ExperimentState.CellClaims

/-! Integration-test executable only. Reads actual SKJS exports; it does not
claim that the source cell fragment already reaches the program consumer. -/
open Lean Verification Verification.ExperimentState

private def Option.toExcept (o : Option α) (message : String) : Except String α :=
  match o with | some a => .ok a | none => .error message

private def put (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj (fields.toList.map (fun (k,v) => (k,if k == key then value else v)))
  | _ => j

private def fieldMap (j : Json) (f : Json → Json) : Except String Json := do
  let a ← (← jArr j "atoms").head?.toExcept "missing record"
  let field ← (← jArr a "fields").head?.toExcept "missing field"
  return put j "atoms" (toJson [put a "fields" (toJson [f field])])

private def atomMap (j : Json) (f : Json → Json) : Except String Json := do
  let a ← (← jArr j "atoms").head?.toExcept "missing record"
  return put j "atoms" (toJson [f a])

private def expect (label : String) (test : Bool) : Except String String :=
  if test then .ok s!"  {label}: OK" else .error s!"{label}: unexpected cell-contract result"

private def is (j : Json) (expected : List Nat) : Bool :=
  match CellClaims.translate j with | .ok A => A == expected | .error _ => false
private def rejects (j : Json) : Bool :=
  match CellClaims.translate j with | .ok _ => false | .error _ => true

private def checks (claims : Json) (fileKey : String) : Except String (List String) := do
  let file ← ((← claims.getArr?).toList.find? (fun f => (f.getObjValAs? String "file").toOption == some fileKey)).toExcept "missing fixture file"
  let fs ← jArr file "functions"
  let param := fun name => do
    let f ← (fs.find? (fun f => (f.getObjValAs? String "name").toOption == some name)).toExcept s!"missing function {name}"
    let p ← (← jArr f "params").head?.toExcept "missing parameter"
    jField p "type"
  let mutableCell ← param "mutableCell"
  let literalCell ← param "literalCell"
  let readonlyCell ← param "readonlyCell"
  let optionalCell ← param "optionalCell"
  let mut log := []
  log := log ++ [← expect "mutable Boolean contract" (is mutableCell [1,2])]
  log := log ++ [← expect "singleton contract preserved" (is literalCell [1])]
  -- Check exported permissions before applying the invariant gate.
  let ro ← CellClaims.decode readonlyCell
  log := log ++ [← expect "readonly exports empty write type"
    (SourceTypes.encode ro.read == [1,2] && SourceTypes.encode ro.write == [])]
  log := log ++ [← expect "readonly is not a mutable invariant" (rejects readonlyCell)]
  log := log ++ [← expect "optional is not a required cell" (rejects optionalCell)]
  for name in ["otherField","extraField","nestedCell"] do
    let ty ← param name
    log := log ++ [← expect s!"{name} stays unsupported"
      ((ty.getObjValAs? Bool "unsupported").toOption == some true)]
  let btrue ← Json.parse "{\"top\":false,\"atoms\":[{\"a\":\"booleanlit\",\"v\":\"true\"}]}"
  let bsplit ← Json.parse "{\"top\":false,\"atoms\":[{\"a\":\"booleanlit\",\"v\":\"false\"},{\"a\":\"booleanlit\",\"v\":\"true\"}]}"
  log := log ++ [← expect "different setter cannot be discarded"
    (rejects (← fieldMap mutableCell (fun f => put f "write" btrue)))]
  log := log ++ [← expect "equivalent primitive union accepted"
    (is (← fieldMap mutableCell (fun f => put f "read" bsplit)) [1,2])]
  log := log ++ [← expect "wrong field rejected"
    (rejects (← fieldMap mutableCell (fun f => put f "name" (toJson "other"))))]
  log := log ++ [← expect "array contract rejected"
    (rejects (← atomMap mutableCell (fun a => put a "array" (toJson "present"))))]
  log := log ++ [← expect "callable contract rejected"
    (rejects (← atomMap mutableCell (fun a => put a "call" (toJson "present"))))]
  log := log ++ [← expect "no empty field projection"
    (rejects (← atomMap mutableCell (fun a => put a "fields" (toJson ([] : List Json)))))]
  let allocated ← (fs.find? (fun f => (f.getObjValAs? String "name").toOption == some "allocatedCell")).toExcept "missing allocation fixture"
  let envs ← jArr allocated "envs"
  let last ← envs.getLast?.toExcept "missing post-write environment"
  let vars ← jArr last "vars"
  for name in ["cell","alias"] do
    let v ← (vars.find? (fun v => (v.getObjValAs? String "name").toOption == some name)).toExcept "missing alias binding"
    log := log ++ [← expect s!"{name} invariant survives alias-write export" (is (← jField v "type") [1,2])]
  -- Sorted source spans put the outer object literal before its initializer.
  -- Pin this current export gap so it cannot silently become a substituted
  -- annotation while allocation lowering is added.
  let allocation ← (← jArr allocated "exprs").head?.toExcept "missing allocation expression"
  let allocationType ← jField allocation "type"
  log := log ++ [← expect "fresh allocation claim remains explicitly unsupported"
    ((allocationType.getObjValAs? Bool "unsupported").toOption == some true)]
  return log

def main (args : List String) : IO UInt32 := do
  match args with
  | [claimsPath,fileKey] =>
    let text ← IO.FS.readFile claimsPath
    match (do checks (← Json.parse text) fileKey) with
    | .error e => IO.eprintln s!"FAIL: {e}"; return 1
    | .ok results =>
      for line in results do IO.println line
      IO.println s!"Cell contracts: {results.length} passed, 0 failed"
      return 0
  | _ => IO.eprintln "usage: cell_claim_tests <claims.json> <file-key>"; return 2
