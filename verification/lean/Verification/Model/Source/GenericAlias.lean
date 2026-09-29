import Verification.Model.Source.Fragment
import Verification.Model.Programs.CellClaims

/-! Alias applications in SKJS's exported claims.

SKJS writes a single-argument named instantiation as an alias atom. The
converter expands `type Id<T> = T` and `type Box<T> = { value: T }` here, at the
claim level. Source annotations do not use this module: `EquationLowering` interprets
every declaration application from its source equation. -/
namespace Verification.Model.GenericAlias
open Lean

structure Alias where
  name : String
  param : String
  body : Json

def paramType (name : String) : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "param"), ("name", toJson name)]])]

def isParamType (j : Json) (name : String) : Bool := j == paramType name

def fieldIsParam (field : Json) (name : String) : Bool :=
  (field.getObjVal? "name").toOption == some (.str "value") &&
    (field.getObjVal? "optional").toOption == some (.bool false) &&
    (match (field.getObjVal? "read").toOption, (field.getObjVal? "write").toOption with
    | some read, some write => isParamType read name && isParamType write name
    | _, _ => false)

def isBoxAtom (atom : Json) (name : String) : Bool :=
  (atom.getObjVal? "a").toOption == some (.str "record") &&
    (match (atom.getObjVal? "fields").toOption with
    | some (.arr fields) => fields.size == 1 && fieldIsParam fields[0]! name
    | _ => false)

def isIdentity (a : Alias) : Bool := isParamType a.body a.param

def isBox (a : Alias) : Bool :=
  (a.body.getObjVal? "top").toOption == some (.bool false) &&
    (match (a.body.getObjVal? "atoms").toOption with
    | some (.arr atoms) => atoms.size == 1 && isBoxAtom atoms[0]! a.param
    | _ => false)

def admit (a : Alias) : Except String Unit :=
  if isIdentity a || isBox a then return ()
  else throw "only identity (`type Id<T> = T`) and cell (`type Box<T> = { value: T }`) aliases are in the fragment"

private def sourceAlias (root : Json) (definitions : List Json) : Except String (Option Alias) := do
  let identity ← jField root "declaration"
  let some definition := definitions.find? (fun d =>
    (d.getObjVal? "declaration").toOption == some identity)
    | throw "declaration root has no source equation"
  let [parameter] := (← jArr definition "parameters")
    | return none
  if (← jField parameter "bound") != Json.null || (← jField parameter "default") != Json.null ||
      !(← jArr definition "bases").isEmpty then return none
  let name ← jStr (← jField (← jField root "binding") "local")
  let param ← jStr (← jField parameter "name")
  let body ← jField definition "expression"
  let paramAtZero (j : Json) : Bool :=
    (j.getObjVal? "k").toOption == some (Json.str "parameter") &&
    (j.getObjVal? "index").toOption == some (toJson (0 : Nat))
  if paramAtZero body then return some ⟨name, param, paramType param⟩
  if (body.getObjVal? "k").toOption != some (Json.str "object") then return none
  if (body.getObjVal? "stringIndex").toOption != some Json.null then return none
  if (body.getObjVal? "numberIndex").toOption.isSome || (body.getObjVal? "symbolIndex").toOption.isSome then
    return none
  if !(← jArr body "calls").isEmpty then return none
  let [field] := (← jArr body "fields") | return none
  if (field.getObjVal? "name").toOption != some (Json.str "value") ||
      (field.getObjVal? "optional").toOption != some (Json.bool false) ||
      (field.getObjVal? "readonly").toOption != some (Json.bool false) ||
      !paramAtZero (← jField field "type") then return none
  let record := Json.mkObj [("a", toJson "record"),
    ("fields", toJson [Json.mkObj [("name", toJson "value"),
      ("optional", toJson false), ("read", paramType param),
      ("write", paramType param)]]),
    ("indexes", Json.mkObj [("string", toJson "absent"),
      ("number", toJson "absent"), ("symbol", toJson "absent")]),
    ("call", toJson "unknown"), ("construct", toJson "unknown"),
    ("array", toJson "unknown")]
  return some ⟨name, param, Json.mkObj [("top", toJson false),
    ("atoms", toJson [record])]⟩

def decodeAliases (ast : Json) : Except String (List Alias) := do
  let document ← jField ast "declarations"
  let definitions ← jArr document "definitions"
  let source ← (← jArr document "roots").mapM (sourceAlias · definitions)
  let aliases := source.filterMap id
  let names := aliases.map (·.name)
  if names.eraseDups.length != names.length then throw "duplicate type alias"
  return aliases

def putFields (j : Json) (updates : List (String × Json)) : Json :=
  match j with
  | .obj kvs =>
    Json.mkObj (updates.foldl (fun acc (k, v) =>
      (k, v) :: acc.filter (fun p => p.1 != k)) (kvs.toList.map fun ⟨k, v⟩ => (k, v)))
  | _ => j

mutual
partial def substAtom (p : String) (arg : Json) (atom : Json) : Except String Json := do
  let tag ← jStr (← jField atom "a")
  match tag with
  | "param" =>
    if (← jStr (← jField atom "name")) == p then
      throw "a type parameter cannot mix with other atoms under substitution"
    else return atom
  | "record" =>
    let fields ← (← jArr atom "fields").mapM fun field => do
      return putFields field
        [("read", ← substType p arg (← jField field "read")),
         ("write", ← substType p arg (← jField field "write"))]
    let index ← match (atom.getObjVal? "indexSignature").toOption with
      | none => pure []
      | some signature => pure [("indexSignature", putFields signature
          [("read", ← substType p arg (← jField signature "read")),
           ("write", ← substType p arg (← jField signature "write"))])]
    return putFields atom ([("fields", toJson fields)] ++ index)
  | "array" | "store" =>
    let required ← (← jArr atom "required").mapM (substType p arg)
    let optional ← (← jArr atom "optional").mapM (substType p arg)
    let rest ← jField atom "rest"
    let rest ← if rest == .null then pure rest else substType p arg rest
    return putFields atom [("required",toJson required),("optional",toJson optional),("rest",rest)]
  | "function" =>
    let params ← (← jArr atom "params").mapM (substType p arg)
    let rest ← match (atom.getObjVal? "rest").toOption with
      | some r => pure [("rest", ← substType p arg r)]
      | none => pure []
    return putFields atom
      ([("this", ← substType p arg (← jField atom "this")), ("params", toJson params),
        ("result", ← substType p arg (← jField atom "result"))] ++ rest)
  | "callable" =>
    return Json.mkObj [("a", toJson "callable"),
      ("function", ← substAtom p arg (← jField atom "function")),
      ("bag", ← substAtom p arg (← jField atom "bag"))]
  | "alias" => throw "alias applications in alias bodies are outside the fragment"
  | _ => return atom

partial def substType (p : String) (arg : Json) (ty : Json) : Except String Json := do
  if (ty.getObjVal? "unsupported").toOption.isSome then return ty
  if isParamType ty p then return arg
  CellClaims.fieldsExactly ty ["top", "atoms"]
  if ← (← jField ty "top").getBool? then return ty
  let atoms ← (← jArr ty "atoms").mapM (substAtom p arg)
  return Json.mkObj [("top", toJson false), ("atoms", toJson atoms)]
end

def applyAlias (a : Alias) (arg : Json) : Except String Json := do
  admit a
  if isIdentity a then return arg
  substType a.param arg a.body

def isTop (ty : Json) : Bool :=
  (ty.getObjVal? "top").toOption == some (.bool true)

def atomsOf (ty : Json) : List Json :=
  match (ty.getObjVal? "atoms").toOption with
  | some (.arr a) => a.toList
  | _ => []

mutual
partial def expandAtom (aliases : List Alias) (atom : Json) : Except String Json := do
  let tag ← jStr (← jField atom "a")
  match tag with
  | "alias" =>
    CellClaims.fieldsExactly atom ["a", "name", "args"]
    let name ← jStr (← jField atom "name")
    let some a := aliases.find? (fun a => a.name == name)
      | throw s!"unknown type alias '{name}'"
    let [arg] ← jArr atom "args" | throw "only one type argument is in the fragment"
    applyAlias a (← expandType aliases arg)
  | "record" =>
    let fields ← (← jArr atom "fields").mapM fun field => do
      return putFields field
        [("read", ← expandType aliases (← jField field "read")),
         ("write", ← expandType aliases (← jField field "write"))]
    let index ← match (atom.getObjVal? "indexSignature").toOption with
      | none => pure []
      | some signature => pure [("indexSignature", putFields signature
          [("read", ← expandType aliases (← jField signature "read")),
           ("write", ← expandType aliases (← jField signature "write"))])]
    return Json.mkObj [("top", toJson false),
      ("atoms", toJson [putFields atom ([("fields", toJson fields)] ++ index)])]
  | "array" | "store" =>
    let required ← (← jArr atom "required").mapM (expandType aliases)
    let optional ← (← jArr atom "optional").mapM (expandType aliases)
    let rest ← jField atom "rest"
    let rest ← if rest == .null then pure rest else expandType aliases rest
    return Json.mkObj [("top",toJson false),("atoms",toJson [putFields atom [("required",toJson required),("optional",toJson optional),("rest",rest)]])]
  | "function" =>
    let params ← (← jArr atom "params").mapM (expandType aliases)
    let rest ← match (atom.getObjVal? "rest").toOption with
      | some r => pure [("rest", ← expandType aliases r)]
      | none => pure []
    return Json.mkObj [("top", toJson false),
      ("atoms", toJson [putFields atom
        ([("this", ← expandType aliases (← jField atom "this")), ("params", toJson params),
         ("result", ← expandType aliases (← jField atom "result"))] ++ rest)])]
  | "callable" =>
    let fnTy ← expandAtom aliases (← jField atom "function")
    let bagTy ← expandAtom aliases (← jField atom "bag")
    let [fn] := atomsOf fnTy | throw "callable function contract must remain a function"
    let [bag] := atomsOf bagTy | throw "callable bag contract must remain a record"
    return Json.mkObj [("top", toJson false),
      ("atoms", toJson [Json.mkObj [("a", toJson "callable"), ("function", fn), ("bag", bag)]])]
  | _ =>
    return Json.mkObj [("top", toJson false), ("atoms", toJson [atom])]

partial def expandType (aliases : List Alias) (ty : Json) : Except String Json := do
  if (ty.getObjVal? "unsupported").toOption.isSome then return ty
  CellClaims.fieldsExactly ty ["top", "atoms"]
  if ← (← jField ty "top").getBool? then return ty
  let parts ← (← jArr ty "atoms").mapM (expandAtom aliases)
  if parts.any isTop then
    return Json.mkObj [("top", toJson true), ("atoms", toJson ([] : List Json))]
  return Json.mkObj [("top", toJson false), ("atoms", toJson (parts.flatMap atomsOf))]
end

def expandNamed (aliases : List Alias) (n : String) (t : Json) : Except String (String × Json) := do
  let t ← expandType aliases t
  return (n, t)

def expandClaims (aliases : List Alias) (c : Fragment.Claims) :
    Except String Fragment.Claims := do
  let params ← c.params.mapM fun (n, t) => expandNamed aliases n t
  let envs ← c.envs.mapM fun (pos, vars) => do
    let vars ← vars.mapM fun (n, t) => expandNamed aliases n t
    return (pos, vars)
  let exprs ← c.exprs.mapM fun (pos, t) => do
    let t ← expandType aliases t
    return (pos, t)
  let ret ← expandType aliases c.ret
  return { c with params, ret, envs, exprs }

private def boolTy : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "boolean")]])]

private def idAlias : Alias := ⟨"Id", "T", paramType "T"⟩

private def boxBody : Json :=
  Json.mkObj [("top", toJson false), ("atoms", toJson [Json.mkObj [
    ("a", toJson "record"),
    ("fields", toJson [Json.mkObj [
      ("name", toJson "value"), ("optional", toJson false),
      ("read", paramType "T"), ("write", paramType "T")]]),
    ("indexes", Json.mkObj [("string", toJson "absent"), ("number", toJson "absent"),
      ("symbol", toJson "absent")]),
    ("call", toJson "unknown"), ("construct", toJson "unknown"), ("array", toJson "unknown")]])]

private def boxAlias : Alias := ⟨"Box", "T", boxBody⟩

private def aliasApp (name : String) (arg : Json) : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "alias"), ("name", toJson name),
      ("args", toJson [arg])]])]

#guard isIdentity idAlias
#guard isBox boxAlias
#guard (match applyAlias idAlias boolTy with | .ok t => t == boolTy | _ => false)
#guard (match expandType [idAlias] (aliasApp "Id" boolTy) with
  | .ok t => t == boolTy | _ => false)
#guard (match expandType [idAlias] (aliasApp "Id" (paramType "T")) with
  | .ok t => isParamType t "T" | _ => false)
#guard (match expandType [boxAlias] (aliasApp "Box" boolTy) with
  | .ok t =>
    match t.getObjVal? "atoms" with
    | .ok (.arr a) => a.size == 1 &&
      (a[0]!.getObjVal? "a").toOption == some (.str "record")
    | _ => false
  | _ => false)
#guard (match admit ⟨"Bad", "T", boolTy⟩ with
  | .error e => "only identity".isPrefixOf e | _ => false)

end Verification.Model.GenericAlias
