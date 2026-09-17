import Verification.ExperimentState.Fragment
import Verification.ExperimentState.CellClaims

/-! Source extraction of first-order generic aliases.

`type Id<T> = T` and `type Box<T> = { value: T }` are the admitted schemes.
Applying an alias is the substitution already proved as `instantiate_param`
and `instantiate_ref`: it is not a second type. Other alias bodies, nullary
aliases, and alias applications in alias bodies remain outside the fragment. -/
namespace Verification.ExperimentState.GenericAlias
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

def decodeAlias (j : Json) : Except String Alias := do
  CellClaims.fieldsExactly j ["name", "typeParams", "body"]
  let name ← jStr (← jField j "name")
  if name.isEmpty then throw "empty alias name"
  if name == "undefined" then throw "shadowing undefined is outside the fragment"
  let [p] ← (← jArr j "typeParams").mapM Fragment.decodeTypeParam
    | throw "only one type parameter is in the fragment"
  if p.name == "undefined" then throw "shadowing undefined is outside the fragment"
  if p.bound.isSome then throw "type parameter bounds on aliases are outside the fragment"
  return ⟨name, p.name, ← jField j "body"⟩

def decodeAliases (ast : Json) : Except String (List Alias) := do
  let aliases ← (← jArr ast "aliases").mapM decodeAlias
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
    return putFields atom [("fields", toJson fields)]
  | "function" =>
    let params ← (← jArr atom "params").mapM (substType p arg)
    return putFields atom
      [("params", toJson params), ("result", ← substType p arg (← jField atom "result"))]
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
    return Json.mkObj [("top", toJson false),
      ("atoms", toJson [putFields atom [("fields", toJson fields)]])]
  | "function" =>
    let params ← (← jArr atom "params").mapM (expandType aliases)
    return Json.mkObj [("top", toJson false),
      ("atoms", toJson [putFields atom
        [("params", toJson params),
         ("result", ← expandType aliases (← jField atom "result"))]])]
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

def expandOpt (aliases : List Alias) : Option Json → Except String (Option Json)
  | none => return none
  | some ty => do
    let t ← expandType aliases ty
    return some t

def expandNamed (aliases : List Alias) (n : String) (t : Json) : Except String (String × Json) := do
  let t ← expandType aliases t
  return (n, t)

partial def expandExpr (aliases : List Alias) (e : Fragment.Expr) : Except String Fragment.Expr := do
  match e with
  | .var p n => return .var p n
  | .lit p v => return .lit p v
  | .logical p a l r =>
    return .logical p a (← expandExpr aliases l) (← expandExpr aliases r)
  | .coalesce p l r =>
    return .coalesce p (← expandExpr aliases l) (← expandExpr aliases r)
  | .nullishAssign p n np r => return .nullishAssign p n np (← expandExpr aliases r)
  | .assign p n np r => return .assign p n np (← expandExpr aliases r)
  | .shapeTest p tag equal e =>
    return .shapeTest p tag equal (← expandExpr aliases e)
  | .equality p eq l r =>
    return .equality p eq (← expandExpr aliases l) (← expandExpr aliases r)
  | .singletonTest p t eq tl l r =>
    return .singletonTest p t eq tl (← expandExpr aliases l) (← expandExpr aliases r)
  | .not p e => return .not p (← expandExpr aliases e)
  | .cast p annot e => return .cast p (← expandOpt aliases annot) (← expandExpr aliases e)
  | .alloc p ns es => return .alloc p ns (← es.mapM (expandExpr aliases))
  | .read p f e => return .read p f (← expandExpr aliases e)
  | .write p f r rhs =>
    return .write p f (← expandExpr aliases r) (← expandExpr aliases rhs)
  | .withValue p fn initial ft bt =>
    return .withValue p (← expandExpr aliases fn) (← expandExpr aliases initial)
      (← expandType aliases ft) (← expandType aliases bt)
  | .lambda p ps result body =>
    let ps ← ps.mapM fun (n, t) => expandNamed aliases n t
    return .lambda p ps (← expandType aliases result) (← expandExpr aliases body)
  | .bindWithReceiver p c r args =>
    return .bindWithReceiver p (← expandExpr aliases c) (← expandExpr aliases r)
      (← args.mapM (expandExpr aliases))
  | .callWithReceiver p c r args =>
    return .callWithReceiver p (← expandExpr aliases c) (← expandExpr aliases r)
      (← args.mapM (expandExpr aliases))
  | .call p c args =>
    return .call p (← expandExpr aliases c) (← args.mapM (expandExpr aliases))
  | .atEnv p e => return .atEnv p (← expandExpr aliases e)
  | .done p => return .done p
  | .seqBody p i b =>
    return .seqBody p (← expandExpr aliases i) (← expandExpr aliases b)
  | .ifBody p result c t e =>
    let result' ← expandOpt aliases result
    return .ifBody p result' (← expandExpr aliases c) (← expandExpr aliases t)
      (← expandExpr aliases e)
  | .letBody p n annot i b =>
    let annot' ← expandOpt aliases annot
    return .letBody p n annot' (← expandExpr aliases i) (← expandExpr aliases b)

private def expandBinding (aliases : List Alias) (b : Fragment.Binding) : Except String Fragment.Binding := do
  return { b with annot := ← expandOpt aliases b.annot, init := ← expandExpr aliases b.init }

partial def expandStmt (aliases : List Alias) (s : Fragment.Stmt) : Except String Fragment.Stmt := do
  match s with
  | .ret p e => return .ret p (← expandExpr aliases e)
  | .constants p bs => return .constants p (← bs.mapM (expandBinding aliases))
  | .mutables p bs => return .mutables p (← bs.mapM (expandBinding aliases))
  | .pattern p props init =>
    let props' ← props.mapM fun q => do
      return { q with default_ := ← q.default_.mapM (expandExpr aliases) }
    return .pattern p props' (← expandExpr aliases init)
  | .ite p c t e =>
    let t' ← t.mapM (expandStmt aliases)
    let e' ← match e with
      | none => pure none
      | some body => (body.mapM (expandStmt aliases)).map some
    return .ite p (← expandExpr aliases c) t' e'
  | .brk p => return .brk p
  | .cont p => return .cont p
  | .loop p c b =>
    return .loop p (← expandExpr aliases c) (← b.mapM (expandStmt aliases))
  | .effect p e => return .effect p (← expandExpr aliases e)

def expandFn (aliases : List Alias) (f : Fragment.Fn) : Except String Fragment.Fn := do
  let params ← f.params.mapM fun p => do
    let ty ← expandType aliases p.ty
    return { p with ty }
  let ret ← expandType aliases f.ret
  let body ← f.body.mapM (expandStmt aliases)
  return { f with params, ret, body }

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

end Verification.ExperimentState.GenericAlias
