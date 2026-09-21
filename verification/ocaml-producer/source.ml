open Json
open Semantic
let unsupported s = fail ("unsupported: " ^ s)
let text k j = str (field k j)
let items k j = list (field k j)
let rec annotation binders j =
  if boolean (field "top" j) then Atoms [Top]
  else List.fold_left union (Atoms []) (List.map (annotation_atom binders) (items "atoms" j))
and annotation_atom binders j =
  (match List.assoc_opt "and" (obj j) with
    | None | Some (Array []) -> ()
    | Some _ -> unsupported "intersection annotation");
  match text "a" j with
  | "null" -> Atoms [Nul] | "undefined" -> Atoms [Undef]
  | "boolean" -> bool | "number" -> Atoms [Num] | "string" -> Atoms [Str]
  | "booleanlit" -> Atoms [if text "v" j = "true" then True else False]
  | "param" -> (match List.assoc_opt (text "name" j) binders with
    | Some id -> Rigid id | None -> fail "unbound rigid parameter")
  | "record" ->
    let fs = List.map (fun f ->
      if boolean (field "optional" f) then unsupported "optional fields";
      let r = annotation binders (field "read" f) and w = annotation binders (field "write" f) in
      if r <> w then unsupported "readonly fields";
      { name=text "name" f; optional=false; read=r; write=Some w }) (items "fields" j) in
    List.iter (fun k -> if text k j <> "absent" && text k j <> "unknown" then unsupported ("record " ^ k)) ["call";"construct";"array"];
    List.iter (fun (_,v) -> if str v <> "absent" && str v <> "unknown" then unsupported "index signature") (obj (field "indexes" j));
    record fs
  | "function" -> arrow (List.map (annotation binders) (items "params" j)) (annotation binders (field "result" j))
  | k -> unsupported ("annotation " ^ k)
type literal = LNull | LUndefined | LBool of bool | LNumber of string | LString of string
let literal j = match text "a" j with
  | "null" -> LNull | "undefined" -> LUndefined
  | "booleanlit" -> LBool (text "v" j = "true")
  | "numberlit" -> LNumber (text "v" j) | "stringlit" -> LString (text "v" j)
  | k -> unsupported ("literal " ^ k)
type arithmetic = Add | Sub | Mul | Div
type equality = StrictEqual | StrictUnequal | LooseEqual | LooseUnequal

(* This is a typed view of the shared Fragment, not a new source language.
   Unknown cases fail here; inference exhaustively matches implemented cases. *)
type expr = { pos: Json.t; node: expr_node }
and expr_node =
  | Id of string | Literal of literal | Not of expr | Arith of arithmetic * expr * expr
  | Equality of equality * expr * expr | Alloc of (string * expr) list
  | Read of expr * string | Write of expr * string * expr
  | Assign of string * expr | Lambda of (string * ty) list * ty * expr
  | Call of expr * expr option * expr list
  | Conditional of expr * expr * expr
and stmt = { span: Json.t; statement: stmt_node }
and stmt_node =
  | Declare of bool * (string * ty option * expr) list
  | Return of expr | Effect of expr | If of expr * stmt list * stmt list
and quantified = { identity: rigid; bound: ty option }
and fn = { quantified: quantified list; name: string; name_pos: Json.t; params: (string * ty) list;
           result: ty; body: stmt list }
type program = { file: Json.t; digest: Json.t; functions: fn list }
let rec expr binders j =
  let sub k = expr binders (field k j) in
  let node = match text "k" j with
  | "id" -> Id (text "name" j) | "lit" -> Literal (literal (field "lit" j))
  | "not" -> Not (sub "e")
  | "arith" -> let op = match text "op" j with
      | "add" -> Add | "sub" -> Sub | "mul" -> Mul | "div" -> Div
      | k -> unsupported ("arithmetic " ^ k) in Arith (op,sub "l",sub "r")
  | "bin" -> let op = match text "op" j with
      | "===" -> StrictEqual | "!==" -> StrictUnequal
      | "==" -> LooseEqual | "!=" -> LooseUnequal
      | k -> unsupported ("operator " ^ k) in Equality (op,sub "l",sub "r")
  | "alloc" -> Alloc (List.map (fun f -> text "name" f,expr binders (field "e" f)) (items "fields" j))
  | "read" -> Read (sub "e",text "field" j)
  | "write" -> Write (sub "receiver",text "field" j,sub "rhs")
  | "assign" -> Assign (text "name" j,sub "rhs")
  | "lambda" -> Lambda (List.map (fun p -> text "name" p,annotation binders (field "type" p))
      (items "params" j),annotation binders (field "result" j),sub "body")
  | "apply" -> Call (sub "callee",None,List.map (expr binders) (items "args" j))
  | "callWithReceiver" -> Call (sub "callee",Some (sub "receiver"),List.map (expr binders) (items "args" j))
  | "conditional" -> Conditional (sub "cond",sub "then",sub "else_")
  | k -> unsupported ("expression " ^ k) in {pos=field "pos" j;node}
let optional_type binders = function Null -> None | j -> Some (annotation binders j)
let rec stmt binders j =
  let statement = match text "k" j with
  | "const" | "let" -> Declare (text "k" j="let",List.map (fun b ->
      text "name" b,optional_type binders (field "annot" b),expr binders (field "init" b)) (items "bindings" j))
  | "return" -> Return (expr binders (field "e" j)) | "effect" -> Effect (expr binders (field "e" j))
  | "if" -> If (expr binders (field "cond" j),List.map (stmt binders) (items "then" j),
      match field "else_" j with Null -> [] | xs -> List.map (stmt binders) (list xs))
  | k -> unsupported ("statement " ^ k) in {span=field "pos" j;statement}
let decode ast =
  if items "aliases" ast <> [] then unsupported "type aliases";
  { file=field "file" ast;digest=field "sourceSha256" ast;
    functions=List.mapi (fun scope f ->
      let parameters = items "typeParams" f in
      let binders = List.mapi (fun index p -> let spelling=text "name" p in
        spelling,{scope;index;spelling}) parameters in
      let quantified = List.map2 (fun (_,identity) p ->
        {identity;bound=optional_type binders (field "bound" p)}) binders parameters in
      {quantified;name=text "name" f; name_pos=field "namePos" f;
      params=List.map (fun p -> text "name" p,annotation binders (field "type" p)) (items "params" f);
      result=annotation binders (field "retType" f);body=List.map (stmt binders) (items "body" f)}) (items "functions" ast) }
