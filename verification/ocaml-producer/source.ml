open Json
open Semantic
let unsupported s = fail ("unsupported: " ^ s)
let text k j = str (field k j)
let items k j = list (field k j)
type type_context = { bindings: (string * ty) list; aliases: (string * Json.t) list;
                      imported: (string * (string * int)) list; expanding: string list }
let identity declaration =
  let span = list (field "span" declaration) in
  match span with
  | [Number first;Number last] ->
    str (field "module" declaration) ^ "#" ^ first ^ ":" ^ last
  | _ -> fail "invalid imported declaration identity"
let rec annotation binders j =
  if boolean (field "top" j) then Atoms [Top]
  else List.fold_left union (Atoms []) (List.map (annotation_atom binders) (items "atoms" j))
and annotation_atom binders j =
  (* An intersection of arrows is one value with several call signatures: the
     shape's calls list, not a second kind of type. Other intersections have no
     representation here. *)
  let conjuncts = match List.assoc_opt "and" (obj j) with
    | None | Some (Array []) -> []
    | Some (Array others) -> others
    | Some _ -> unsupported "intersection annotation" in
  if conjuncts <> [] && text "a" j <> "function" then
    unsupported "intersection annotation";
  match text "a" j with
  | "null" -> Atoms [Nul] | "undefined" -> Atoms [Undef]
  | "boolean" -> bool | "number" -> Atoms [Num] | "string" -> Atoms [Str]
  | "void" -> Atoms [Top]
  | "numberlit" -> number_literal (text "v" j)
  | "stringlit" -> Atoms [StrLit (text "v" j)]
  | "booleanlit" -> Atoms [if text "v" j = "true" then True else False]
  | "param" -> (match List.assoc_opt (text "name" j) binders.bindings with
    | Some t -> t | None -> fail "unbound rigid parameter")
  | "record" ->
    let fs = List.map (fun f ->
      let r = annotation binders (field "read" f) and w = annotation binders (field "write" f) in
      { name=text "name" f; optional=boolean (field "optional" f); read=r;
        write=(if w=Atoms [] then None else Some w) }) (items "fields" j) in
    List.iter (fun k -> if text k j <> "absent" && text k j <> "unknown" then unsupported ("record " ^ k)) ["call";"construct";"array"];
    List.iter (fun (_,v) -> if str v <> "absent" && str v <> "unknown" then unsupported "index signature") (obj (field "indexes" j));
    let string_index = match List.assoc_opt "indexSignature" (obj j) with
      | None -> None
      | Some signature ->
        let value = annotation binders (field "read" signature) in
        let writable = annotation binders (field "write" signature) in
        Some {value;writable=(if writable=Atoms [] then None else Some writable)} in
    Atoms [Shape {fields=fs;string_index;calls=[];elements=None}]
  | "alias" ->
    let name = text "name" j in
    let args = List.map (annotation binders) (items "args" j) in
    (match List.assoc_opt name binders.imported with
    | Some (id,arity) ->
      if List.length args <> arity then fail ("imported alias arity: " ^ name);
      Atoms [Named (id,args)]
    | None ->
      if List.mem name binders.expanding then unsupported ("recursive alias " ^ name);
      let a = match List.assoc_opt name binders.aliases with Some a -> a | None -> fail ("unknown alias " ^ name) in
      let ps = items "typeParams" a in
      if List.length ps <> List.length args then fail ("alias arity: " ^ name);
      let bindings = List.map2 (fun p arg -> text "name" p,arg) ps args in
      annotation {binders with bindings; expanding=name::binders.expanding} (field "body" a))
  | "array" -> array {
      required=List.map (annotation binders) (items "required" j);
      optional_elements=List.map (annotation binders) (items "optional" j);
      rest=(match field "rest" j with Null -> None | t -> Some (annotation binders t));
      readonly=boolean (field "readonly" j) }
  | "function" ->
    let signature a = { quantified=[];
      receiver=annotation binders (field "this" a);
      params=List.map (annotation binders) (items "params" a);
      variadic=Option.map (annotation binders) (List.assoc_opt "rest" (obj a));
      result=annotation binders (field "result" a) } in
    List.iter (fun a -> if text "a" a <> "function" then
      unsupported "intersection annotation") conjuncts;
    Atoms [Shape {fields=[];string_index=None;calls=List.map signature (j::conjuncts);elements=None}]
  | k -> unsupported ("annotation " ^ k)
type literal = LNull | LUndefined | LBool of bool | LNumber of string | LString of string
let literal j = match text "a" j with
  | "null" -> LNull | "undefined" -> LUndefined
  | "booleanlit" -> LBool (text "v" j = "true")
  | "numberlit" -> LNumber (text "v" j) | "stringlit" -> LString (text "v" j)
  | k -> unsupported ("literal " ^ k)
let optional_type binders = function Null -> None | j -> Some (annotation binders j)
let span_start j = match list j with
  | Number n :: _ -> int_of_string n
  | _ -> Json.fail "empty source span"

(* Decode binders in declaration order. A bound sees outer and preceding
   binders, while the signature and body see the complete local frame. An
   inner spelling shadows an outer one without identifying their rigid IDs. *)
let quantify binders scope parameters =
  let rec loop index binders accumulated = function
    | [] -> binders,List.rev accumulated
    | p::rest ->
      let spelling=text "name" p in
      if List.exists (fun (q:quantifier) -> q.identity.spelling=spelling) accumulated
      then Json.fail "duplicate type parameter";
      let identity={scope;index;spelling} in
      let quantified={identity;bound=optional_type binders (field "bound" p)} in
      let binders={binders with bindings=(spelling,Rigid identity)::binders.bindings} in
      loop (index+1) binders (quantified::accumulated) rest in
  loop 0 binders [] parameters
type arithmetic = Add | Sub | Mul | Div
type equality = StrictEqual | StrictUnequal | LooseEqual | LooseUnequal

(* This is a typed view of the shared Fragment, not a new source language.
   Unknown cases fail here; inference exhaustively matches implemented cases. *)
type expr = { pos: Json.t; node: expr_node }
and expr_node =
  | Id of string | Literal of literal | Not of expr | Arith of arithmetic * expr * expr
  | Equality of equality * expr * expr | Alloc of (string * expr) list
  | Read of expr * string | Write of expr * string * expr
  | Assign of string * expr
  (* A parameter's type is what the body reads. A defaulted one also admits
     `undefined` where the closure is called; the default replaces it. A rest
     parameter reads the tuple its arguments are collected into, and the
     signature has one position per required element of that tuple. The
     receiver is the `this` annotation of an ordinary function, none for an
     arrow, whose `this` is the enclosing one. *)
  | Lambda of ty option * quantifier list * (string * ty) list * (int * expr) list * bool * ty * expr
  (* The positions of the arguments written with `...`: each stands for the
     elements of its operand, read where it is written. *)
  | Call of expr * expr option * expr list * int list
  (* A call through a property reference: the callee is the read of the
     method, and the object it is read from is the receiver. *)
  | Invoke of expr * expr list * int list
  (* `f.apply(r, list)`: the list's elements, read by index, are the actuals. *)
  | Apply of expr * expr * expr option
  | Conditional of expr * expr * expr | Coalesce of expr * expr
  | ArrayLiteral of expr list | Index of expr * expr | IndexWrite of expr * expr * expr
  | Bind of expr * expr * expr list
  | WithFields of expr * expr * ty * ty
  | Cast of string * ty option * expr
  | DoneBody | ReturnBody of expr | SequenceBody of expr * expr
  | LetBody of string * ty option * expr * expr
  | IfBody of ty * expr * expr * expr
and stmt = { span: Json.t; statement: stmt_node }
and stmt_node =
  | Declare of bool * (string * ty option * expr) list
  | Return of expr | Effect of expr | If of expr * stmt list * stmt list
  | While of expr * stmt list | Break | Continue
and fn = { quantified: quantifier list; name: string; name_pos: Json.t; params: (string * ty) list;
           result: ty; body: stmt list }
type imported_definition = { id: string; parameters: string list; expression: ty }
type program = { file: Json.t; digest: Json.t; imports: imported_definition list; functions: fn list }

(* Candidate-only view of a source equation. Lean independently derives the
   authoritative graph row from the same import document. Named edges remain
   named here, including cycles; no recursive declaration is unfolded. *)
let rec imported_type j =
  match text "k" j with
  | "atom" -> (match text "name" j with
    | "null" -> Atoms [Nul] | "undefined" -> Atoms [Undef]
    | "boolean" -> bool | "number" -> Atoms [Num]
    | "string" -> Atoms [Str] | "unknown" | "void" -> top
    | "never" -> Atoms [] | name -> unsupported ("imported atom " ^ name))
  | "literal" -> (match text "name" j with
    | "true" -> Atoms [True] | "false" -> Atoms [False]
    | "number" -> number_literal (text "text" j)
    | "string" -> Atoms [StrLit (text "text" j)]
    | name -> unsupported ("imported literal " ^ name))
  | "union" -> List.fold_left union (Atoms []) (List.map imported_type (items "parts" j))
  | "array" -> array {required=[];optional_elements=[];
      rest=Some (imported_type (field "element" j));readonly=boolean (field "readonly" j)}
  | "object" ->
    let fields = List.map (fun f ->
      let t = imported_type (field "type" f) in
      {name=text "name" f;optional=boolean (field "optional" f);
       read=t;write=(if boolean (field "readonly" f) then None else Some t)})
      (items "fields" j) in
    let string_index = match field "stringIndex" j with
      | Null -> None
      | index -> let t = imported_type (field "value" index) in
        Some {value=t;writable=(if boolean (field "readonly" index) then None else Some t)} in
    Atoms [Shape {fields;string_index;calls=[];elements=None}]
  | "reference" ->
    let args = List.map imported_type (items "args" j) in
    Atoms [Named (identity (field "target" (field "reference" j)), args)]
  | "parameter" -> unsupported "imported generic body needs parameter substitution"
  | "intersection" -> unsupported "imported intersection needs source graph conjunction"
  | k -> unsupported ("imported type expression " ^ k)
let rec expr binders j =
  let sub k = expr binders (field k j) in
  let node = match text "k" j with
  | "id" -> Id (text "name" j) | "lit" -> Literal (literal (field "lit" j))
  | "this" -> Id "this"
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
  | "lambda" ->
      let inner,quantified = quantify binders (-1 - span_start (field "pos" j))
        (items "typeParams" j) in
      let parameters = items "params" j in
      let rest = List.exists (fun p -> List.mem_assoc "rest" (obj p)) parameters in
      let receiver = match field "receiver" j with
        | Null -> None
        | r ->
          (* The receiver rule is the strict one; sloppy code substitutes the
             global object, which nothing here models. *)
          if not (boolean (field "strict" r)) then unsupported "an ordinary function in sloppy code";
          Some (annotation inner (field "type" r)) in
      Lambda (receiver,quantified,
        List.map (fun p -> text "name" p,annotation inner (field "type" p)) parameters,
        List.filter_map (fun (i,p) -> match List.assoc_opt "default" (obj p) with
          | None -> None
          | Some d -> Some (i, expr inner d))
          (List.mapi (fun i p -> i,p) parameters),
        rest,
        annotation inner (field "result" j),
        expr inner (field "body" j))
  | "apply" ->
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    Call (sub "callee",None,List.map (expr binders) (items "args" j),spreads)
  | "invoke" ->
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    Invoke (sub "callee",List.map (expr binders) (items "args" j),spreads)
  | "applyWithReceiver" ->
    Apply (sub "callee",sub "receiver",(match field "list" j with Null -> None | l -> Some (expr binders l)))
  | "callWithReceiver" ->
    Call (sub "callee",Some (sub "receiver"),List.map (expr binders) (items "args" j),[])
  | "coalesce" -> Coalesce (sub "left",sub "right")
  | "arrayLit" -> ArrayLiteral (List.map (expr binders) (items "elems" j))
  | "index" -> Index (sub "e",sub "key")
  | "indexWrite" -> IndexWrite (sub "receiver",sub "key",sub "rhs")
  | "withValue" -> WithFields (sub "fn",sub "initial",annotation binders (field "functionType" j),annotation binders (field "bagType" j))
  | "bindWithReceiver" -> Bind (sub "callee",sub "receiver",List.map (expr binders) (items "args" j))
  | "cast" -> Cast (text "cast" j,(match field "annot" j with Null -> None | a -> Some (annotation binders a)),sub "e")
  | "doneBody" -> DoneBody | "returnBody" -> ReturnBody (sub "e")
  | "seqBody" -> SequenceBody (sub "init",sub "body")
  | "letBody" -> LetBody (text "name" j,(match field "annot" j with Null -> None | a -> Some (annotation binders a)),sub "init",sub "body")
  | "ifBody" -> IfBody (annotation binders (field "result" j),sub "cond",sub "then",sub "else_")
  | "conditional" -> Conditional (sub "cond",sub "then",sub "else_")
  | k -> unsupported ("expression " ^ k) in {pos=field "pos" j;node}
let rec stmt binders j =
  let statement = match text "k" j with
  | "const" | "let" -> Declare (text "k" j="let",List.map (fun b ->
      text "name" b,optional_type binders (field "annot" b),expr binders (field "init" b)) (items "bindings" j))
  | "return" -> Return (expr binders (field "e" j)) | "effect" -> Effect (expr binders (field "e" j))
  | "while" -> While (expr binders (field "cond" j),List.map (stmt binders) (items "body" j))
  | "break" -> Break | "continue" -> Continue
  | "if" -> If (expr binders (field "cond" j),List.map (stmt binders) (items "then" j),
      match field "else_" j with Null -> [] | xs -> List.map (stmt binders) (list xs))
  | k -> unsupported ("statement " ^ k) in {span=field "pos" j;statement}
let decode ast =
  let imports = field "imports" ast in
  let definitions = List.map (fun definition ->
    let declaration = field "declaration" definition in
    {id=identity declaration;
     parameters=List.map (fun p -> text "name" p) (items "parameters" definition);
     expression=imported_type (field "expression" definition)})
    (items "definitions" imports) in
  let imported = List.map (fun root ->
    let id=identity (field "declaration" root) in
    let definition = match List.find_opt (fun d -> d.id=id) definitions with
      | Some d -> d | None -> fail ("import root lacks definition " ^ id) in
    text "local" (field "binding" root), (id,List.length definition.parameters))
    (items "roots" imports) in
  if List.length (List.sort_uniq compare (List.map fst imported)) <> List.length imported then
    fail "duplicate imported local type";
  let aliases = List.map (fun a -> text "name" a,a) (items "aliases" ast) in
  { file=field "file" ast;digest=field "sourceSha256" ast;
    imports=definitions;
    functions=List.mapi (fun scope f ->
      let parameters = items "typeParams" f in
      let initial={bindings=[];aliases;imported;expanding=[]} in
      let binders,quantified = quantify initial scope parameters in
      {quantified;name=text "name" f; name_pos=field "namePos" f;
      params=List.map (fun p -> text "name" p,annotation binders (field "type" p)) (items "params" f);
      result=annotation binders (field "retType" f);body=List.map (stmt binders) (items "body" f)}) (items "functions" ast) }
