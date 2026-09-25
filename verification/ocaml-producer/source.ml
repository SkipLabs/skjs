open Json
open Semantic
let unsupported s = fail ("unsupported: " ^ s)
let text k j = str (field k j)
let items k j = list (field k j)
(* Where a source type's names resolve. A function annotation reads its
   enclosing binders by spelling; a declaration body reads its own parameters
   by position and its method receiver as the declaration. A reference names
   its declaration by identity. *)
type type_context = { bindings: (string * type_argument) list;
                      owner: string option; positional: rigid list;
                      arity: (string * (int * int)) list;
                      symbolic: (string * (rigid * ty)) list }
let identity declaration =
  let span = list (field "span" declaration) in
  match span with
  | [Number first;Number last] ->
    str (field "module" declaration) ^ "#" ^ first ^ ":" ^ last
  | _ -> fail "invalid declaration identity"
(* The source type terms function annotations and declaration bodies share.
   This is a candidate-only view: Lean independently derives the authoritative
   graph rows from the same terms. Named edges remain named here, including
   cycles; no recursive declaration is unfolded. *)
(* A field name: a string key, or `{"symbol": i}` for the declaration
   document's i-th symbol. *)
let property_key = function
  | String name -> Name name
  | Object ["symbol",Number i] -> Key (int_of_string i)
  | _ -> fail "expected a property key"
(* A rest term typed by a pack parameter, `{"k": "pack", "of": binder}`. *)
let is_pack = function
  | Object fields -> List.assoc_opt "k" fields = Some (String "pack")
  | _ -> false

(* Free uses by role, not occurrences in serialized JSON. Nested schemes
   shadow their own names, including in their bounds and signatures. *)
let rec binder_use name = function
  | Object fields as term ->
    let get key = List.assoc_opt key fields in
    if get "k" = Some (String "binder") then get "name" = Some (String name),false
    else if is_pack term then
      (match get "of" with
      | Some (Object operand) when List.assoc_opt "k" operand = Some (String "binder") ->
        false,List.assoc_opt "name" operand = Some (String name)
      | Some operand -> binder_use name operand
      | None -> false,false)
    else if get "k" = Some (String "scheme") &&
      (match get "binders" with
      | Some (Array binders) -> List.exists (function
          | Object binder -> List.assoc_opt "name" binder = Some (String name)
          | Null | Bool _ | Number _ | String _ | Array _ -> false) binders
      | Some (Null | Bool _ | Number _ | String _ | Object _) | None -> false)
    then false,false
    else binder_uses name (List.map snd fields)
  | Array terms -> binder_uses name terms
  | Null | Bool _ | Number _ | String _ -> false,false
and binder_uses name terms = List.fold_left (fun (values,packs) term ->
  let value,pack=binder_use name term in values || value,packs || pack) (false,false) terms

let rec source_type ctx j =
  let recur = source_type ctx in
  match text "k" j with
  | "atom" -> (match text "name" j with
    | "null" -> Atoms [Nul] | "undefined" -> Atoms [Undef]
    | "boolean" -> bool | "number" -> Atoms [Num]
    | "string" -> Atoms [Str] | "bigint" -> Atoms [Bigint] | "symbol" -> Atoms [Symbol]
    | "unknown" | "void" -> top
    | "never" -> Atoms [] | name -> unsupported ("atom " ^ name))
  | "literal" -> (match text "name" j with
    | "true" -> Atoms [True] | "false" -> Atoms [False]
    | "number" -> number_literal_type (text "text" j)
    | "string" -> Atoms [StrLit (text "text" j)]
    | name -> unsupported ("literal type " ^ name))
  | "union" ->
    (* `unknown` absorbs the rest of its union: semantic top. *)
    (match List.fold_left union (Atoms []) (List.map recur (items "parts" j)) with
    | Atoms atoms when List.mem Top atoms -> top
    | t -> t)
  | "array" -> array {required=[];optional_elements=[];
      rest=Some (recur (field "element" j));readonly=boolean (field "readonly" j)}
  | "tuple" -> array {required=List.map recur (items "required" j);
      optional_elements=List.map recur (items "optional" j);
      rest=(match field "rest" j with Null -> None | t -> Some (recur t));
      readonly=boolean (field "readonly" j)}
  (* A generic method: its signatures quantify lexically scoped binders.
     Self-dependent bounds and mixed value/pack uses remain opaque,
     consistently with Lean's declaration lowering; a rest is a pack
     parameter or any number of actuals at an element, as Lean reads it. *)
  | "scheme" ->
    let binders = items "binders" j and signatures = items "signatures" j in
    let names = List.map (fun b -> text "name" b) binders in
    (* A bound naming the method's own binders, an F-bound, is not what a
       scheme's bounds mean: they are read where the method is declared. *)
    let mentions_own term = List.exists (fun name ->
      let value,pack=binder_use name term in value || pack) names in
    let uses=List.map (fun name -> name,binder_uses name signatures) names in
    let packs=List.filter_map (fun (name,(_,pack)) -> if pack then Some name else None) uses in
    if List.exists (fun (_, (value,pack)) -> value && pack) uses
       || List.exists (fun b -> mentions_own (field "bound" b)) binders then top
    else begin
      let start = match list (field "span" j) with
        | Number n :: _ -> int_of_string n
        | _ -> fail "empty source span" in
      let scope = -1_000_000_000 - start in
      let identities = List.mapi (fun index b -> {scope;index;spelling=text "name" b}) binders in
      let inner = {ctx with bindings =
        List.map (fun (r:rigid) -> r.spelling,
          if List.mem r.spelling packs then PackArgument (PackParameter r)
          else ValueArgument (Rigid r)) identities @ ctx.bindings} in
      let pack_bound t = match text "k" t with
        | "array" -> Pack {required=[];optional_elements=[];
            rest=Some (source_type ctx (field "element" t));readonly=false}
        | "tuple" when items "optional" t = [] && field "rest" t = Null ->
          Pack {required=List.map (source_type ctx) (items "required" t);
            optional_elements=[];rest=None;readonly=false}
        | _ -> unsupported "a pack parameter's bound is an array or a tuple" in
      let quantified = List.map2 (fun identity b ->
        {identity;bound=(match field "bound" b with
          | Null -> None
          | t when List.mem identity.spelling packs -> Some (PackArgument (pack_bound t))
          | t -> Some (ValueArgument (source_type ctx t)))})
        identities binders in
      let calls = List.map (fun f -> match source_type inner f with
        | Atoms [Shape {fields=[];string_index=None;calls=[s];elements=None}] -> {s with quantified}
        | _ -> unsupported "generic method signature") signatures in
      Atoms [Shape {fields=[];string_index=None;calls;elements=None}]
    end
  | "constructor" ->
    (* A construct signature's rest, if any, is one argument list: a pack
       parameter, or any number at an element. *)
    let rest_pack = match field "rest" j with
      | Null -> None
      | t when is_pack t -> Some (source_pack ctx (field "of" t))
      | t -> Some (Pack {required=[];optional_elements=[];rest=Some (recur t);readonly=false}) in
    Atoms [Ctors [{quantified=[];receiver=top;params=List.map recur (items "params" j);
      variadic=None;rest_pack;result=recur (field "result" j)}]]
  | "function" ->
    let receiver = match field "receiver" j with Null -> top | source -> recur source in
    let variadic,rest_pack = match field "rest" j with
      | Null -> None,None
      | t when is_pack t -> None,Some (source_pack ctx (field "of" t))
      | t -> Some (recur t),None in
    let signature = {quantified=[];receiver;
      params=List.map recur (items "params" j);
      variadic;rest_pack;
      result=recur (field "result" j)} in
    Atoms [Shape {fields=[];string_index=None;calls=[signature];elements=None}]
  | "self" -> (match ctx.owner with
    | None -> fail "a method receiver outside a declaration"
    | Some owner ->
      (* A generic declaration's receiver is its application to its own
         parameters, which instantiation makes the instance. *)
      Atoms [Named (owner,List.map (fun r -> Rigid r) ctx.positional)])
  | "object" ->
    let fields = List.map (fun f ->
      let t = recur (field "type" f) in
      {name=property_key (field "name" f);optional=boolean (field "optional" f);
       read=t;write=(if boolean (field "readonly" f) then None else Some t)})
      (items "fields" j) in
    let string_index = match field "stringIndex" j with
      | Null -> None
      | index -> let t = recur (field "value" index) in
        Some {value=t;writable=(if boolean (field "readonly" index) then None else Some t)} in
    let calls = List.map (fun c -> match recur c with
      | Atoms [Shape {fields=[];string_index=None;calls=[signature];elements=None}] -> signature
      | _ -> unsupported "call signature") (items "calls" j) in
    Atoms [Shape {fields;string_index;calls;elements=None}]
  | "reference" ->
    let id = identity (field "target" (field "reference" j)) in
    let args = List.map recur (items "args" j) in
    (match List.assoc_opt id ctx.arity with
    | Some (required,total) when List.length args < required || List.length args > total ->
      fail ("type application arity: " ^ id)
    | Some _ -> ()
    | None -> fail ("reference lacks a declaration " ^ id));
    (* An annotation applies a one-parameter cell or identity declaration
       directly: its body is the argument, substituted. *)
    (match ctx.owner,args,List.assoc_opt id ctx.symbolic with
    | None,[arg],Some (parameter,body) -> Inference.substitute [parameter,ValueArgument arg] body
    | _ -> Atoms [Named (id,args)])
  | "parameter" ->
    let index = match field "index" j with
      | Number n -> (match int_of_string_opt n with
        | Some i when i >= 0 -> i
        | _ -> fail "invalid declaration parameter index")
      | _ -> fail "invalid declaration parameter index" in
    (match List.nth_opt ctx.positional index with
    | Some identity -> Rigid identity
    | None -> fail "declaration parameter index outside declaration")
  | "binder" -> (match List.assoc_opt (text "name" j) ctx.bindings with
    | Some (ValueArgument t) -> t
    | Some (PackArgument _) -> unsupported "an argument pack used as a value type"
    | None -> fail "unbound rigid parameter")
  | "intersection" ->
    (* Function operands are one overloaded callable. A type parameter's
       intersection with another type, `V & DepSafe`, is proposed as the
       parameter: its instances are what the declarations call it at, and Lean
       lowers and checks the whole intersection. In a declaration's equation,
       a parameter of the declaration or a named operand is read once it is
       known, at the application (`Meet`); elsewhere, record operands are the
       one object they describe, and any other ground operands, such as an
       array with a record's members, are kept as `Meet`, whose row Lean
       fills with its own meet. *)
    let parts = List.map recur (items "parts" j) in
    let callable = function
      | Atoms [Shape {fields=[];string_index=None;calls;elements=None}] when calls <> [] -> Some calls
      | _ -> None in
    let rigid = List.find_opt (function Rigid _ -> true | _ -> false) parts in
    (match rigid,parts with
     | Some (Rigid r as rigid),_ when List.mem r ctx.positional ->
       Meet (rigid,List.filter (fun part -> part <> rigid) parts)
     | Some rigid,_ -> rigid
     | None,_ when List.for_all (fun part -> callable part <> None) parts ->
       Atoms [Shape {fields=[];string_index=None;calls=List.concat (List.filter_map callable parts);elements=None}]
     | None,first::rest when ctx.owner <> None -> Meet (first,rest)
     | None,first::rest ->
       (match List.fold_left (fun acc part -> Option.bind acc (fun a -> meet_objects a part))
                (Some first) rest with
        | Some merged -> merged
        | None -> Meet (first,rest))
     | None,[] -> fail "empty intersection")
  | k -> unsupported ("type term " ^ k)
and source_pack ctx j =
  if text "k" j <> "binder" then unsupported "a pack rest must name a type parameter";
  match List.assoc_opt (text "name" j) ctx.bindings with
  | Some (PackArgument p) -> p
  | Some (ValueArgument _) -> unsupported "a value parameter used as an argument pack"
  | None -> fail "unbound pack parameter"

type literal = LNull | LUndefined | LBool of bool | LNumber of string | LString of string

let literal j = match text "a" j with
  | "null" -> LNull | "undefined" -> LUndefined
  | "booleanlit" -> LBool (text "v" j = "true")
  | "numberlit" -> LNumber (text "v" j) | "stringlit" -> LString (text "v" j)
  | k -> unsupported ("literal " ^ k)
let optional_type binders = function Null -> None | j -> Some (source_type binders j)
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
      let quantified={identity;bound=Option.map (fun t -> ValueArgument t)
        (optional_type binders (field "bound" p))} in
      let binders={binders with bindings=(spelling,ValueArgument (Rigid identity))::binders.bindings} in
      loop (index+1) binders (quantified::accumulated) rest in
  loop 0 binders [] parameters
type arithmetic = Add | Sub | Mul | Div
type equality = StrictEqual | StrictUnequal | LooseEqual | LooseUnequal

(* This is a typed view of the shared Fragment, not a new source language.
   Unknown cases fail here; inference exhaustively matches implemented cases. *)
type expr = { pos: Json.t; node: expr_node }
and expr_node =
  | Id of string | Literal of literal | Not of expr | Arith of arithmetic * expr * expr
  (* `typeof e === "shape"` (equal) or `!==`: a test of the operand's shape. *)
  | TypeofTest of string * bool * expr
  | Equality of equality * expr * expr | Alloc of (string * expr) list
  (* A named read: a string key, or the symbol key of `e[k]` with `k` a
     `unique symbol` constant. *)
  | Read of expr * key | Write of expr * string * expr
  | Assign of string * expr
  (* A parameter's type is what the body reads. A defaulted one also admits
     `undefined` where the closure is called; the default replaces it. A rest
     parameter reads the tuple its arguments are collected into, and the
     signature has one position per required element of that tuple. The
     receiver is the `this` annotation of an ordinary function, none for an
     arrow, whose `this` is the enclosing one. *)
  (* The result is none where the source states no result annotation: the
     producer proposes it, and Lean checks the body against that claim. *)
  | Lambda of ty option * quantifier list * (string * ty) list * (int * expr) list * bool * ty option * expr
  (* The positions of the arguments written with `...`: each stands for the
     elements of its operand, read where it is written. *)
  | Call of expr * expr option * expr list * int list
  (* A call through a property reference: the callee is the read of the
     method, and the object it is read from is the receiver. The types are the
     explicit type arguments written on the call, if any. *)
  | Invoke of expr * expr list * int list * ty list
  (* `f.apply(r, list)`: the list's elements, read by index, are the actuals. *)
  | Apply of expr * expr * expr option
  (* A class value: its constructor lambda as construct-only code. *)
  | Ctor of expr
  (* `new callee<types>(args)`: the explicit type arguments, if written,
     name the instantiation proposed for a generic class. *)
  | New of expr * ty list * expr list
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
  (* `for (const name of iterable) body`: the name's position, the iterable
     and the body. *)
  | ForOf of string * Json.t * expr * stmt list
and fn = { quantified: quantifier list; name: string; name_pos: Json.t; params: (string * ty) list;
           rest: bool; result: ty; body: stmt list }
type declaration = { id: string; parameters: rigid list;
  defaults: ty option list; bases: ty list; expression: ty }
(* `init` is the module's top-level code, run once after its function
   declarations exist. *)
(* `values` are the client's value imports, at the types their declarations
   state: assumptions, not checked here. *)
type program = { file: Json.t; digest: Json.t; declarations: declaration list;
                 functions: fn list; init: stmt list; values: (string * ty) list }

let rec expr binders j =
  let sub k = expr binders (field k j) in
  let node = match text "k" j with
  | "id" -> Id (text "name" j) | "lit" -> Literal (literal (field "lit" j))
  | "this" -> Id "this"
  | "not" -> Not (sub "e")
  | "typeofTest" -> TypeofTest (text "shape" j,boolean (field "equal" j),sub "e")
  | "arith" -> let op = match text "op" j with
      | "add" -> Add | "sub" -> Sub | "mul" -> Mul | "div" -> Div
      | k -> unsupported ("arithmetic " ^ k) in Arith (op,sub "l",sub "r")
  | "bin" -> let op = match text "op" j with
      | "===" -> StrictEqual | "!==" -> StrictUnequal
      | "==" -> LooseEqual | "!=" -> LooseUnequal
      | k -> unsupported ("operator " ^ k) in Equality (op,sub "l",sub "r")
  | "alloc" -> Alloc (List.map (fun f -> text "name" f,expr binders (field "e" f)) (items "fields" j))
  | "read" -> Read (sub "e",property_key (field "field" j))
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
          Some (source_type inner (field "type" r)) in
      Lambda (receiver,quantified,
        List.map (fun p -> text "name" p,source_type inner (field "type" p)) parameters,
        List.filter_map (fun (i,p) -> match List.assoc_opt "default" (obj p) with
          | None -> None
          | Some d -> Some (i, expr inner d))
          (List.mapi (fun i p -> i,p) parameters),
        rest,
        optional_type inner (field "result" j),
        expr inner (field "body" j))
  | "ctor" -> Ctor (sub "lambda")
  | "new" ->
    let types = match List.assoc_opt "typeArgs" (obj j) with
      | None -> [] | Some ts -> List.map (source_type binders) (list ts) in
    New (sub "callee",types,List.map (expr binders) (items "args" j))
  | "apply" ->
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    Call (sub "callee",None,List.map (expr binders) (items "args" j),spreads)
  | "invoke" ->
    let spreads = match List.assoc_opt "spreads" (obj j) with
      | None -> [] | Some s -> List.map (fun n -> int_of_string (match n with
          | Json.Number n -> n | _ -> Json.fail "a spread position is a number")) (list s) in
    let type_args = match List.assoc_opt "typeArgs" (obj j) with
      | None -> [] | Some ts -> List.map (source_type binders) (list ts) in
    Invoke (sub "callee",List.map (expr binders) (items "args" j),spreads,type_args)
  | "applyWithReceiver" ->
    Apply (sub "callee",sub "receiver",(match field "list" j with Null -> None | l -> Some (expr binders l)))
  | "callWithReceiver" ->
    Call (sub "callee",Some (sub "receiver"),List.map (expr binders) (items "args" j),[])
  | "coalesce" -> Coalesce (sub "left",sub "right")
  | "arrayLit" -> ArrayLiteral (List.map (expr binders) (items "elems" j))
  | "index" -> Index (sub "e",sub "key")
  | "indexWrite" -> IndexWrite (sub "receiver",sub "key",sub "rhs")
  | "withValue" -> WithFields (sub "fn",sub "initial",source_type binders (field "functionType" j),source_type binders (field "bagType" j))
  | "bindWithReceiver" -> Bind (sub "callee",sub "receiver",List.map (expr binders) (items "args" j))
  | "cast" -> Cast (text "cast" j,(match field "annot" j with Null -> None | a -> Some (source_type binders a)),sub "e")
  | "doneBody" -> DoneBody | "returnBody" -> ReturnBody (sub "e")
  | "seqBody" -> SequenceBody (sub "init",sub "body")
  | "letBody" -> LetBody (text "name" j,(match field "annot" j with Null -> None | a -> Some (source_type binders a)),sub "init",sub "body")
  | "ifBody" -> IfBody (source_type binders (field "result" j),sub "cond",sub "then",sub "else_")
  | "conditional" -> Conditional (sub "cond",sub "then",sub "else_")
  | k -> unsupported ("expression " ^ k) in {pos=field "pos" j;node}
let rec stmt binders j =
  let statement = match text "k" j with
  | "const" | "let" -> Declare (text "k" j="let",List.map (fun b ->
      text "name" b,optional_type binders (field "annot" b),expr binders (field "init" b)) (items "bindings" j))
  | "return" -> Return (expr binders (field "e" j)) | "effect" -> Effect (expr binders (field "e" j))
  | "while" -> While (expr binders (field "cond" j),List.map (stmt binders) (items "body" j))
  | "forOf" -> ForOf (text "name" j,field "namePos" j,expr binders (field "iterable" j),
      List.map (stmt binders) (items "body" j))
  | "break" -> Break | "continue" -> Continue
  | "if" -> If (expr binders (field "cond" j),List.map (stmt binders) (items "then" j),
      match field "else_" j with Null -> [] | xs -> List.map (stmt binders) (list xs))
  | k -> unsupported ("statement " ^ k) in {span=field "pos" j;statement}
let decode ast =
  let document = field "declarations" ast in
  let arity = List.map (fun definition ->
    let parameters = items "parameters" definition in
    identity (field "declaration" definition),
      (List.length (List.filter (fun p -> field "default" p = Null) parameters),
       List.length parameters)) (items "definitions" document) in
  let definitions = List.mapi (fun index definition ->
    let id = identity (field "declaration" definition) in
    let parameters = List.mapi (fun i p -> {scope= -1-index;index=i;spelling=text "name" p})
      (items "parameters" definition) in
    let body = source_type {bindings=[];owner=Some id;positional=parameters;arity;symbolic=[]} in
    {id;parameters;
     defaults=List.map (fun p -> match field "default" p with
       | Null -> None | j -> Some (body j)) (items "parameters" definition);
     bases=List.map body (items "bases" definition);
     expression=body (field "expression" definition)})
    (items "definitions" document) in
  let locals = List.map (fun root ->
    let id=identity (field "declaration" root) in
    if not (List.exists (fun d -> d.id=id) definitions) then
      fail ("import root lacks definition " ^ id);
    text "local" (field "binding" root)) (items "roots" document) in
  if List.length (List.sort_uniq compare locals) <> List.length locals then
    fail "duplicate declaration root name";
  let symbolic = List.filter_map (fun d ->
    match d.parameters,d.defaults,d.bases,d.expression with
    | [parameter],[None],[],(Rigid identity as body) when identity=parameter ->
      Some (d.id,(parameter,body))
    | [parameter],[None],[],(Atoms [Shape shape] as body) ->
      (match shape.fields,shape.string_index,shape.calls,shape.elements with
      | [{name=Name "value";optional=false;read=Rigid identity;
          write=Some (Rigid written)}],None,[],None
          when identity=parameter && written=parameter ->
        Some (d.id,(parameter,body))
      | _ -> None)
    | _ -> None) definitions in
  let top={bindings=[];owner=None;positional=[];arity;symbolic} in
  { file=field "file" ast;digest=field "sourceSha256" ast;
    declarations=definitions;
    init=List.map (stmt top) (items "init" ast);
    values=List.mapi (fun index v ->
      (* A generic value's binders quantify its one signature. *)
      let binders,quantified = quantify top (-1000-index) (items "typeParams" v) in
      text "local" (field "binding" v),
      (match source_type binders (field "type" v),quantified with
       | t,[] -> t
       | Atoms [Shape ({calls=[call];_} as shape)],_ ->
         Atoms [Shape {shape with calls=[{call with quantified}]}]
       | Atoms [Ctors [signature]],_ -> Atoms [Ctors [{signature with quantified}]]
       | _ -> unsupported "a generic imported value must be one callable"))
      (items "values" document);
    functions=List.mapi (fun scope f ->
      let parameters = items "typeParams" f in
      let initial={bindings=[];owner=None;positional=[];arity;symbolic} in
      let binders,quantified = quantify initial scope parameters in
      {quantified;name=text "name" f; name_pos=field "namePos" f;
      params=List.map (fun p -> text "name" p,source_type binders (field "type" p)) (items "params" f);
      rest=List.exists (fun p -> List.mem_assoc "rest" (obj p)) (items "params" f);
      result=source_type binders (field "retType" f);body=List.map (stmt binders) (items "body" f)}) (items "functions" ast) }
