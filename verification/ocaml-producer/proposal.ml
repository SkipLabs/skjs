open Semantic
open Environment
open Source
open Inference

type entry = { start: Json.t; bindings: (string * binding) list }
(* A call site's proposed substitution travels with its claim. It is proposal
   output for Lean to re-check, never an acceptance fact. *)
type expression = { pos: Json.t; type_: ty; instantiation: (string * type_argument) list option }
(* One closure advertising several signatures has one body and a separate
   obligation at each: the interior claims are collected once per signature,
   keyed by the closure's span and ordered with the signatures. *)
type overlay = { row_entries: entry list; row_expressions: expression list }
type function_claim = { source: fn; entries: entry list; expressions: expression list;
                        arrows: (Json.t * overlay list) list }
type t = { program: program; functions: function_claim list; init: function_claim option }
let unsupported s = Json.fail ("unsupported: " ^ s)
let combine = List.fold_left union (Atoms [])
(* A proposal heuristic for choosing an advertised arrow. It does not
   establish subtyping: Lean checks the selected call and its arguments. *)
let rec plausible_subtype actual expected =
  if actual=expected then true else match actual,expected with
  | Atoms _,Atoms [Top] -> true
  | Atoms xs,Atoms ys -> List.for_all (fun x -> List.exists (fun y ->
      x=y || match x,y with
      | NumLit _,Num | StrLit _,Str | BigintLit _,Bigint -> true
      | _ -> false) ys) xs
  | Union parts,_ -> List.for_all (fun part -> plausible_subtype part expected) parts
  | _,Union parts -> List.exists (plausible_subtype actual) parts
  (* A value of an intersection is a value of each operand. *)
  | Meet (t,ts),_ -> List.exists (fun part -> plausible_subtype part expected) (t::ts)
  | Rigid _,_ | _,(Rigid _ | Meet _) -> false
let literal_type = function
  | LNull -> Atoms [Nul] | LUndefined -> Atoms [Undef]
  | LBool true -> Atoms [True] | LBool false -> Atoms [False]
  | LNumber s -> number_literal s | LString s -> Atoms [StrLit s]
  | LBigint s -> Atoms [BigintLit s]

(* Read permissions do not imply write permissions. All candidates still pass
   through reconstructed obligations, including readonly view conversion. *)
let definition declarations id args =
  (* An interface and its base as one object: disjoint fields, and the one
     index signature either states. A hint only: Lean's `inheritRows` gives
     the declaration's meaning. *)
  let merge base own = match meet_objects base own with
    | Some t -> t
    | None -> (match base,own with
      (* A base that holds every record, `{}` or `object`, adds nothing to
         the interface's own record: their meet is that record. *)
      | Atoms atoms,Atoms [Shape _] when List.mem Top atoms ||
          List.mem (Shape {fields=[];indexes=[];calls=[];elements=None}) atoms -> own
      | Atoms [Shape inherited],Atoms [Shape local]
        when inherited.calls=[] && local.calls=[] && inherited.elements=None && local.elements=None
             && (inherited.indexes=[] || local.indexes=[]) ->
        unsupported "overlapping inherited fields need compatibility checking"
      | _ -> unsupported "inheritance needs plain object contracts") in
  let rec instantiate seen id args =
  if List.mem id seen then unsupported "cyclic inheritance";
  match List.find_opt (fun (d:Source.declaration) -> d.id=id) declarations with
  | Some d ->
    if List.length args > List.length d.parameters then
      unsupported "type application has wrong arity";
    let rec complete previous supplied parameters defaults =
      match parameters, defaults with
      | [], [] -> List.rev previous
      | parameter::rest, default::other ->
        let value, supplied = match supplied with
          | value::tail -> value,tail
          | [] -> (match default with
            | Some value -> value,[]
            | None -> unsupported "type application has missing required argument") in
        let value = Inference.substitute (List.rev previous) value in
        complete ((parameter,ValueArgument value)::previous) supplied rest other
      | _ -> unsupported "declaration parameter/default length mismatch" in
    let solution = complete [] args d.parameters d.defaults in
    (* An intersection of the equation, its arguments substituted, is the one
       object its operands describe where they are records, a declared one
       read through its equation (`Serializable<Todo>`); otherwise, with ground
       operands, it stays their intersection, a row Lean fills with their meet
       (`[number, number] & DepSafe`), and over a type parameter it is its
       principal operand, the argument, as a type parameter's intersection is
       proposed. *)
    let meet t ts =
      let expand t = match t with
        | Atoms [Named (named,named_args)] when not (List.mem named (id::seen)) ->
          (try instantiate (id::seen) named named_args with Json.Error _ -> t)
        | t -> t in
      match List.fold_left (fun acc part -> Option.bind acc (fun a -> meet_objects a (expand part)))
              (Some (expand t)) ts with
      | Some merged -> merged
      | None -> if List.exists Semantic.mentions_rigid (t::ts) then t else Meet (t,ts) in
    let body = Inference.substitute ~meet solution d.expression in
    List.fold_left (fun own base ->
      match Inference.substitute ~meet solution base with
      | Atoms [Named (baseId,baseArgs)] ->
        merge (instantiate (id::seen) baseId baseArgs) own
      | _ -> unsupported "heritage is not a named base")
      body d.bases
  | None -> unsupported ("missing declaration " ^ id) in
  instantiate [] id args
(* A declaration's equation, for inference to look inside an application. *)
let expand_named declarations = function
  | Atoms [Named (id,args)] ->
    (try Some (definition declarations id args) with Json.Error _ -> None)
  | _ -> None
(* Inspect a declared callable's source equation for proposal purposes only.
   The point claim remains the named type; Lean independently fills and checks
   that graph row from the same declaration. *)
let rec declared_head declarations seen = function
  | Atoms [Named (id,args)] ->
    if List.mem id seen then unsupported "unguarded callable alias cycle";
    declared_head declarations (id::seen) (definition declarations id args)
  | t -> t
(* The first operand of an intersection a read succeeds on. *)
let first_part read parts =
  match List.find_map (fun t -> try Some (read t) with Json.Error _ -> None) parts with
  | Some t -> t
  | None -> unsupported "read on an intersection none of whose operands has it"
(* `ArrayProto`, the declaration of `Array.prototype`'s members, by identity. *)
let array_prototype = "skjs/array-prototype#0:0"
let key_text = function Name n -> n | Key i -> "[symbol " ^ string_of_int i ^ "]"
(* The contract of the prototype a primitive's members are read through:
   `StringProto` for a string, and so on. *)
let primitive_prototype = function
  | Str | StrLit _ -> Some "skjs/string-prototype#0:0"
  | Num | NumLit _ -> Some "skjs/number-prototype#0:0"
  | Bigint | BigintLit _ -> Some "skjs/bigint-prototype#0:0"
  | True | False -> Some "skjs/boolean-prototype#0:0"
  | _ -> None
(* The ground bounds of the binders of the function being proposed: a
   bounded binder's value is read at its bound (TypeScript's apparent type),
   and Lean reads the binder as the meet of its row and the bound. *)
let rigid_bounds : (Semantic.rigid * ty) list ref = ref []
let rigid_bound r = List.assoc_opt r !rigid_bounds
(* The property key a number spells (`ToString`), for integers below 1e21
   and decimals `%g` writes as JavaScript does; none otherwise. *)
let number_key bits =
  let n = Int64.float_of_bits bits in
  if Float.is_integer n && Float.abs n < 1e21 then Some (Printf.sprintf "%.0f" (Float.abs n) |> fun s ->
    if n < 0. then "-" ^ s else s)
  else if Float.is_finite n then
    let rec shortest p = if p > 17 then None else
      let s = Printf.sprintf "%.*g" p n in
      if float_of_string s = n then (if String.contains s 'e' then None else Some s) else shortest (p+1) in
    shortest 1
  else None
(* Whether a key is canonical numeric: the spelling of the number it reads
   as, which is the key `o[n]` reaches for that number. *)
let canonical_numeric s =
  s = "NaN" || s = "Infinity" || s = "-Infinity" ||
  (match float_of_string_opt s with
   | Some n -> number_key (Int64.bits_of_float n) = Some s
   | None -> false)
(* The index of a shape whose class surely admits a key: the canonical
   numeric keys' first, which is the narrowest, then every string key's; a
   symbol key's. *)
let index_for (shape:shape) name =
  let find keys = List.find_opt (fun (i:Semantic.index_signature) -> i.keys=keys) shape.indexes in
  match name with
  | Name s ->
    (match (if canonical_numeric s then find Numeric else None) with
     | Some i -> Some i | None -> find Strings)
  | Key _ -> find Symbols
let rec field_type declarations seen t name = match t with
  | Atoms atoms -> combine (List.map (function
      | Shape {elements=Some _;_} when name=Name "length" -> Atoms [Num]
      (* Any other key of an array is read from its prototype. *)
      | Shape {elements=Some _;_} ->
        field_type declarations seen (Atoms [Named (array_prototype,[])]) name
      | Shape shape -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) shape.fields with
          | Some f -> if f.optional then union f.read (Atoms [Undef]) else f.read
          | None -> (match index_for shape name with
            | Some index -> union index.value (Atoms [Undef])
            | None -> unsupported ("missing field " ^ key_text name)))
      | Exact fields -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) fields with
          | Some f -> f.read
          | None -> unsupported ("missing field " ^ key_text name))
      | Named (id,args) ->
        if List.mem id seen then unsupported "unguarded field cycle";
        field_type declarations (id::seen) (definition declarations id args) name
      (* A string owns its `length`; any other member of a primitive is its
         wrapper prototype's. *)
      | Str | StrLit _ when name=Name "length" -> Atoms [Num]
      | atom when primitive_prototype atom <> None ->
        field_type declarations seen (Atoms [Named (Option.get (primitive_prototype atom),[])]) name
      | _ -> unsupported "field read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> field_type declarations seen t name) ts)
  (* A value of an intersection is one of each operand: read as the first
     operand that has the field, a hint Lean checks. *)
  | Meet (t,ts) -> first_part (fun t -> field_type declarations seen t name) (t::ts)
  | Rigid r -> (match rigid_bound r with
    | Some b -> field_type declarations seen b name
    | None -> unsupported "field read on rigid parameter")
(* Whether writing the key would add a property: the object is a record (not
   an array, a dictionary or a declaration of either) none of whose arms has
   it. An object's keys are fixed where it is allocated, in JavaScript's
   meaning of a record type as in the model's, so such a write is refused by
   name rather than left to fail in search (TypeScript refuses it too). *)
let adds_key declarations t name =
  match (try declared_head declarations [] t with Json.Error _ -> t) with
  | Atoms (_::_ as atoms) -> List.for_all (function
      | Shape {elements=None;indexes=[];calls=[];fields;_} ->
        not (List.exists (fun (f:Semantic.field) -> f.name=name) fields)
      | Exact fields -> not (List.exists (fun (f:Semantic.field) -> f.name=name) fields)
      | _ -> false) atoms
  | _ -> false
(* Whether the key is a writable optional field of some arm and a required
   or readonly one of none: writing it may add it, where the object was
   allocated without it. (A readonly one grants no write, which Lean
   refuses.) *)
let may_add_key declarations t name =
  match (try declared_head declarations [] t with Json.Error _ -> t) with
  | Atoms (_::_ as atoms) ->
    let field = function
      | Shape {elements=None;calls=[];fields;_} | Exact fields ->
        List.find_opt (fun (f:Semantic.field) -> f.name=name) fields
      | _ -> None in
    List.exists (fun a -> match field a with Some f -> f.optional | None -> false) atoms
    && not (List.exists (fun a -> match field a with
      | Some f -> not f.optional || f.write = None | None -> false) atoms)
  | _ -> false
let refuse_growth declarations t name =
  if adds_key declarations t name then
    unsupported ("a write adds the property '" ^ key_text name ^ "'"
      ^ " to an object allocated without it: an object's keys are fixed at its allocation");
  if may_add_key declarations t name then
    unsupported ("a write to the optional property '" ^ key_text name ^ "'"
      ^ " adds it where the object was allocated without it: an object's keys are fixed at its allocation")
(* What a fresh array literal expected at an iterable type holds, found as
   TypeScript finds it: the expected type's member under the key
   `Array.prototype` iterates by (its one symbol key, `[Symbol.iterator]`),
   the `next` results of that member's result other than a finished one, and
   their `value`. A construction hint only: Lean proves the literal, a
   `readonly T[]`, below the expected type. *)
let iterated_hint declarations expected =
  let expand = function Atoms [Named (id,args)] -> definition declarations id args | t -> t in
  let shape t = match expand t with Atoms [Shape s] -> Some s | _ -> None in
  let member key t = Option.bind (shape t) (fun s ->
    Option.map (fun (f:Semantic.field) -> f.read)
      (List.find_opt (fun (f:Semantic.field) -> f.name=key) s.fields)) in
  let result t = Option.bind (shape t) (fun s -> match s.calls with
    | c :: _ -> Some c.result | [] -> None) in
  (* A union's alternatives, through the aliases that name it. *)
  let rec parts seen t = match t with
    | Union ts -> List.concat_map (parts seen) ts
    | Atoms [Named (id,args)] when not (List.mem id seen) ->
      (match definition declarations id args with
       | Atoms [Shape _] -> [t]
       | body -> parts (id::seen) body)
    | Atoms (_::_::_ as atoms) -> List.concat_map (fun a -> parts seen (Atoms [a])) atoms
    | t -> [t] in
  let ( let* ) = Option.bind in
  let* key = Option.bind (shape (Atoms [Named (array_prototype,[])])) (fun s ->
    List.find_map (fun (f:Semantic.field) -> match f.name with
      | Key _ -> Some f.name | Name _ -> None) s.fields) in
  let* iterator = Option.bind (member key expected) result in
  let* results = Option.bind (member (Name "next") iterator) result in
  match List.filter_map (fun r -> match member (Name "done") r with
      | Some (Atoms [True]) -> None
      | _ -> member (Name "value") r) (parts [] results) with
  | [] -> None
  | values -> Some (combine values)
let rec index_type declarations seen receiver key = match receiver with
  | Atoms atoms -> combine (List.map (function
      | Shape {elements=Some sequence;_} ->
        let at i = if i < 0 then Atoms [Undef]
          else match List.nth_opt sequence.required i with
          | Some t -> t
          | None -> let offset=i-List.length sequence.required in
            union (Atoms [Undef]) (match List.nth_opt sequence.optional_elements offset with
              | Some t -> t | None -> Option.value sequence.rest ~default:(Atoms [])) in
        (match key with
          | Atoms [NumLit bits] -> let n=Int64.float_of_bits bits in
            if n >= 0. && n < float_of_int max_int && Float.floor n=n then at (int_of_float n)
            else Atoms [Undef]
          | _ -> combine (Atoms [Undef] :: sequence.required @ sequence.optional_elements @ Option.to_list sequence.rest))
      | Shape shape -> (match key with
          | Atoms [StrLit name] -> field_type declarations seen (Atoms [Shape shape]) (Name name)
          (* A number names the property its `ToString` spells. *)
          | Atoms (NumLit bits :: rest) when List.for_all (fun a -> a = NumLit bits
              || (match a with NumLit b -> Int64.float_of_bits b = Int64.float_of_bits bits | _ -> false)) rest
              && Option.is_some (number_key bits) ->
            field_type declarations seen (Atoms [Shape shape]) (Name (Option.get (number_key bits)))
          (* A dynamic key reads through an index over its keys: a string
             through a string index, a number through a number index or a
             string one, a symbol through a symbol index. *)
          | Atoms [(Str | Num | Symbol) as k] ->
            let within = match k with
              | Str -> [Strings] | Num -> [Numeric;Strings] | _ -> [Symbols] in
            (match List.find_map (fun keys -> List.find_opt
                (fun (i:Semantic.index_signature) -> i.keys=keys) shape.indexes) within with
              | Some index -> union index.value (Atoms [Undef])
              | None -> unsupported "dynamic index requires a dictionary over its keys")
          | _ -> unsupported "record index requires a string key")
      | Exact _ as atom -> (match key with
          | Atoms [StrLit name] -> field_type declarations seen (Atoms [atom]) (Name name)
          | Atoms [NumLit bits] when number_key bits <> None ->
            field_type declarations seen (Atoms [atom]) (Name (Option.get (number_key bits)))
          | _ -> unsupported "record index requires a string key")
      | Named (id,args) ->
        if List.mem id seen then unsupported "unguarded index cycle";
        index_type declarations (id::seen) (definition declarations id args) key
      (* A string's index properties are its code units: a numeric key reads
         one, or `undefined` past the end. A string literal key is a named
         member's. *)
      | (Str | StrLit _) as atom -> (match key with
          | Atoms [StrLit name] -> field_type declarations seen (Atoms [atom]) (Name name)
          | Atoms ks when ks <> [] && List.for_all (function Num | NumLit _ -> true | _ -> false) ks ->
            Atoms [Str;Undef]
          | _ -> unsupported "a string's index needs a numeric key")
      (* Another primitive's named member is its wrapper prototype's. *)
      | atom when primitive_prototype atom <> None -> (match key with
          | Atoms [StrLit name] -> field_type declarations seen (Atoms [atom]) (Name name)
          | _ -> unsupported "a primitive's member needs a string literal key")
      | _ -> unsupported "indexed read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> index_type declarations seen t key) ts)
  | Meet (t,ts) -> first_part (fun t -> index_type declarations seen t key) (t::ts)
  | Rigid r -> (match rigid_bound r with
    | Some b -> index_type declarations seen b key
    | None -> unsupported "indexed read on rigid parameter")

(* A fresh literal is built at the one object contract its expected type
   names: a record or dictionary shape, possibly behind a declaration (a class
   instance, or the dictionary arm of a recursive type). This is a construction
   hint only: every field still has a source obligation against the contract.
   Existing objects never gain a dictionary guarantee by this lookup. *)
let rec object_hint declarations seen = function
  | Atoms atoms ->
    let choices = List.filter_map (function
      | Shape ({elements=None;_} as shape) -> Some shape
      | Named (id,args) when not (List.mem id seen) ->
        object_hint declarations (id::seen) (definition declarations id args)
      | _ -> None) atoms in
    (match choices with [shape] -> Some shape | _ -> None)
  | Union parts ->
    (match List.filter_map (object_hint declarations seen) parts with
    | [shape] -> Some shape | _ -> None)
  | Rigid _ | Meet _ -> None

(* Where the expected type is a union of several records or several arrays,
   a fresh literal is built at the one arm its own keys (or length) and its
   literal-valued members select, as TypeScript discriminates a contextual
   union by a literal's properties: `{ kind: "a", n: 1 }` at
   `{ kind: "a"; n: number } | { kind: "b"; s: string }` is built at the
   first arm, so its `kind` holds the literal type the arm fixes rather than
   the widened `string` no arm admits. A construction hint only, as
   [object_hint] is: Lean checks every member against the arm, and no other
   arm is ever assumed. *)
let literal_admitted declarations (e:expr) t = match e.node with
  | Literal l -> plausible_subtype (literal_type l) (declared_head declarations [] t)
  | _ -> true
let rec record_arms declarations seen = function
  | Atoms atoms -> List.concat_map (function
      | Shape ({elements=None;calls=[];_} as shape) -> [shape]
      | Named (id,args) when not (List.mem id seen) ->
        record_arms declarations (id::seen) (definition declarations id args)
      | _ -> []) atoms
  | Union parts -> List.concat_map (record_arms declarations seen) parts
  | Rigid _ | Meet _ -> []
let discriminated_record declarations expected (members:(string * expr) list) =
  let admits (s:shape) =
    List.for_all (fun (name,e) ->
      match List.find_opt (fun (f:field) -> f.name = Name name && not f.host) s.fields with
      | Some f -> literal_admitted declarations e f.read
      | None -> index_for s (Name name) <> None) members
    && List.for_all (fun (f:field) -> f.optional || f.host
      || (match f.name with Name n -> List.mem_assoc n members | Key _ -> false)) s.fields in
  match List.filter admits (record_arms declarations [] expected) with
  | [shape] -> Some shape
  | _ -> None
let discriminated_array declarations (arms:sequence list) (elements:expr list) =
  let n = List.length elements in
  let admits (s:sequence) =
    let fixed = s.required @ s.optional_elements in
    n >= List.length s.required && (s.rest <> None || n <= List.length fixed)
    && List.for_all Fun.id (List.mapi (fun i e -> match List.nth_opt fixed i with
      | Some t -> literal_admitted declarations e t
      | None -> Option.fold ~none:false ~some:(literal_admitted declarations e) s.rest) elements) in
  match List.filter admits arms with
  | [s] -> Some s
  | _ -> None

(* The numeric family of an operand: bigint where every atom is one. *)
let numeric_family declarations t =
  match declared_head declarations [] t with
  | Atoms (_::_ as atoms) when List.for_all (function Bigint | BigintLit _ -> true | _ -> false) atoms ->
    Atoms [Bigint]
  | _ -> Atoms [Num]

(* Whether every value of a type is a string. *)
let string_like declarations t =
  match declared_head declarations [] t with
  | Atoms (_::_ as atoms) -> List.for_all (function Str | StrLit _ -> true | _ -> false) atoms
  | _ -> false

(* What an arithmetic operator yields: a string for `+` with a string
   operand, which concatenates; else the numeric family of the left operand.
   Lean checks the operands pair by pair. *)
let operation_result declarations op left right =
  if op = Add && (string_like declarations left || string_like declarations right) then Atoms [Str]
  else numeric_family declarations left

(* The atoms of `t` that may be (`equal`) or may not be strictly equal to a
   singleton value. Unknown/rigid predicates conservatively retain their type;
   proof checking validates each narrower cut. *)
let restrict singleton equal t = match t with
  | Atoms xs -> ground (List.filter (fun atom ->
      let known = match atom,singleton with
        | Nul,Nul | Undef,Undef | True,True | False,False -> Some true
        (* Number::equal: NaN equals nothing, and the zeros each other. *)
        | NumLit a,NumLit b -> Some (Int64.float_of_bits a = Int64.float_of_bits b)
        | StrLit a,StrLit b -> Some (a=b)
        | BigintLit a,BigintLit b -> Some (a=b)
        | Num,NumLit _ | Str,StrLit _ | Bigint,BigintLit _ -> None
        (* A declaration's atoms are not known here; any other atom is of
           another kind than the singleton, or an object, never equal to it. *)
        | (Top | Named _),_ -> None
        | _,_ -> Some false in
      match known with Some result -> result=equal | None -> true) xs)
  | Rigid _ | Union _ | Meet _ -> t
(* The one value every member of a type is, as Lean selects a singleton
   operand: null, undefined, a Boolean, a string, a bigint, or one number
   (both zeros are one). *)
let singleton_atom = function
  | Atoms [(Nul | Undef | True | False | StrLit _ | BigintLit _ | NumLit _) as a] -> Some a
  | Atoms (NumLit b :: rest) when List.for_all (function
      | NumLit c -> Int64.float_of_bits c = Int64.float_of_bits b | _ -> false) rest -> Some (NumLit b)
  | _ -> None
(* The arms of an object's union that may remain once its field `key` was
   found (not) equal to something: an arm whose field, sliced by that outcome,
   holds nothing is dropped. The arm stays dropped whatever the field holds
   later: an object's arm is fixed where it is allocated. Lean checks the
   slice. *)
let discriminate declarations t key slice =
  match declared_head declarations [] t with
  | Atoms atoms ->
    let admits atom =
      match (try Some (field_type declarations [] (Atoms [atom]) key) with Json.Error _ -> None) with
      | Some field -> slice field <> Atoms []
      | None -> true in
    let kept = List.filter admits atoms in
    if List.length kept = List.length atoms then t else Atoms kept
  | Rigid _ | Union _ | Meet _ -> t
(* An immutable binding declared at a named union is held at the union's
   arms, the same values: a guard then keeps or drops each arm, and a read
   splits on them. Lean checks the declared type below the arms on the edge
   from the declaration. *)
let arms declarations t = match t with
  | Atoms [Named _] ->
    (match (try Some (declared_head declarations [] t) with Json.Error _ -> None) with
     | Some (Atoms (_::_::_ as atoms)) -> Atoms atoms
     | _ -> t)
  | _ -> t
(* Keep the atoms of a `typeof` test's shape where it holds, and the others
   where it fails. *)
let typeof_slice shape holds = function
  | Atoms xs when not (List.mem Top xs) ->
    let has = function
      (* `Array.isArray`: an array owns its store; an open record may be an
         array carrying other keys, and stays on both arms. *)
      | Shape s when shape="array" ->
        if s.elements<>None then Some true else if s.calls<>[] then Some false else None
      | Top | Named _ when shape="array" -> None
      | _ when shape="array" -> Some false
      (* `"object"`: null, or an object without call code. *)
      | Nul when shape="object" -> Some true
      | Shape s when shape="object" -> Some (s.calls=[])
      | Exact _ when shape="object" -> Some true
      | Num | NumLit _ -> Some (shape="number") | Str | StrLit _ -> Some (shape="string")
      | True | False -> Some (shape="boolean") | Undef -> Some (shape="undefined")
      | Bigint | BigintLit _ -> Some (shape="bigint") | Symbol -> Some (shape="symbol")
      | Shape s -> Some (shape="function" && s.calls<>[])
      | Exact _ -> Some false
      (* A class is a function to `typeof`. *)
      | Ctors _ | Callable -> Some (shape="function")
      | Nul -> Some false
      (* A declaration's shape is not known here: it stays on both arms. No
         value is an argument pack. *)
      | Top | Named _ -> None in
    Atoms (List.filter (fun a -> match has a with
      | Some result -> result = holds | None -> true) xs)
  (* `unknown`, where a test naming one primitive family holds: that
     family, whatever the value was (a caught value, say). *)
  | Atoms _ when holds ->
    (match shape with
     | "string" -> Atoms [Str] | "number" -> Atoms [Num] | "bigint" -> Atoms [Bigint]
     | "symbol" -> Atoms [Symbol] | "undefined" -> Atoms [Undef] | "boolean" -> bool
     | _ -> Atoms [Top])
  | t -> t
(* Keep the atoms that may own the key where `key in o` held, and those that
   may lack it where it failed: a record's required field is owned, a fresh
   literal's keys are exactly its fields', and a primitive owns none. *)
let key_slice key holds = function
  | Atoms xs when not (List.mem Top xs) ->
    let field_of fields = List.find_opt (fun (f:Semantic.field) -> f.name = Name key) fields in
    let has = function
      | Shape s -> (match field_of s.fields with
        | Some f when not f.optional -> Some true | _ -> None)
      | Exact fields -> (match field_of fields with
        | Some f -> if f.optional then None else Some true | None -> Some false)
      | Ctors _ | Callable | Named _ | Top -> None
      | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _
      | Bigint | Symbol | BigintLit _ -> Some false in
    Atoms (List.filter (fun a -> match has a with
      | Some result -> result = holds | None -> true) xs)
  | t -> t
(* Whether a field's contents can be asserted of an object of this type: a
   plain record that has the field, not optionally. *)
let single_record declarations t field =
  match (try Some (declared_head declarations [] t) with Json.Error _ -> None) with
  | Some (Atoms [Shape {fields;calls=[];elements=None;indexes=[]}])
  | Some (Atoms [Exact fields]) ->
    List.exists (fun (f:Semantic.field) -> f.name = Name field && not f.optional) fields
  | _ -> false
(* A guard on a field of an immutable binding's object: what the field holds
   is known until a step may write it. *)
let refine_field declarations env name field refine =
  match List.assoc_opt name env with
  | Some (Value t) when single_record declarations t field ->
    let key = field_key name field in
    let current = match List.assoc_opt key env with
      | Some (Value c) -> Some c
      | _ -> (try Some (field_type declarations [] t (Name field)) with Json.Error _ -> None) in
    (match current with Some c -> fact env key (refine c) | None -> env)
  | _ -> env
let rec branch_with declarations env cond truth =
  let branch = branch_with declarations in
  let refine_field = refine_field declarations in
  match cond.node with
  | Not e -> branch env e (not truth)
  (* A name as a condition is tested for truthiness; a Boolean's slice is
     its literal. *)
  | Id name -> refine_value env name (truthy_slice truth)
  | Read ({node=Id name;_},Name field) -> refine_field env name field (truthy_slice truth)
  (* A true `&&` (a false `||`) established both operands so; the other
     answer came from either operand, the right one after the left answered
     the first way, and holds what either established. *)
  | Logical (conjunction,a,b) when truth = conjunction -> branch (branch env a truth) b truth
  | Logical (_,a,b) ->
    let either = branch env a truth and later = branch (branch env a (not truth)) b truth in
    (* A field's contents are known where both paths know them. *)
    List.filter_map (fun (n,x) -> match x,List.assoc_opt n later with
      | Value l,Some (Value r) -> Some (n,Value (union l r))
      | Storage (contract,l),Some (Storage (_,r)) -> Some (n,holding contract (union l r))
      | _ when is_field n -> None
      | _ -> Some (n,x)) either
  | TypeofTest (shape,equal,{node=Id name;_}) ->
    refine_value env name (typeof_slice shape (truth = equal))
  | HasKey ({node=Literal (LString key);_},{node=Id name;_}) -> refine_value env name (key_slice key truth)
  | TypeofTest (shape,equal,{node=Read ({node=Id name;_},Name field);_}) ->
    refine_field env name field (typeof_slice shape (truth = equal))
  (* `x == null` holds of null and undefined alike. *)
  | Equality ((LooseEqual | LooseUnequal as op),{node=Id name;_},{node=Literal (LNull | LUndefined);_})
  | Equality ((LooseEqual | LooseUnequal as op),{node=Literal (LNull | LUndefined);_},{node=Id name;_}) ->
    let equal = truth=(op=LooseEqual) in
    refine_value env name (fun t ->
      if equal then union (restrict Nul true t) (restrict Undef true t)
      else restrict Undef false (restrict Nul false t))
  (* A comparison with a singleton, a literal or a name or field holding one,
     narrows the other operand where it is a name, or a field of a name's
     object, and that object's arms, on both outcomes. Where it holds, one
     with a name or field holding one of several singletons narrows the
     other to the values that may equal one of them. *)
  | Equality ((StrictEqual | StrictUnequal as op),l,r) ->
    let equal = truth=(op=StrictEqual) in
    let values (e:expr) = Option.bind (match e.node with
      | Literal lit -> Some (literal_type lit)
      | Id n -> Option.map binding_type (List.assoc_opt n env)
      | Read ({node=Id n;_},Name f) ->
        (match List.assoc_opt (field_key n f) env,List.assoc_opt n env with
         | Some b,_ -> Some (binding_type b)
         | None,Some b -> (try Some (field_type declarations [] (binding_type b) (Name f)) with Json.Error _ -> None)
         | None,None -> None)
      | _ -> None) (fun t -> match singleton_atom t,t with
        | Some a,_ -> Some ((fun t -> restrict a equal t),true)
        | None,Atoms (_::_ as atoms) when equal
            && List.for_all (fun a -> singleton_atom (Atoms [a]) <> None) atoms ->
          Some ((fun t -> combine (List.map (fun a -> restrict a true t) atoms)),false)
        | _ -> None) in
    (* What a field holds is known from a test against one singleton, whose
       saved read Lean observes; several are tested one read at a time. *)
    let narrow env (operand:expr) other = match values other,operand.node with
      | None,_ -> env
      | Some (slice,_),Id name -> refine_value env name slice
      | Some (slice,single),Read ({node=Id name;_},key) ->
        let env = refine_value env name (fun t -> discriminate declarations t key slice) in
        (match key with
         | Name field when single -> refine_field env name field slice
         | _ -> env)
      | Some _,_ -> env in
    narrow (narrow env l r) r l
  | _ -> env

(* Expected types guide fresh construction only. They are never a shortcut
   claiming that an arbitrary expression already satisfies an annotation. *)
(* A module function as its callers see it: an ordinary function at exactly its
   annotated parameters and result. A rest parameter contributes its tuple's
   positions or its array's element. Generic ones are not reachable yet. *)
(* A leading `this: T` parameter is the receiver, not a position. *)
let module_type (g:Source.fn) =
  let receiver,params = match g.params with
    | ("this",t) :: rest -> t,rest
    | params -> top,params in
  let tys = List.map snd params in
  match g.rest,List.rev tys with
  | true,last::before ->
    (match Semantic.tuple_positions ~readonly:true last,Semantic.array_element ~readonly:true last with
     | Some positions,_ -> quantified_arrow ~receiver g.quantified (List.rev before @ positions) g.result
     | None,Some element -> variadic_arrow ~quantified:g.quantified ~receiver (List.rev before) element g.result
     | _ -> unsupported "rest parameter contract of a module function")
  | _ -> quantified_arrow ~receiver g.quantified tys g.result

(* One pass over a function. [offered] gives, for a named closure's creation,
   the further signatures its uses offer it; the pass reports them as
   [requests], and [infer_function] runs a second pass with them. *)
let infer_pass offered declarations module_functions (f:Source.fn) =
  let branch = branch_with declarations in
  (* A parameter the body assigns is a cell holding its argument, at its
     annotation. *)
  let env0 = List.map (fun (n,t) ->
    n,if List.exists (assigns n) f.body then cell t else Value (arms declarations t)) f.params in
  (* Unannotated immutable locals bound to a closure without binders or a rest
     parameter: where the closure is created, and its parameters' types. *)
  let closures = ref [] and requests = ref [] in
  (* Classes declared here: where the class value is created, its
     constructor's parameters, its instance type, and its methods, each a key
     and the named closure the instance holds under it. *)
  let classes = ref [] in
  (* A constructor's statements run before its instance is allocated. *)
  let rec allocated (body:expr) = match body.node with
    | Alloc fs -> Some fs
    | LetBody (_,_,_,rest) | SequenceBody (_,rest) | IfBody (_,_,rest,_) -> allocated rest
    | _ -> None in
  let named_closure n written (init:expr) = match written,init.node with
    | (None | Some (Atoms [Shape {calls=[_];fields=[];string_index=None;elements=None}])),Lambda (_,[],ps,_,false,_,_) ->
      closures := (n,(init.pos,List.map snd ps)) :: !closures
    | Some _,Ctor {node=Lambda (None,[],ps,[],false,Some instance,body);_} when allocated body <> None ->
      let fs = Option.get (allocated body) in
      let methods = List.filter_map (fun (key,(e:expr)) -> match e.node with
        | Id m when List.mem_assoc m !closures -> Some (key,m)
        | _ -> None) fs in
      classes := (n,(init.pos,List.map snd ps,instance,methods)) :: !classes
    | _ -> () in
  (* A named closure offered a signature binding more parameters than it does
     — a fixed signature taking more, or a variadic one whose fixed parameters
     cover its own — whose leading positions its own parameters take, is
     claimed at it beside its own, where it is created. The result is the
     action stating the offer, when there is one. *)
  let closure_offer n (offered:Semantic.signature) =
    let pos,own = List.assoc n !closures in
    let arity = List.length own in
    if offered.quantified=[] && offered.rest_pack=None
       && (match offered.variadic with
           | None -> List.length offered.params > arity
           | Some _ -> List.length offered.params >= arity)
       && List.for_all2 plausible_subtype
            (List.filteri (fun i _ -> i < arity) offered.params) own
    then Some (fun () -> requests := (pos,offered) :: !requests) else None in
  (* A class value expected at a construct signature: it is claimed there too,
     beside its own, when that signature's instance has a method taking more
     parameters than the class's own, or when the signature passes more
     actuals than the constructor binds (a resource class constructed with
     the request's parameters it ignores). The method's closure is then
     claimed at the longer parameters too, with its own receiver, the
     instance; the class value, at the signature's parameters where they are
     longer and its own otherwise, giving the expected instance. `new` and
     calls through the member discard the extra actuals; Lean checks the
     constructor's body at each construct signature (its first parameters)
     and the method's at each signature. *)
  let offer_class (pos,params,instance,methods) expected =
    match declared_head declarations [] expected with
    | Atoms [Ctors signatures] ->
      List.iter (fun (s:Semantic.signature) ->
        let member key = match (try Some (declared_head declarations []
            (field_type declarations [] s.result (Name key))) with Json.Error _ -> None) with
          | Some (Atoms [Shape {calls=[m];fields=[];indexes=[];elements=None}]) -> Some m
          | _ -> None in
        let widened = List.filter (fun (key,m) -> match member key with
          | Some offered -> (match closure_offer m {offered with receiver=instance} with
            | Some state -> state (); true
            | None -> false)
          | None -> false) methods in
        let arity = List.length params in
        let longer = s.variadic=None && s.rest_pack=None && List.length s.params > arity
          && List.for_all2 plausible_subtype (List.filteri (fun i _ -> i < arity) s.params) params in
        if widened <> [] || longer then
          requests := (pos,{quantified=[];receiver=top;params=if longer then s.params else params;
                            variadic=None;rest_pack=None;result=s.result}) :: !requests)
        (List.filter (fun (s:Semantic.signature) -> s.quantified=[]) signatures)
    | _ -> () in
  (* A name no parameter or local binds is one of the file's functions. *)
  let resolve env n = match List.assoc_opt n env with
    | Some b -> binding_type b
    | None -> (match List.assoc_opt n module_functions with
      | Some g -> Lazy.force g | None -> Json.fail ("unbound name " ^ n)) in
  let entries = ref [] and expressions = ref [] and instantiations = ref [] in
  (* A read of a generic module value that a call instantiates is claimed at
     that instance: Lean gives the value's slot the instances its calls name. *)
  let instances = ref [] in
  let instance_of ?declared (callee:expr) substitution =
    match callee.node with
    (* A generic method read from its object is claimed at the instance the
       call names: Lean puts the method's scheme below it. *)
    | Read _ | Index _ ->
      (match declared with
       | Some (Atoms [Shape ({calls=[signature];_} as shape)]) ->
         let instance = Inference.substitute substitution
           (Atoms [Shape {shape with calls=[{signature with quantified=[]}]}]) in
         instances := (callee.pos,instance) :: !instances
       | _ -> ())
    | Id n when not (List.mem_assoc n env0) && List.mem_assoc n module_functions ->
      (match Lazy.force (List.assoc n module_functions) with
       | Atoms [Shape ({calls=[signature];_} as shape)] ->
         let instance = Inference.substitute substitution
           (Atoms [Shape {shape with calls=[{signature with quantified=[]}]}]) in
         instances := (callee.pos,instance) :: !instances
       | Atoms [Ctors [signature]] ->
         let instance = Inference.substitute substitution
           (Atoms [Ctors [{signature with quantified=[]}]]) in
         instances := (callee.pos,instance) :: !instances
       | _ -> ())
    | _ -> () in
  (* A method's instance is its read's claim, not the call's. *)
  let method_read (callee:expr) = match callee.node with
    | Read _ | Index _ -> true | _ -> false in
  let arrows = ref [] in
  let entry env span = match Json.list span with
    | start::_ ->
      (* A field's contents are claimed where its object is still one record. *)
      let bindings = List.filter (fun (n,_) -> not (is_field n) ||
        (match List.assoc_opt (owner n) env with
         | Some (Value t) -> single_record declarations t (field_of n)
         | _ -> false)) env in
      entries := {start;bindings} :: !entries
    | [] -> Json.fail "empty source span" in
  (* The contract an assignment target is read and written at: a local's
     storage contract, or the type of the field or named index, whose read is
     also the target's claim. *)
  let rec target_contract env (target:expr) = match target.node with
    | Id n ->
      ignore (expr env target);
      (match lookup env n with
       | Storage (contract,_) -> contract
       | Value _ -> unsupported "assignment to immutable binding")
    | _ -> expr env target
  (* The type `e as const` gives its operand: a literal its own type, an
     array literal the readonly tuple of its elements', an object literal
     readonly fields of theirs; a name keeps its type. None for any other
     operand, which TypeScript refuses. *)
  and const_type env (e:expr) = match e.node with
    | Literal l -> Some (literal_type l)
    | Id n -> Some (resolve env n)
    | Cast ("const",None,e) -> const_type env e
    | ArrayLiteral es ->
      let elements = List.map (const_type env) es in
      if List.mem None elements then None
      else Some (array {required=List.filter_map Fun.id elements;optional_elements=[];rest=None;readonly=true})
    | Alloc fs ->
      let fields = List.map (fun (name,e) -> name,const_type env e) fs in
      if List.exists (fun (_,t) -> t = None) fields then None
      else Some (record (List.map (fun (name,t) ->
        {name=Name name;optional=false;read=Option.get t;write=None;host=false}) fields))
    | _ -> None
  and expr ?expected env e =
    let t = match e.node with
    | Id n ->
      Option.iter (fun expected -> Option.iter (fun c -> offer_class c expected)
        (List.assoc_opt n !classes)) expected;
      (* A named closure expected at a signature binding more parameters
         than it does is offered it, wherever it flows: an argument (as
         below), an annotated binding, a return, a field. *)
      (match expected with
       | Some (Atoms [Shape {calls=[o];fields=[];string_index=None;elements=None}])
         when List.mem_assoc n !closures && List.mem_assoc n env ->
         Option.iter (fun state -> state ()) (closure_offer n o)
       | _ -> ());
      resolve env n
    | Literal l -> literal_type l
    | Not e -> ignore (expr env e); bool
    | TypeofTest (_,_,e) -> ignore (expr env e); bool
    (* A string literal key is part of the test, not a claim site. *)
    | HasKey ({node=Literal (LString _);_},e) -> ignore (expr env e); bool
    | HasKey (k,e) -> ignore (expr env k); ignore (expr env e); bool
    (* A comparison is a Boolean; `+` with a string operand is a string;
       other arithmetic is of its operands' numeric family, bigint where the
       left one is all bigints, else number. *)
    | Arith (op,l,r) ->
      let left = expr env l in let right = expr env r in
      if relational op then bool else operation_result declarations op left right
    | Comma (a,b) -> ignore (expr env a); expr ?expected env b
    (* The target is read at its storage contract and written back: a local's
       contract, or the field's type. An increment adds one of that family;
       the old value is the contract's, the new one the operation's. *)
    | Update (op,target,rhs,post) ->
      let contract = target_contract env target in
      let right = match rhs with Some r -> expr env r | None -> contract in
      if post then contract else operation_result declarations op contract right
    (* The kept value is the target's, where the test keeps it: present for
       `??=`, `true` for `||=`, `false` for `&&=`; the other arm's is the right
       side's, written at the contract. *)
    | LogicalAssign (op,target,rhs) ->
      let contract = target_contract env target in
      let right = expr ~expected:contract env rhs in
      union (match op with
        | Nullish -> without_nullish contract | OrElse -> Atoms [True] | AndAlso -> Atoms [False]) right
    | NullishAssign (n,name_pos,rhs) ->
      let current = resolve env n in
      expressions := {pos=name_pos;type_=current;instantiation=None} :: !expressions;
      let contract = match lookup env n with
        | Storage (contract,_) -> contract
        | Value _ -> unsupported "assignment to immutable binding" in
      union (without_nullish current) (expr ~expected:contract env rhs)
    (* `typeof e` names one of eight shapes: a string. *)
    | Unary (Typeof,e) -> ignore (expr env e); Atoms [Str]
    | Unary (_,e) -> numeric_family declarations (expr env e)
    (* The right side is built at the tuple of the targets' contracts, as
       TypeScript types it from the targets; each target takes its
       position's read, or its default, at its storage contract. The value
       is the right side's. *)
    | ArrayAssign (targets,rest,rhs) ->
      let contract n = match lookup env n with
        | Storage (contract,_) -> contract
        | Value _ -> unsupported "assignment to immutable binding" in
      (* A literal's positions past the rest's index are the rest's: its
         tuple's positions or its array's element. *)
      let width = match rhs.node,rest with
        | ArrayLiteral es,_ -> List.length es
        | _,Some (i,_,_) -> i
        | _,None -> 1 + List.fold_left (fun m (i,_,_) -> max m i) (-1) targets in
      let required = List.init width (fun i -> match List.find_opt (fun (j,_,_) -> j=i) targets,rest with
        | Some (_,n,Some _),_ -> union (contract n) (Atoms [Undef])
        | Some (_,n,None),_ -> contract n
        | None,Some (start,_,n) when i >= start ->
          (match declared_head declarations [] (contract n) with
           | Atoms [Shape {elements=Some s;_}] ->
             (match List.nth_opt s.required (i-start) with
              | Some t -> t | None -> Option.value s.rest ~default:Semantic.top)
           | _ -> Semantic.top)
        | None,_ -> Semantic.top) in
      let actual = expr ~expected:(array {required;optional_elements=[];rest=None;readonly=false}) env rhs in
      List.iter (fun (_,n,d) -> Option.iter (fun d -> ignore (expr ~expected:(contract n) env d)) d) targets;
      (* The rest's fresh array is claimed at its local's contract where that
         is an array, which a fresh array meets, else at the positions it
         takes. *)
      Option.iter (fun (start,span,n) ->
        let claim = match Semantic.array_element (contract n),declared_head declarations [] actual with
          | Some _,_ -> contract n
          | None,Atoms [Shape {elements=Some s;_}] when s.optional_elements=[] && s.rest=None ->
            array {required=List.filteri (fun i _ -> i >= start) s.required;
                   optional_elements=[];rest=None;readonly=false}
          | _ -> unsupported "an array rest needs one tuple of required positions: the rest of an array of unknown length is a slice" in
        expressions := {pos=span;type_=claim;instantiation=None} :: !expressions) rest;
      actual
    | Equality (_,l,r) -> ignore (expr env l); ignore (expr env r); bool
    | Alloc fs ->
      let contract = match Option.bind expected (object_hint declarations []) with
        | Some shape -> Some shape
        | None -> Option.bind expected (fun t -> discriminated_record declarations t fs) in
      let fields = List.map (fun (name,e) ->
        let hint = Option.bind contract (fun s -> List.find_opt (fun (f:Semantic.field) -> f.name=Name name) s.fields) in
        (* A key the contract names is built at its member's type; any other
           at the index. *)
        let expected = match hint,contract with
          | Some (f:Semantic.field),_ -> Some f.read
          | None,Some shape -> Option.map (fun (i:Semantic.index_signature) -> i.value)
              (index_for shape (Name name))
          | None,_ -> None in
        let inferred=expr ?expected env e in
        (* A method's closure offered further signatures is held at its own
           claim: a construct signature offering them reads them there. *)
        let widened = match e.node with
          | Id m -> (match List.assoc_opt m !closures with
            | Some (pos,_) -> List.mem_assoc pos offered | None -> false)
          | _ -> false in
        (* A literal's type widens in a mutable field, as TypeScript's fresh
           literal types do; a name's or a read's declared type does not. *)
        let fresh = match e.node with Id _ | Read _ -> false | _ -> true in
        let t=if widened || (expected = None && not fresh) then inferred
          else Option.value expected ~default:(widen inferred) in
        {name=Name name;optional=false;read=t;write=Some t;host=false}) fs in
      (* Where the contract is a dictionary, or has optional fields, the
         literal is claimed with its exact keys: that own-key bound is what
         lets it meet an index, or an optional field it leaves out. *)
      (match contract with
       | Some {indexes=_::_;_} -> Atoms [Exact fields]
       | Some {fields=contract_fields;_}
         when List.exists (fun (f:Semantic.field) -> f.optional) contract_fields -> Atoms [Exact fields]
       | _ -> record fields)
    | ArrayLiteral es ->
      (* One array arm of the expected type is the literal's contract: an
         optional array parameter, `readonly T[] | undefined`, is its array. *)
      let arrays = match expected with
        | Some (Atoms atoms) -> List.filter_map (function Shape {elements=Some s;_} -> Some s | _ -> None) atoms
        | _ -> [] in
      let contract = match expected,arrays with
        | _,[s] -> Some s
        | _,_::_::_ when discriminated_array declarations arrays es <> None ->
          discriminated_array declarations arrays es
        | Some expected,_ ->
          Option.map (fun t -> {required=[];optional_elements=[];rest=Some t;readonly=true})
            (iterated_hint declarations expected)
        | None,_ -> None in
      let types = List.mapi (fun i e ->
        let expected = Option.bind contract (fun s -> match List.nth_opt (s.required @ s.optional_elements) i with
          | Some t -> Some t | None -> s.rest) in expr ?expected env e) es in
      (match contract with
        | Some s -> array s
        | None -> array {required=[];optional_elements=[];rest=Some (widen (combine types));readonly=false})
    (* A field a guard found holding less than its type is read at that. *)
    | Read (({node=Id name;_} as o),Name field) when List.mem_assoc (field_key name field) env ->
      ignore (expr env o); binding_type (List.assoc (field_key name field) env)
    | Read (e,n) -> field_type declarations [] (expr env e) n
    | Index (e,key) -> let receiver=expr env e in let key=expr env key in index_type declarations [] receiver key
    | IndexWrite (receiver,key,rhs) ->
      let t = expr env receiver in
      (match expr env key with
       | Atoms [StrLit k] -> refuse_growth declarations t (Name k)
       | _ -> ());
      expr env rhs
    | Write (receiver,field,rhs) -> refuse_growth declarations (expr env receiver) (Name field); expr env rhs
    | Assign (n,rhs) ->
      if not (List.mem_assoc n env) && List.mem_assoc n module_functions then
        unsupported ("assignment to module function " ^ n);
      (match lookup env n with
      | Storage (contract,_) -> expr ~expected:contract env rhs
      | Value _ -> unsupported "assignment to immutable binding")
    | Ctor {node=Lambda (None,[],ps,[],false,Some result,body);_} ->
      (* The constructor's body under its parameters; `new` passes it no
         receiver it reads, and runs it later, when a cell it captures holds
         what its contract admits. The class value's type is its construct
         signature. *)
      let inner = List.fold_left (fun env (n,t) -> extend env n (Value t)) (forget env) ps in
      ignore (expr ~expected:result inner body);
      (* A class offered construct signatures giving other instances is
         claimed at them too, beside its own; Lean checks the body at each. *)
      let own = {quantified=[];receiver=Semantic.top;params=List.map snd ps;variadic=None;rest_pack=None;result} in
      let extra = Option.value (List.assoc_opt e.pos offered) ~default:[] in
      Atoms [Ctors (own :: List.filter (fun s -> s <> own) (List.sort_uniq compare extra))]
    | Ctor _ -> unsupported "a class value is a constructor lambda with plain parameters"
    | New (callee,types,args) ->
      (* `new` may omit trailing actuals, as a call may: the machine binds
         `undefined` there, and Lean checks each omitted position admits it. *)
      let written (s:Semantic.signature) = List.filteri (fun i _ -> i < List.length args) s.params in
      (match declared_head declarations [] (expr env callee) with
       | Atoms [Ctors [signature]] when signature.quantified <> [] ->
         (* A generic class: its instance is the one the explicit type
            arguments name, or is inferred from the actuals, as a generic
            call's is. *)
         if List.length args > List.length signature.params then
           unsupported "no construct signature takes this many arguments";
         let substitution,result =
           if types <> [] then begin
             if List.length types <> List.length signature.quantified then
               unsupported "explicit type arguments must name every class type parameter";
             let substitution = List.map2 (fun (q:Semantic.quantifier) t -> q.identity,ValueArgument t)
               signature.quantified types in
             let instance = Inference.substitute_signature substitution {signature with quantified=[]} in
             List.iter2 (fun p a -> ignore (expr ~expected:p env a)) (written instance) args;
             substitution,instance.result
           end else
             let missing = List.length signature.params - List.length args in
             let inferred = Inference.infer ~expand:(expand_named declarations) ~receiver:Semantic.top ?expected signature
               (List.map (expr env) args @ List.init missing (fun _ -> Atoms [Undef])) in
             inferred.substitution,inferred.result in
         instance_of callee substitution;
         instantiations := (e.pos,List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
           substitution) :: !instantiations;
         result
       | Atoms [Ctors signatures] ->
         if types <> [] then unsupported "explicit type arguments to a class that takes none";
         let exact,short = List.partition (fun (s:Semantic.signature) ->
           List.length s.params = List.length args) (List.filter (fun (s:Semantic.signature) ->
             s.quantified = [] && List.length s.params >= List.length args) signatures) in
         (match exact @ short with
          | s :: _ ->
            List.iter2 (fun p a -> ignore (expr ~expected:p env a)) (written s) args;
            s.result
          | [] -> unsupported "no construct signature takes this many arguments")
       | _ -> unsupported "`new` needs a value with construct signatures")
    | Lambda (receiver,quantified,ps,defaults,rest,written,body) ->
      (* An ordinary function binds its own `this`, replacing an enclosing
         one; an arrow keeps the enclosing binding, as a capture. *)
      (* The body runs later, when any cell it captures holds whatever its
         contract admits. *)
      let env = forget env in
      let env = match receiver with
        | Some t -> List.remove_assoc "this" env @ ["this",Value t]
        | None -> env in
      let receiver = Option.value receiver ~default:Semantic.top in
      (* Executing defaults see only earlier bindings. A literal closure may
         capture later parameters; this is a proposal about its eventual body,
         not permission to invoke it during initialization. Lean independently
         schedules acyclic captures and rejects pending closure exposure. *)
      let inner = List.fold_left (fun env (i,(n,t)) ->
        Option.iter (fun d ->
          let scope = match d.node with
            | Lambda _ -> List.fold_left (fun scope (n,t) ->
                if List.mem_assoc n scope then scope else extend scope n (Value t)) env ps
            | _ -> env in
          try ignore (expr ~expected:t scope d) with
          | Json.Error message when String.starts_with ~prefix:"unbound name " message ->
            unsupported ("parameter default may only read initialized earlier parameters and captures: " ^ message))
          (List.assoc_opt i defaults);
        extend env n (Value t)) env (List.mapi (fun i p -> i,p) ps) in
      (* A closure literal without a result annotation expected at one
         signature taking at least its parameters has that signature's result
         as its contextual return type, as in TypeScript. *)
      let contextual = match written,expected with
        | None,Some t when quantified = [] ->
          (match (try declared_head declarations [] t with Json.Error _ -> t) with
           | Atoms [Shape {calls=[s];fields=[];indexes=[];elements=None}]
             when s.quantified=[] && s.rest_pack=None && s.variadic=None
                  && List.length s.params >= List.length ps -> Some s.result
           | _ -> None)
        | _ -> None in
      let body_type = expr ?expected:(if written <> None then written else contextual) inner body in
      (* Without a result annotation the result is the body's, widened as
         TypeScript widens an inferred return type, or the contextual return
         type where the body's fits it: a literal result the context asks for
         (`() => "hello"` at `() => "hello"`) is kept, and an async body's
         promise is the one the context names. It is a claim: Lean checks the
         body against it. *)
      let rec fits a b = plausible_subtype a b || match a,b with
        | Atoms [Named (i,xs)],Atoms [Named (j,ys)] ->
          i=j && List.length xs = List.length ys && List.for_all2 fits xs ys
        | _ -> false in
      let result = match written,contextual with
        | Some result,_ -> result
        | None,_ when quantified <> [] -> unsupported "a quantified closure needs its result annotation"
        | None,Some r when fits body_type r -> r
        | None,_ -> widen body_type in
      let params = List.mapi (fun i (_,t) ->
        if List.mem_assoc i defaults then union t (Atoms [Undef]) else t) ps in
      (* A tuple rest is one binding and several positions: the signature
         carries the elements, the body reads the tuple. An array rest is one
         binding and any number of positions, each at its element type. *)
      let params,element = if not rest then params,None else
        match List.rev params with
        | last :: fixed ->
          (match Semantic.tuple_positions ~readonly:true last,Semantic.array_element ~readonly:true last with
           | Some elements,_ -> List.rev fixed @ elements,None
           | None,Some element -> List.rev fixed,Some element
           | _ -> unsupported "a rest parameter needs a tuple of required positions or an array")
        | [] -> unsupported "a rest parameter needs a parameter" in
      let own = match element with
        | Some element -> variadic_arrow ~quantified ~receiver params element result
        | None -> quantified_arrow ~receiver quantified params result in
      (* A named closure passed where more parameters are offered is claimed
         at those signatures too, beside its own: calls through it discard
         the actuals past its parameters, and Lean checks its body at each. *)
      (* A closure literal expected at one signature binding more parameters
         than it does, whose leading positions its own take, is offered it
         where it is created, as a named one is offered by its uses. *)
      let from_context = match expected with
        | Some t -> (match (try declared_head declarations [] t with Json.Error _ -> t) with
          | Atoms [Shape {calls=[s];fields=[];string_index=None;elements=None}]
            when s.quantified=[] && s.rest_pack=None
                 && (match s.variadic with
                     | None -> List.length s.params > List.length ps
                     | Some _ -> List.length s.params >= List.length ps)
                 && List.for_all2 plausible_subtype
                      (List.filteri (fun i _ -> i < List.length ps) s.params) (List.map snd ps) -> [s]
          | _ -> [])
        | None -> [] in
      let offered_here = match List.assoc_opt e.pos offered, from_context with
        | None,[] -> None
        | extra,context -> Some (Option.value extra ~default:[] @ context) in
      let own = match offered_here, own with
        | Some extra, Atoms [Shape ({calls=[call];_} as shape)] when quantified=[] && element=None ->
          Atoms [Shape {shape with calls=call :: List.filter (fun s -> s <> call)
            (List.sort_uniq compare extra)}]
        | _ -> own in
      (* A contract advertising several signatures is implemented by this one
         closure. Propose that contract and state what the body claims under
         each signature; Lean checks every one of them. *)
      let implements (s:Semantic.signature) =
        s.quantified=[] && s.variadic=None && element=None && List.length s.params=List.length ps in
      (match expected with
       | Some (Atoms [Shape {calls=(_::_::_ as calls);fields=[];indexes=[];elements=None}] as contract)
         when quantified=[] && defaults=[] && List.for_all implements calls ->
         let row (s:Semantic.signature) =
           let saved = !expressions and saved_entries = !entries in
           expressions := []; entries := [];
           let env_row = List.fold_left2 (fun env (n,_) t -> extend env n (Value t))
             env ps s.params in
           ignore (expr ~expected:s.result env_row body);
           (* An entry environment replaces the context it is checked against,
              so a body's entries are stated per signature like its
              expressions. *)
           let claims = {row_expressions=List.rev !expressions;
                         row_entries=List.rev !entries} in
           expressions := saved; entries := saved_entries;
           claims in
         let rows = List.map row calls in
         arrows := (e.pos,rows) :: !arrows;
         contract
       | _ -> own)
    | Call _ | Invoke _ ->
      (* A method call types its callee, the read of the method, and so its
         object; the receiver Lean checks is that object. *)
      let callee,receiver,args,spreads,type_args = match e.node with
        | Call (c,r,a,s,t) -> c,r,a,s,t
        | Invoke (c,a,s,t) -> c,None,a,s,t
        | _ -> assert false in
      (* Explicit type arguments fix the callee's leading binders; the others
         are inferred from the receiver and the actuals. Lean checks that the
         claimed instance agrees with them. *)
      let infer_explicit ~receiver ?expected (signature:Semantic.signature) actuals =
        if List.length type_args > List.length signature.quantified then
          unsupported "more explicit type arguments than the callee has binders";
        let fixed = List.mapi (fun i t ->
          (List.nth signature.quantified i).identity,ValueArgument t) type_args in
        let partial = Inference.substitute_signature fixed
          {signature with quantified=List.filteri (fun i _ -> i >= List.length type_args)
             signature.quantified} in
        if partial.quantified = [] then fixed,partial.result
        else
          let inferred = Inference.infer ~expand:(expand_named declarations) ~receiver ?expected partial actuals in
          fixed @ inferred.substitution,inferred.result in
      let no_type_arguments () = if type_args <> [] then
        unsupported "explicit type arguments on a callee without binders" in
      let target = callee in
      let callee = declared_head declarations [] (expr env callee) in
      (* The receiver the call passes: the `.call` operand, the object a
         method is read from, or `undefined`. A scheme infers from it too. *)
      let receiver_type = match receiver, target.node with
        | Some r, _ -> expr env r
        | None, (Read (o,_) | Index (o,_)) when (match e.node with Invoke _ -> true | _ -> false) ->
          (match List.find_opt (fun (x:expression) -> x.pos = o.pos) !expressions with
           | Some x -> x.type_
           | None -> Atoms [Undef])
        | None, _ -> Atoms [Undef] in
      (* A closure passed where a callback is offered more parameters than it
         binds — a fixed signature taking more, or a variadic one whose fixed
         parameters cover them — is claimed at the offered signature: calls
         through it discard the actuals past its parameters, and Lean checks
         its body at the offered receiver, parameters and result. A literal is
         claimed there; a named closure, where it is created, beside its own
         signature, and only at a signature whose positions its parameters
         take: another is not one its body could be checked at. The result is
         the action stating the offer. *)
      let offer_to (arg:expr) param =
        let offered arity = match param with
          | Atoms [Shape {calls=[offered];fields=[];indexes=[];elements=None}] as t
              when offered.quantified=[] && offered.rest_pack=None
                && (match offered.variadic with
                    | None -> List.length offered.params > arity
                    | Some _ -> List.length offered.params >= arity) -> Some (t,offered)
          | _ -> None in
        match arg.node with
        | Lambda (_,[],ps,_,false,_,_) ->
          Option.map (fun (t,_) () -> instances := (arg.pos,t) :: !instances)
            (offered (List.length ps))
        | Id n when List.mem_assoc n !closures ->
          (match param with
           | Atoms [Shape {calls=[o];fields=[];indexes=[];elements=None}] -> closure_offer n o
           | _ -> None)
        (* A class value at a generic call's construct parameter, known only
           once the call's instance is: offered as where the parameter's type
           is expected. *)
        | Id n when List.mem_assoc n !classes ->
          Some (fun () -> offer_class (List.assoc n !classes) param)
        | _ -> None in
      let param_at (s:Semantic.signature) i = match List.nth_opt s.params i with
        | Some p -> Some p
        | None -> s.variadic in
      let offer ?(substitute=Fun.id) (s:Semantic.signature) =
        List.iteri (fun i arg -> Option.iter (fun p ->
          Option.iter (fun state -> state ()) (offer_to arg (substitute p))) (param_at s i)) args in
      (match callee with
       | Atoms [Shape {calls=[{quantified=[];variadic=Some element;params;result;_} as signature];_}] ->
         no_type_arguments ();
         offer signature;
         (* A variadic callee: the fixed actuals at its parameters, every
            further actual at its element type, and a spread at its own array
            contract, whose elements Lean checks against the element type. *)
         (* A shorter call omits trailing fixed positions, each admitting
            `undefined`, and writes nothing further. *)
         if List.length args < List.length params
            && not (List.for_all Semantic.admits_undefined
                      (List.filteri (fun i _ -> i >= List.length args) params))
         then unsupported "a variadic call omits a fixed parameter that does not admit undefined";
         List.iteri (fun i e ->
           if List.mem i spreads then ignore (expr env e)
           else match List.nth_opt params i with
             | Some p -> ignore (expr ~expected:p env e)
             | None -> ignore (expr ~expected:element env e)) args;
         result
       | Atoms [Shape {calls=[signature];_}]
           when signature.quantified<>[] && signature.rest_pack<>None ->
         (* A rest typed by a pack parameter: the actuals past the fixed ones,
            widened as TypeScript infers them, are its instance, a tuple; the
            other binders are inferred from the fixed actuals. Lean checks the
            instance against the bound, position by position. *)
         if spreads <> [] then unsupported "a spread into a pack parameter";
         if type_args <> [] then unsupported "explicit type arguments beside a pack parameter";
         let fixed = List.length signature.params in
         if List.length args < fixed then
           unsupported "a call omits a fixed parameter before a pack parameter";
         let actuals = List.map (expr env) args in
         let extras = List.filteri (fun i _ -> i >= fixed) actuals in
         let pack = Pack {required=List.map Semantic.widen extras;
           optional_elements=[];rest=None;readonly=false} in
         let solution = match signature.rest_pack with
           | Some (PackParameter p) when List.exists (fun (q:Semantic.quantifier) -> q.identity=p)
               signature.quantified -> [p,PackArgument pack]
           | _ -> unsupported "a pack rest that is not the method's own parameter" in
         let rest_quantified = List.filter (fun (q:Semantic.quantifier) ->
           not (List.mem_assoc q.identity solution)) signature.quantified in
         let partial = Inference.substitute_signature solution
           {signature with quantified=rest_quantified} in
         let substitution,result =
           if rest_quantified = [] then solution,partial.result
           else
             let inferred = Inference.infer ~expand:(expand_named declarations) ~receiver:receiver_type
               {partial with rest_pack=None}
               (List.filteri (fun i _ -> i < fixed) actuals) in
             solution @ inferred.substitution,inferred.result in
         instance_of ~declared:callee target substitution;
         offer ~substitute:(Inference.substitute substitution) signature;
         if not (method_read target) then
           instantiations := (e.pos,List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
             substitution) :: !instantiations;
         result
       | Atoms [Shape {calls=[signature];_}]
           when signature.quantified<>[] && signature.variadic<>None ->
         let actuals = List.concat (List.mapi (fun i arg ->
           let actual = expr env arg in
           if not (List.mem i spreads) then [actual]
           else if i < List.length signature.params then
             unsupported "a spread cannot fill fixed parameters of a variadic signature"
           else match Semantic.tuple_positions actual, Semantic.array_element actual with
             | Some positions,_ -> positions
             | None,Some element -> [union element (Atoms [Undef])]
             | _ -> unsupported "generic spread requires a mutable array or required tuple") args) in
         let missing = max 0 (List.length signature.params - List.length actuals) in
         let substitution,result = infer_explicit ~receiver:receiver_type signature
           (actuals @ List.init missing (fun _ -> Atoms [Undef])) in
         instance_of ~declared:callee target substitution;
         if not (method_read target) then
         instantiations := (e.pos,List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
           substitution) :: !instantiations;
         result
       | _ ->
      let spread = spreads <> [] in
      if spread && spreads <> [List.length args - 1] then
        unsupported "a spread into fixed parameters is the last argument";
      (* A call writes a prefix of the declared positions. The rest are omitted,
         which is admissible exactly when each of their contracts admits
         `undefined`; Lean checks that premise for itself. *)
      (* A spread argument stands for the required elements of its operand's
         tuple contract: the call writes those positions. *)
      (* Counting the positions must not state the operand's claim twice, so a
         name is read from the environment and anything else is typed once,
         here, and not again below. *)
      let spread_type = lazy (match List.rev args with
        | { node = Id name; _ } :: _ -> resolve env name
        | last :: _ -> expr env last
        | [] -> unsupported "a spread argument needs an operand") in
      let named_spread = match List.rev args with
        | { node = Id _; _ } :: _ -> true | _ -> false in
      let spread_positions () =
        match Semantic.tuple_positions (Lazy.force spread_type) with
        | Some elements -> List.length elements
        | None -> unsupported "a spread argument needs a tuple of required positions" in
      let written_positions =
        if not spread then List.length args
        else List.length args - 1 + spread_positions () in
      let callable (signature:Semantic.signature) =
        let declared = List.length signature.params and written = written_positions in
        (signature.variadic <> None && written >= declared)
        || (written <= declared
            && List.for_all Semantic.admits_undefined
                 (List.filteri (fun i _ -> i >= written) signature.params)) in
      (* Of several advertised signatures, the only one taking this many
         arguments is the one the call uses: its parameters guide the
         actuals' construction, as a single signature's do. *)
      let callee = match callee with
        | Atoms [Shape ({calls=(_::_::_ as calls);_} as shape)]
            when List.for_all (fun (s:Semantic.signature) -> s.quantified=[]) calls ->
          (match List.filter callable calls with
           | [s] -> Atoms [Shape {shape with calls=[s]}]
           | _ -> callee)
        | _ -> callee in
      (match callee with Atoms [Shape {calls=[signature];_}]
          when signature.quantified=[] && callable signature ->
        no_type_arguments ();
        (* A spread operand is checked at its own tuple contract; Lean reads
           the positions from that contract and checks each of them. *)
        List.iteri (fun i e ->
          if spread && i = List.length args - 1 then
            (if named_spread then ignore (expr env e))
          else let expected = match List.nth_opt signature.params i with
            | Some t -> t
            | None -> (match signature.variadic with
              | Some t -> t
              | None -> unsupported "call has too many arguments") in
            ignore (expr ~expected env e)) args;
        offer signature;
        signature.result
      | Atoms [Shape {calls=[signature];_}]
          when signature.quantified<>[] && callable signature ->
        (* Omission contributes undefined to inference, but no expression or
           claim is inserted into the source's argument list. An actual at a
           parameter mentioning no type parameter is built at it, as at a
           call without binders: TypeScript types it contextually, and a
           fresh literal leaving out an optional field is claimed at its
           exact keys there. Explicit type arguments naming every binder give
           every parameter its type, and each actual is built at it. *)
        let stated = if List.length type_args <> List.length signature.quantified then None
          else Some (List.map2 (fun (q:Semantic.quantifier) t -> q.identity,ValueArgument t)
            signature.quantified type_args) in
        (* An array literal at a parameter typed by a binder bounded by a
           tuple is built at that tuple, as TypeScript types it by the
           constraint: `exact<K extends [0, 1]>(x: K)` called with `[0, 1]`
           instantiates `K` at the tuple, not at `number[]`. *)
        let tuple_bound = function
          | Rigid r -> (match List.find_opt (fun (q:Semantic.quantifier) -> q.identity = r)
                          signature.quantified with
            | Some {bound=Some (ValueArgument (Atoms [Shape {elements=Some {rest=None;_};fields=[];
                calls=[];indexes=[]}] as t));_} -> Some t
            | _ -> None)
          | _ -> None in
        let dictionary_bound = function
          | Rigid r -> (match List.find_opt (fun (q:Semantic.quantifier) -> q.identity = r)
                          signature.quantified with
            | Some {bound=Some (ValueArgument t);_} ->
              (match object_hint declarations [] t with
               | Some {string_index=Some _;_} -> Some t
               | _ -> None)
            | _ -> None)
          | _ -> None in
        let actuals=List.mapi (fun i arg -> match param_at signature i,stated with
          | Some p,_ when not (Semantic.mentions_rigid p) -> expr ~expected:p env arg
          | Some p,Some solution -> expr ~expected:(Inference.substitute solution p) env arg
          | Some p,None when (match arg.node with ArrayLiteral _ -> true | _ -> false)
                              && tuple_bound p <> None ->
            expr ?expected:(tuple_bound p) env arg
          (* An object literal at a binder bounded by a union with one
             dictionary arm, `T extends Json`, is built at that arm, with
             its exact keys, as a record held in a variable could not be:
             TypeScript checks the fresh literal against the constraint. *)
          | Some p,None when (match arg.node with Alloc _ -> true | _ -> false)
                              && dictionary_bound p <> None ->
            expr ?expected:(dictionary_bound p) env arg
          | _ -> expr env arg) args @
          List.init (max 0 (List.length signature.params - List.length args)) (fun _ -> Atoms [Undef]) in
        let substitution,result = infer_explicit ~receiver:receiver_type ?expected signature actuals in
        instance_of ~declared:callee target substitution;
        offer ~substitute:(Inference.substitute substitution) signature;
        if not (method_read target) then
        instantiations := (e.pos,List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
          substitution) :: !instantiations;
        result
      (* Several advertised signatures on one value. The actuals are typed on
         their own — contextual construction inside such a call is not guided —
         and the signature whose domains they match is proposed. Lean selects
         the row it checks and re-checks every argument obligation. *)
      | Atoms [Shape {calls=(_::_::_ as calls);_}]
          when List.for_all (fun (s:Semantic.signature) -> s.quantified=[]) calls ->
        no_type_arguments ();
        let actuals = List.map (expr env) args in
        let usable = List.filter callable calls in
        (* A closure an offer would claim at the parameter matches it. *)
        let matching = List.filter (fun (s:Semantic.signature) ->
          List.for_all Fun.id (List.mapi (fun i (arg,t) -> match param_at s i with
            | Some p -> plausible_subtype t p || offer_to arg p <> None
            | None -> false) (List.combine args actuals))) usable in
        (match matching,usable with
         | s :: _,_ -> offer s; s.result
         | [],(first :: rest) when List.for_all (fun (s:Semantic.signature) ->
             s.result = first.result) rest -> first.result
         | _ -> unsupported "overloaded call needs a signature its arguments match")
      | _ -> unsupported "call requires a single arrow the arguments can call"))
    | Apply (callee,receiver,list) ->
      (* The list is typed at its own contract; Lean reads each element's
         type from it and checks the call against the target's signature. *)
      let callee = declared_head declarations [] (expr env callee) in
      ignore (expr env receiver);
      Option.iter (fun l -> ignore (expr env l)) list;
      (match callee with
       | Atoms [Shape {calls=[{quantified=[];result;_}];_}] -> result
       | _ -> unsupported ".apply requires a single arrow")
    | WithFields (fn,initial,ft,bag) ->
      ignore (expr ~expected:ft env fn); ignore (expr ~expected:bag env initial);
      (match ft,bag with
        | Atoms [Shape f],Atoms [Shape b] when f.fields=[] && f.elements=None && b.calls=[] && b.elements=None ->
          Atoms [Shape {b with calls=f.calls}]
        | _ -> unsupported "function field construction requires a callable and a record contract")
    | Bind (callee,receiver,args) ->
      let callee=declared_head declarations [] (expr env callee) in ignore (expr env receiver);
      (match callee with Atoms [Shape {calls=[signature];_}]
          when signature.quantified=[] && (signature.variadic<>None
            || List.length args<=List.length signature.params) ->
        (* The prefix takes the first positions; past a variadic signature's
           fixed ones, each is at its element contract. What is left is the
           bound function's signature, at any receiver. *)
        let rec prefix ps args = match ps,args with
          | rest,[] -> rest
          | p::ps,e::es -> ignore (expr ~expected:p env e); prefix ps es
          | [],e::es -> (match signature.variadic with
              | Some element -> ignore (expr ~expected:element env e); prefix [] es
              | None -> unsupported "bind argument prefix exceeds arity") in
        let rest = prefix signature.params args in
        (match signature.variadic with
         | Some element -> variadic_arrow rest element signature.result
         | None -> arrow rest signature.result)
      | _ -> unsupported "bind requires a single arrow and a valid argument prefix")
    | Conditional (c,a,b) -> ignore (expr env c);
      let left = expr ?expected (branch env c true) a in
      let right = expr ?expected (branch env c false) b in union left right
    | Coalesce (a,b) -> let left=expr env a in let right=expr ?expected env b in
      union (without_nullish left) right
    (* The body runs where the receiver is present, and reads it so; a
       nullish receiver gives `undefined`. An inner chain's receiver hides
       an outer one's. *)
    | Optional (r,b) -> let receiver=expr env r in
      let present=without_nullish receiver in
      let body=expr ?expected (List.remove_assoc chain_name env @ [chain_name,Value present]) b in
      if present = receiver then body else union (Atoms [Undef]) body
    (* The left operand's value where it decides, the right's elsewhere; the
       right operand runs where the left answered the other way. *)
    | Logical (conjunction,a,b) -> let left=expr env a in
      let right=expr ?expected (branch env a conjunction) b in
      union (truthy_slice (not conjunction) left) right
    (* The operand is built at its const type, which is the cast's. *)
    | Cast ("const",None,e) ->
      (match const_type env e with
       | Some t -> ignore (expr ~expected:t env e); t
       | None -> unsupported "`as const` on an operand other than a literal, an array or object literal, or a name")
    | Cast (kind,annot,e) -> let actual=expr ?expected:annot env e in
      (match kind,annot with
        | "nonNull",None -> without_nullish actual
        | "satisfies",Some _ -> actual
        | "as",Some target -> target
        | _ -> unsupported "cast form")
    | DoneBody -> Atoms [Undef]
    | ReturnBody body -> entry env e.pos; expr ?expected env body
    (* A throw has every type: the empty union. *)
    | ThrowBody body -> ignore (expr env body); Atoms []
    | SequenceBody (init,body) -> entry env e.pos; ignore (expr env init); expr ?expected env body
    | DestructBody (target,init,body) -> entry env e.pos;
      let env = bind env target (expr env init) None in
      expr ?expected env body
    | LetBody (name,written,init,body) -> entry env e.pos;
      let initial=expr ?expected:written env init in
      named_closure name written init;
      (* An unnamed slot holds a discarded statement value; no claim names it. *)
      if name = "" then expr ?expected env body
      else expr ?expected (extend env name (Value (Option.value written ~default:initial))) body
    | IfBody (result,c,a,b) -> entry env e.pos; ignore (expr env c);
      let left=expr ~expected:result (branch env c true) a in
      let right=expr ~expected:result (branch env c false) b in union left right in
    (* Block wrappers correspond to statement entries, not expression sites. *)
    (match e.node with
      | DoneBody | ReturnBody _ | ThrowBody _ | SequenceBody _ | LetBody _ | IfBody _ | DestructBody _ -> ()
      | _ -> expressions := {pos=e.pos;type_=t;
          instantiation=List.assoc_opt e.pos !instantiations} :: !expressions); t
  (* A pattern binding [target] to a value of [t], in pattern order: a
     property at its field's read, an element at its position's, a rest at the
     tuple of the positions from its index on, claimed at its span; a
     default, which sees the earlier bindings, replaces the read's undefined
     slice. *)
  and bind env target t default =
    (* The read's defined slice, through the declarations naming it. *)
    let rec present t = match t with
      | Union ts -> combine (List.map present ts)
      | Atoms xs -> combine (List.map (fun a -> match a,expand_named declarations (Atoms [a]) with
          | Named _,Some e when e <> Atoms [a] -> present e
          | _ -> restrict Undef false (Atoms [a])) xs)
      | t -> t in
    let t = match default with
      | None -> t
      | Some d ->
        let kept = present t in
        let expected = match kept with Atoms [] -> None | t -> Some t in
        union kept (expr ?expected env d) in
    match target with
    | PName (n,_) -> extend env n (Value t)
    | PObject props -> List.fold_left (fun env (f,target,d) ->
        bind env target (field_type declarations [] t (Name f)) d) env props
    | PArray (elems,rest) ->
      let env = List.fold_left (fun env (i,target,d) ->
        bind env target (index_type declarations [] t (number_literal (string_of_int i))) d) env elems in
      (match rest with
       | None -> env
       | Some (start,span,target) ->
         let remaining = match declared_head declarations [] t with
           | Atoms [Shape {elements=Some s;_}] when s.optional_elements=[] && s.rest=None ->
             List.filteri (fun i _ -> i >= start) s.required
           | _ -> unsupported "an array rest needs one tuple of required positions: the rest of an array of unknown length is a slice" in
         let rest_t = array {required=remaining;optional_elements=[];rest=None;readonly=false} in
         expressions := {pos=span;type_=rest_t;instantiation=None} :: !expressions;
         bind env target rest_t None)
  in
  (* Whether a list never completes normally: it ends in a jump, in an `if`
     whose arms both do, or in a block that does and, labeled, that no
     `break` leaves. *)
  let rec returns ss = match List.rev ss with
    | {statement=Return _ | Throw _ | Break _ | Continue;_}::_ -> true
    | {statement=If (_,a,b);_}::_ -> returns a && returns b
    (* A `try` completes only through a body or handler that does, and only
       if its `finally` does. *)
    | {statement=Try (body,handler,finalizer);_}::_ ->
      returns (Option.value finalizer ~default:[]) ||
      (returns body && (match handler with Some (_,h) -> returns h | None -> true))
    | {statement=Block (label,body);_}::_ ->
      returns body && (match label with Some l -> not (List.exists (leaves l) body) | None -> true)
    | _ -> false
  and leaves l s = match s.statement with
    | Break (Some l') -> l = l'
    | If (_,a,b) -> List.exists (leaves l) (a @ b)
    | While (_,body,update) -> List.exists (leaves l) (body @ update)
    | ForOf (_,_,_,body) | Block (_,body) -> List.exists (leaves l) body
    | Try (body,handler,finalizer) -> List.exists (leaves l)
      (body @ (match handler with Some (_,h) -> h | None -> []) @ Option.value finalizer ~default:[])
    | Declare _ | Destructure _ | Return _ | Effect _ | Throw _ | Break _ | Continue -> false in
  (* A step that may write a cell it does not name: a call, or a write. The
     cells are then known only by their contracts. Creating a closure runs
     nothing. *)
  let rec stirs (e:expr) = match e.node with
    | Call _ | Invoke _ | New _ | Apply _ | Bind _ | Write _ | IndexWrite _ | Assign _
    | Update _ | LogicalAssign _ | NullishAssign _ | ArrayAssign _ -> true
    | Lambda _ -> false
    | _ -> List.exists stirs (Source.children e) in
  let after e env = if stirs e then forget env else env in
  (* An assignment statement writes only the cell it names. *)
  let rec stirs_statement s = match s.statement with
    | Declare (_,bs) -> List.exists (fun (_,_,e) -> stirs e) bs
    | Destructure (target,d,init) -> List.exists stirs (init :: Option.to_list d @ pattern_defaults target)
    | Effect {node=Assign (_,rhs) | NullishAssign (_,_,rhs);_} -> stirs rhs
    | Return e | Effect e -> stirs e
    | If (c,a,b) -> stirs c || List.exists stirs_statement (a @ b)
    | While (c,body,update) -> stirs c || List.exists stirs_statement (body @ update)
    (* Each step of the loop calls `%Iterate%`. *)
    | ForOf _ -> true
    | Block (_,body) -> List.exists stirs_statement body
    | Throw e -> stirs e
    | Try (body,handler,finalizer) -> List.exists stirs_statement
      (body @ (match handler with Some (_,h) -> h | None -> []) @ Option.value finalizer ~default:[])
    | Break _ | Continue -> false in
  (* A point reached after any part of these statements ran: a cell they
     assign, or any cell where they may write one unseen, is known there by
     its contract. *)
  let havoc env body =
    if List.exists stirs_statement body then forget env
    else forget ~only:(fun n -> List.exists (assigns n) body) env in
  (* Where two arms meet, a cell holds what either left in it. *)
  let join before left right =
    List.filter_map (fun (n,b) -> match b,List.assoc_opt n left,List.assoc_opt n right with
      | Storage (contract,_),Some (Storage (_,l)),Some (Storage (_,r)) -> Some (n,holding contract (union l r))
      | _ when is_field n -> None
      | _ -> Some (n,b)) before
    (* A field's contents are known after both arms where each knows them. *)
    @ List.filter_map (fun (n,b) -> match b,List.assoc_opt n right with
      | Value l,Some (Value r) when is_field n && List.mem_assoc (owner n) before ->
        Some (n,Value (union l r))
      | _ -> None) left in
  (* What continues past a point from an arm: the bindings in scope before
     it, and the fields of their objects the arm knows. *)
  let continuing before env = List.filter (fun (n,_) ->
    List.mem_assoc n before || (is_field n && List.mem_assoc (owner n) before)) env in
  (* The environments a `break` of each label leaves with, gathered until the
     labeled block it leaves ends. *)
  let exits = Hashtbl.create 8 in
  (* Where several paths arrive, a value or a cell holds what it holds on
     one of them. With no arrival the point is unreachable, and [fallback]
     describes it. *)
  let merge before fallback arrivals =
    (* A path that knows a value of the empty type is never taken. *)
    let reachable = List.filter (fun env ->
      not (List.exists (fun (_,b) -> binding_type b = Atoms []) env)) arrivals in
    match reachable with
    | [] -> fallback
    | first::_ ->
      (* A field's contents are known where every path knows them; the
         first path names the candidates. *)
      let fields = List.filter (fun (n,_) -> is_field n && List.mem_assoc (owner n) before) first in
      List.filter_map (fun (n,b) ->
        let arriving = List.filter_map (List.assoc_opt n) reachable in
        match b,arriving with
        | _,_ when is_field n && List.length arriving < List.length reachable -> None
        | _,[] -> Some (n,b)
        | Value _,_ -> Some (n,Value (combine (List.map binding_type arriving)))
        | Storage (contract,_),_ -> Some (n,holding contract (combine (List.map binding_type arriving))))
        (List.filter (fun (n,_) -> not (is_field n)) before @ fields) in
  (* The unlabeled `break` and `continue` environments of each enclosing
     loop, innermost first. *)
  let loops = ref [] in
  (* Run [f] for what it computes, leaving no claim, request or exit behind:
     a loop head is found by running its body from candidate heads. *)
  let trial f =
    let saved = (!closures,!requests,!classes,!entries,!expressions,!instantiations,
                 !instances,!arrows,!loops) in
    let saved_exits = Hashtbl.fold (fun k v acc -> (k,v) :: acc) exits [] in
    let result = try Some (f ()) with Json.Error _ -> None in
    let (a,b,c,d,e,g,h,i,j) = saved in
    closures := a; requests := b; classes := c; entries := d; expressions := e;
    instantiations := g; instances := h; arrows := i; loops := j;
    Hashtbl.reset exits;
    List.iter (fun (k,v) -> Hashtbl.add exits k v) saved_exits;
    result in
  (* The statements following each statement of a block, by its span. *)
  let following = Hashtbl.create 64 in
  let rec mentions n (e:expr) =
    (match e.node with Id m -> m = n | _ -> false) || List.exists (mentions n) (Source.children e) in
  let rec stmt_mentions n (s:stmt) = match s.statement with
    | Declare (_,bs) -> List.exists (fun (_,_,e) -> mentions n e) bs
    | Destructure (p,d,e) -> List.exists (mentions n) (e :: Option.to_list d @ pattern_defaults p)
    | Return e | Effect e | Throw e -> mentions n e
    | If (c,a,b) -> mentions n c || List.exists (stmt_mentions n) (a @ b)
    | While (c,b,u) -> mentions n c || List.exists (stmt_mentions n) (b @ u)
    | Block (_,b) -> List.exists (stmt_mentions n) b
    | ForOf (_,_,e,b) -> mentions n e || List.exists (stmt_mentions n) b
    | Try (b,h,f) -> List.exists (stmt_mentions n)
      (b @ (match h with Some (_,h) -> h | None -> []) @ Option.value f ~default:[])
    | Break _ | Continue -> false in
  (* The first use of an unannotated constant's fresh array, in the
     statements after its declaration: where it is the whole value expected
     at a type (an annotated constant's initializer, a returned value, an
     argument of a call to a function of one plain signature), that type;
     any other first use, none. `None` where it is not used. *)
  let first_use env n rest =
    let rec sink expected (e:expr) = match e.node with
      | Id m when m = n -> Some expected
      | Call ({node=Id g;_},None,args,[],[]) when g <> n ->
        let params = match (try declared_head declarations [] (resolve env g) with Json.Error _ -> Atoms []) with
          | Atoms [Shape {calls=[s];_}] when s.quantified=[] && s.variadic=None && s.rest_pack=None -> s.params
          | _ -> [] in
        List.find_map Fun.id (List.mapi (fun i a -> sink (List.nth_opt params i) a) args)
      | _ -> List.find_map (sink None) (Source.children e) in
    let at (s:stmt) = match s.statement with
      | Declare (_,bs) -> List.find_map (fun (_,written,e) -> sink written e) bs
      | Return e -> sink (Some f.result) e
      | Effect e -> sink None e
      | _ -> if stmt_mentions n s then Some None else None in
    Option.join (List.find_map at rest) in
  let rec statements env ss =
    let rec record = function [] -> () | s :: rest -> Hashtbl.replace following s.span rest; record rest in
    record ss;
    List.fold_left (fun env s ->
    let env = match s.statement with
      | While (c,body,update) -> loop_fix env c body update
      | ForOf _ -> forget env
      | _ -> env in
    (* A block has no entry of its own: its first statement's is. *)
    (match s.statement with Block _ -> () | _ -> entry env s.span);
    match s.statement with
    | Declare (mutable_,bs) -> List.fold_left (fun env (n,written,init) ->
      (* An unannotated constant's fresh array is built at the array type its
         first use expects it at, where that use is one (SKJS commits such a
         literal there; TypeScript widens it at the declaration, and refuses
         the use when that differs). A proposal: Lean checks the elements
         against it and every use against the binding. *)
      let committed = match mutable_,written,init.node with
        | false,None,ArrayLiteral (_::_) ->
          (match first_use env n (Option.value (Hashtbl.find_opt following s.span) ~default:[]) with
           | Some t -> (match (try declared_head declarations [] t with Json.Error _ -> t) with
             | Atoms atoms when atoms <> [] && List.for_all (function
                 | Shape {elements=Some _;_} -> true | _ -> false) atoms -> Some t
             | _ -> None)
           | None -> None)
        | _ -> None in
      let initial = expr ?expected:(if committed <> None then committed else written) env init in
      if not mutable_ then named_closure n written init;
      let binding = match mutable_,written with
        (* TypeScript's declared type for an unannotated `let`: its
           initializer's type, widened. Lean checks the initializer and every
           assignment against it. `null`, `undefined` and `[]` give an
           evolving type (implicit `any`) there, which is no contract. *)
        | true,None ->
          (match init.node with
           | Literal (LNull | LUndefined) | ArrayLiteral [] ->
             unsupported "an unannotated `let` initialized with null, undefined or [] has no storage contract"
           | _ -> cell (widen initial))
        | true,Some contract -> cell contract
        (* A class's annotation is its own construct signature, which the
           parser writes; the class value's claim may offer more. *)
        | false,Some _ when (match init.node with Ctor _ -> true | _ -> false) -> Value initial
        (* A closure offered further signatures holds them beside its
           annotation's: the binding is the closure, claimed at all of them,
           which Lean checks against the annotation. *)
        | false,Some _ when List.mem_assoc init.pos offered -> Value initial
        | false,Some contract -> Value (arms declarations contract)
        | false,None -> Value initial in
      extend (after init env) n binding) env bs
    (* The initializer, then each binding in pattern order: a property at its
       field's read, an element at its position's, a rest at the tuple of the
       positions from its index on, claimed at its span; a default, which
       sees the earlier bindings, replaces the read's undefined slice. *)
    | Destructure (target,default,init) ->
      let env = bind env target (expr env init) default in
      if stirs_statement s then forget env else env
    | Return e -> ignore (expr ~expected:f.result env e); env
    (* An assignment statement leaves the cell holding the value written;
       `n ??= rhs`, the value it yields. *)
    | Effect ({node=Assign (n,rhs) | NullishAssign (n,_,rhs);_} as e) ->
      let t = expr env e in
      (match lookup env n with
       | Storage _ -> assign (after rhs env) n t
       | Value _ -> env)
    | Effect e -> ignore (expr env e); after e env
    | If (c,a,b) -> ignore (expr env c);
      let env = after c env in
      let left = statements (branch env c true) a and right = statements (branch env c false) b in
      (* The rest of the block runs only where an arm that always returns was
         not taken; where both may complete, a cell holds what either left. *)
      (match returns a,returns b with
       | true,false -> continuing env right
       | false,true -> continuing env left
       | _ -> join env left right)
    (* The update runs where the body ends or continues: from the head's
       knowledge, which already forgets what the body assigns. *)
    | While (c,body,update) -> ignore (expr env c);
      let _,breaks = loop_pass env c body update in
      (* The loop is left from its head or by a `break`. *)
      merge env env (env :: breaks)
    (* A block's bindings end with it. A labeled one is also left by each
       `break` of its label, with what that path knew. *)
    | Block (label,body) ->
      let inner = statements env body in
      let completes = if returns body then [] else [inner] in
      (match label with
       | Some l ->
         let breaks = Hashtbl.find_all exits l in
         List.iter (fun _ -> Hashtbl.remove exits l) breaks;
         merge env (havoc env body) (completes @ breaks)
       | None -> merge env env completes)
    | ForOf (name,name_pos,iterable,body) ->
      (* The loop is the call of `%Iterate%` on the iterable, claimed at the
         statement with its instance; the element, at the name it binds. *)
      let actual = expr env iterable in
      let signature = match declared_head declarations [] (resolve env "%Iterate%") with
        | Atoms [Shape {calls=[signature];_}] when signature.quantified<>[] -> signature
        | _ -> unsupported "a for...of loop needs the %Iterate% intrinsic" in
      let inferred = Inference.infer ~receiver:(Atoms [Undef]) signature [actual] in
      let element = match inferred.substitution with
        | [_,ValueArgument t] -> t
        | _ -> unsupported "%Iterate% has one value binder" in
      expressions := {pos=s.span;type_=inferred.result;
        instantiation=Some (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
          inferred.substitution)} :: !expressions;
      expressions := {pos=name_pos;type_=element;instantiation=None} :: !expressions;
      (* Its `break`s and `continue`s are its own. *)
      loops := (ref [],ref []) :: !loops;
      ignore (statements (extend env name (Value element)) body);
      loops := List.tl !loops; env
    | Throw e -> ignore (expr env e); env
    | Try (body,handler,finalizer) ->
      let local after = List.filter (fun (n,_) -> List.mem_assoc n env) after in
      let completed = statements env body in
      (* A throw leaves the body from any point of it, after any part of it
         ran: the handler knows each cell by its contract, and what was
         thrown, which may be anything, at `unknown`. *)
      let completed = match handler with
        | None -> local completed
        | Some (param,handled) ->
          let caught = forget env in
          let caught = match param with
            | Some (name,_) -> extend caught name (Value Semantic.top)
            | None -> caught in
          let recovered = statements caught handled in
          (match returns body,returns handled with
           | true,false -> local recovered
           | false,true -> local completed
           | _ -> join env (local completed) (local recovered)) in
      (match finalizer with
       | None -> completed
       (* The `finally` block runs after a completion, a `return` or a throw,
          from any point: it knows each cell by its contract. *)
       | Some finalizer -> local (statements (forget env) finalizer))
    | Break (Some l) -> Hashtbl.add exits l env; env
    | Break None -> (match !loops with (breaks,_) :: _ -> breaks := env :: !breaks | [] -> ()); env
    | Continue -> (match !loops with (_,continues) :: _ -> continues := env :: !continues | [] -> ()); env)
    env ss
  (* One pass over a loop from the head [head]: the body where the
     condition held, the update where the body ends or continues, and what
     the update leaves for the head, with the environments its `break`s
     leave with. *)
  and loop_pass head c body update =
    let breaks = ref [] and continues = ref [] in
    loops := (breaks,continues) :: !loops;
    let inner = statements (branch head c true) body in
    loops := List.tl !loops;
    let ends = (if returns body then [] else [inner]) @ !continues in
    (* Where no end is reachable, neither is the update, nor the head again
       from it: the update is then claimed from the head, as before. *)
    let reachable = List.filter (fun env ->
      not (List.exists (fun (_,b) -> binding_type b = Atoms []) env)) ends in
    let at_update = if reachable = [] then head else merge head head reachable in
    let back = statements at_update update in
    (if reachable = [] then None else Some back),!breaks
  (* A loop's head: what its cells hold on entry and on every return from
     its body, found by running the body from the entry until the head is
     stable. A condition or body that may write a cell unseen, or no stable
     head within a few rounds, gives the head each assigned cell's contract,
     as before. The head is a claim: Lean checks the entry and back edges. *)
  and loop_fix env c body update =
    if stirs c || List.exists stirs_statement (body @ update) then forget env else
    let fallback = havoc env (body @ update) in
    let rec go head rounds =
      if rounds = 0 then fallback else
      match Option.map fst (trial (fun () -> loop_pass head c body update)) with
      | None -> fallback
      | Some None -> env
      | Some (Some back) ->
        let next = merge env fallback [env; back] in
        if next = head then head else go next (rounds - 1) in
    go env 5 in
  ignore (statements env0 f.body);
  (* An expression the lowering reaches on two paths (the fields the arms of a
     constructor's last `if` share) is claimed once when both claims agree;
     two different claims at one span stay, and Lean refuses them. *)
  let seen = Hashtbl.create 64 in
  let expressions = List.filter (fun x ->
    not (Hashtbl.mem seen x) && (Hashtbl.add seen x (); true)) (List.rev !expressions) in
  let expressions = List.map (fun (x:expression) -> match List.assoc_opt x.pos !instances with
    | Some instance -> {x with type_=instance}
    | None -> x) expressions in
  {source=f;entries=List.rev !entries;expressions;arrows=List.rev !arrows},!requests
(* A named closure's claim is fixed where it is created, before the calls that
   offer it more parameters are reached: a first pass finds those offers, and
   the second states them at the creation. *)
let infer_function declarations module_functions (f:Source.fn) =
  rigid_bounds := List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
    | Some (ValueArgument b) when not (Semantic.mentions_rigid b) -> Some (q.identity,b)
    | _ -> None) f.quantified;
  let claim,requests = infer_pass [] declarations module_functions f in
  if requests = [] then claim else
  let offered = List.map (fun pos -> pos,List.filter_map (fun (p,s) ->
    if p = pos then Some s else None) requests)
    (List.sort_uniq compare (List.map fst requests)) in
  fst (infer_pass offered declarations module_functions f)
let infer program =
  let module_functions = List.map (fun (g:Source.fn) -> g.name,lazy (module_type g))
    program.Source.functions
    @ List.map (fun (name,t) -> name,lazy t) program.Source.values in
  let infer_with = infer_function program.Source.declarations in
  let init = match program.Source.init with
    | [] -> None
    | body -> Some (infer_with module_functions
        {quantified=program.Source.init_quantified;name="";name_pos=Json.Null;params=[];rest=false;
         result=Atoms [Undef];body}) in
  (* A function reads a module constant at its annotation or, without one, at
     the initialization unit's claim for its initializer; that unit is what
     establishes it. *)
  (* A generic class's constructor is quantified over the class's binders:
     a unit reading it names its instance, as for a generic function. *)
  let quantify_class t = match t with
    | Atoms [Ctors [signature]] when program.Source.init_quantified <> [] ->
      let mentioned = List.filter (fun (q:Semantic.quantifier) ->
        let rec mentions = function
          | Rigid r -> r = q.identity
          | Union ts -> List.exists mentions ts
          | Meet (t,ts) -> List.exists mentions (t::ts)
          | Atoms atoms -> List.exists (function
              | Named (_,args) -> List.exists mentions args
              | _ -> false) atoms in
        List.exists mentions (signature.result :: signature.params)) program.Source.init_quantified in
      if mentioned = [] then t else Atoms [Ctors [{signature with quantified=mentioned}]]
    | t -> t in
  let module_constants = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) -> List.map (fun (n,written,(e:expr)) -> n,lazy (match written with
        | Some t -> quantify_class t
        | None ->
          match Option.bind init (fun c -> List.find_opt (fun (x:expression) -> x.pos = e.pos) c.expressions) with
          | Some x -> x.type_
          | None -> unsupported ("module constant " ^ n ^ " has no claimed initializer")))
      bindings
    | _ -> []) program.Source.init in
  {program;init;functions=List.map (infer_with (module_functions @ module_constants))
    program.Source.functions}
