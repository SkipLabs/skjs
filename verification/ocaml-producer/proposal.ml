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
(* A run that explains a failed search (`producer --explain`): each form
   whose failure has a known cause is recorded at its source span with its
   reason, and the one at the failed obligation names it. An ordinary run
   proposes these forms as any other, and Lean decides; an explanation only
   names why it found no derivation. *)
let explaining = ref false
let explanations : (Json.t * string) list ref = ref []
let explain pos s = if !explaining then explanations := (pos,s) :: !explanations
let combine = List.fold_left union (Atoms [])
(* A proposal heuristic for choosing an advertised arrow. It does not
   establish subtyping: Lean checks the selected call and its arguments. *)
let rec plausible_subtype actual expected =
  if actual=expected then true else match actual,expected with
  | Atoms _,Atoms [Top] -> true
  | Atoms xs,Atoms ys -> List.for_all (fun x -> List.exists (fun y ->
      x=y || match x,y with
      | NumLit _,Num | StrLit _,Str | BigintLit _,Bigint -> true
      | Shape a,Shape b when a.fields=b.fields && a.indexes=b.indexes && a.elements=b.elements ->
        List.for_all (fun (q:Semantic.signature) -> List.exists (fun (p:Semantic.signature) ->
          (p.call_effect=q.call_effect || q.call_effect=Unrestricted) &&
          {p with call_effect=q.call_effect}=q) a.calls) b.calls
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
             && (inherited.indexes=[] || local.indexes=[] || inherited.indexes=local.indexes) ->
        (* A member both declare, as a derived class's override: the
           declaration's own is the hint; Lean's meaning is both, and a value
           must meet each. *)
        let own_names = List.map (fun (f:Semantic.field) -> f.name) local.fields in
        Atoms [Shape {local with fields=local.fields @ List.filter
          (fun (f:Semantic.field) -> not (List.mem f.name own_names)) inherited.fields;
          indexes=(if local.indexes=[] then inherited.indexes else local.indexes)}]
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
       read through its equation (`Serializable<Todo>`); otherwise it stays
       their intersection, including over type parameters. Keeping only the
       principal operand would lose receiver restrictions when the equation
       is later instantiated. Lean fills the claim's meet row independently. *)
    let meet t ts =
      let expand t = match t with
        | Atoms [Named (named,named_args)] when not (List.mem named (id::seen)) ->
          (try instantiate (id::seen) named named_args with Json.Error _ -> t)
        | t -> t in
      match List.fold_left (fun acc part -> Option.bind acc (fun a -> meet_objects a (expand part)))
              (Some (expand t)) ts with
      | Some merged -> merged
      | None -> Meet (t,ts) in
    let body = Inference.substitute ~meet solution d.expression in
    (* A base named through an alias of another declaration is that
       declaration, instantiated: its members are inherited by structure. *)
    let rec base_of seen t = match t with
      | Atoms [Named (named,named_args)] ->
        if List.mem named seen then unsupported "cyclic inheritance";
        base_of (named::seen) (instantiate seen named named_args)
      | t -> t in
    List.fold_left (fun own base ->
      match Inference.substitute ~meet solution base with
      | Atoms [Named _] as named -> merge (base_of (id::seen) named) own
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
(* The first operand of an intersection a read succeeds on; where none has
   it, the principal operand's reason. *)
let first_part read parts =
  match List.find_map (fun t -> try Some (read t) with Json.Error _ -> None) parts with
  | Some t -> t
  | None -> (match parts with
    | principal :: _ -> read principal
    | [] -> unsupported "read on an empty intersection")
(* `ArrayProto`, the declaration of `Array.prototype`'s members, by identity. *)
(* The key an object keeps its prototype under: no source property spells it. *)
let proto_key = "[[proto]]"
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
            | None -> (match List.find_opt (fun (f:Semantic.field) -> f.name=Name proto_key) shape.fields with
              (* A member the object holds on its prototype. *)
              | Some p -> field_type declarations seen p.read name
              | None -> unsupported ("missing field " ^ key_text name))))
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
        let id = Option.get (primitive_prototype atom) in
        (* The parser reads a wrapper prototype where TypeScript types a
           member's receiver as that primitive. *)
        if not (List.exists (fun (d:Source.declaration) -> d.id=id) declarations) then begin
          let kind = String.sub id 5 (String.index id '-' - 5) in
          unsupported ("a member read on a " ^ kind ^ " where the type TypeScript gives the receiver holds no " ^
            kind ^ ": the producer and TypeScript disagree on the receiver")
        end;
        field_type declarations seen (Atoms [Named (id,[])]) name
      | _ -> unsupported "field read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> field_type declarations seen t name) ts)
  (* A value of an intersection is one of each operand: read as the first
     operand that has the field, a hint Lean checks. *)
  | Meet (t,ts) -> first_part (fun t -> field_type declarations seen t name) (t::ts)
  | Rigid r -> (match rigid_bound r with
    | Some b -> field_type declarations seen b name
    | None -> unsupported "field read on rigid parameter")
(* A key-adding write (DESIGN.md, "A key-adding write"): a write of a key
   some plain-object arm of the receiver's type states neither as a required
   field nor as a method may add the key. Lean lowers it on an owned local as
   the copy of the object with the key, and refuses it on any other object;
   the producer proposes the grown type and the new field's contract. *)
let plain_arms declarations t =
  match (try declared_head declarations [] t with Json.Error _ -> t) with
  | Atoms (_::_ as atoms) when List.for_all (function
      | Shape {elements=None;calls=[];_} | Exact _ -> true | _ -> false) atoms -> Some atoms
  | _ -> None
let arm_fields = function Shape {fields;_} | Exact fields -> fields | _ -> []
let may_lack declarations t name =
  match plain_arms declarations t with
  | Some atoms ->
    List.exists (fun a -> not (List.exists (fun (f:Semantic.field) ->
      f.name=name && not f.optional) (arm_fields a))) atoms
    && not (List.exists (fun a -> List.exists (fun (f:Semantic.field) ->
      f.name=name && f.optional && f.write=None) (arm_fields a)) atoms)
  | None -> false
(* The contract the new field is added at: an optional field's own where an
   arm states one, else the value's type, a literal's widened as a fresh
   literal's field is. *)
let added_contract declarations t name (rhs:Source.expr) value =
  let declared = Option.bind (plain_arms declarations t) (List.find_map (fun a ->
    List.find_map (fun (f:Semantic.field) ->
      if f.name=name && f.optional then f.write else None) (arm_fields a))) in
  (* A binding's or a read's type is the contract as it stands, without the
     exact keys a fresh literal has, as TypeScript's declared type is. *)
  let loosen = function
    | Atoms atoms -> Atoms (List.map (function
        | Exact fields -> Shape {fields;indexes=[];calls=[];elements=None}
        | a -> a) atoms)
    | t -> t in
  match declared,rhs.node with
  | Some c,_ -> c
  | None,(Id _ | Read _) -> loosen value
  | None,_ -> loosen (widen value)
(* The object's type once the key is added at [c]: every arm owns it. *)
let grown declarations t name c =
  match plain_arms declarations t with
  | Some atoms ->
    let field = {name;optional=false;read=c;write=Some c;host=false} in
    let add fs = List.filter (fun (f:Semantic.field) -> f.name<>name) fs @ [field] in
    Atoms (List.map (function
      | Shape s -> Shape {s with fields=add s.fields}
      | Exact fs -> Exact (add fs)
      | a -> a) atoms)
  | None -> t
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
(* The first arm of an iterated value that is not an array, named for the
   refusal where the loop or spread steps `%Iterate%` or copies an array:
   the parser picks the intrinsic of a string, a `Set`, a `Map` or a host
   collection iterator only where TypeScript types the whole iterable as one
   such kind, and lowers a program's iterable, or a union with one, to the
   iterator protocol (PROGRAM-TYPING.md "Loops and spreads over iterables").
   A type parameter is left to Lean. *)
let rec non_array_arm declarations seen t = match t with
  | Rigid _ -> None
  | Union ts -> List.find_map (non_array_arm declarations seen) ts
  | Meet (t,_) -> non_array_arm declarations seen t
  | Atoms atoms -> List.find_map (function
      | Shape {elements=Some _;_} -> None
      | Named (id,args) when not (List.mem id seen) ->
        (match definition declarations id args with
         | body -> non_array_arm declarations (id::seen) body
         | exception Json.Error _ -> None)
      | Named _ -> None
      | Str | StrLit _ -> Some "a string"
      (* An object naming a symbol-keyed member, as `[Symbol.iterator]` is:
         an iterable to TypeScript. Any other is left to Lean, which finds
         no iterator, as TypeScript does not. *)
      | Shape {fields;_} when List.exists (fun (f:Semantic.field) ->
            match f.name with Key _ -> true | Name _ -> false) fields ->
        Some "an object that is not an array (a Set, a Map, an iterator or another iterable)"
      | _ -> None) atoms
let iteration_reason =
  "the iteration of one host kind is stated (%Iterate:K%), picked where the whole iterable is of that \
   kind: a union of host kinds has no one intrinsic (an iterable the program defines, or a union with \
   one, runs the iterator protocol)"
(* The elements a slice rest from index [start] collects from an array of
   type [t]: every arm's positions from there on, an optional one with
   `undefined`, and its rest element. `%RestFrom:k%` is claimed at it. *)
let slice_element declarations start t =
  let rec arms seen t = match t with
    | Union ts -> List.concat_map (arms seen) ts
    | Atoms atoms -> List.concat_map (function
        | Named (id,_) as a when not (List.mem id seen) ->
          arms (id::seen) (declared_head declarations [] (Atoms [a]))
        | a -> [a]) atoms
    | Rigid _ | Meet _ -> unsupported "a slice rest over a type parameter or an intersection" in
  combine (List.concat_map (function
    | Shape {elements=Some s;_} ->
      let r = List.length s.required in
      List.filteri (fun i _ -> i >= start) s.required
      @ List.filteri (fun i _ -> i + r >= start) (List.map (fun t -> union t (Atoms [Undef])) s.optional_elements)
      @ Option.to_list s.rest
    | _ -> unsupported "an array pattern over a value that may not be an array: it would step that value's own \
        iterator, which is not modeled; only an array's positions are read") (arms [] t))
(* A key of several string or number singletons (NaN, which no equality
   test finds, is none): Lean reads, per singleton, the member its key names. *)
let key_singletons = function
  | Atoms (_::_::_ as ks) when List.for_all (function
      | StrLit _ -> true
      | NumLit bits -> not (Float.is_nan (Int64.float_of_bits bits)) && number_key bits <> None
      | _ -> false) ks -> Some ks
  | _ -> None
let rec index_type declarations seen receiver key =
  match key_singletons key with
  | Some ks -> combine (List.map (fun k -> index_type declarations seen receiver (Atoms [k])) ks)
  | None -> match receiver with
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
let discriminated_record declarations expected (members:(key * expr) list) =
  let admits (s:shape) =
    List.for_all (fun (name,e) ->
      match List.find_opt (fun (f:field) -> f.name = name && not f.host) s.fields with
      | Some f -> literal_admitted declarations e f.read
      | None -> index_for s name <> None) members
    && List.for_all (fun (f:field) -> f.optional || f.host
      || List.mem_assoc f.name members) s.fields in
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
let rec restrict ?declarations singleton equal t = match t with
  | Atoms xs -> ground (List.filter (fun atom ->
      let rec known atom = match atom,singleton with
        | Nul,Nul | Undef,Undef | True,True | False,False -> Some true
        (* Number::equal: NaN equals nothing, and the zeros each other. *)
        | NumLit a,NumLit b -> Some (Int64.float_of_bits a = Int64.float_of_bits b)
        | StrLit a,StrLit b -> Some (a=b)
        | BigintLit a,BigintLit b -> Some (a=b)
        | Num,NumLit _ | Str,StrLit _ | Bigint,BigintLit _ -> None
        (* A declaration answers as its atoms do, where they all agree, as
           Lean's slice of its row does; an intersection as its first
           part's, which holds every value of it. *)
        | Named _,_ ->
          let agree = function
            | Some r :: more when List.for_all (( = ) (Some r)) more -> Some r
            | _ -> None in
          let rec head_answer = function
            | Atoms (a::rest) when Atoms (a::rest) <> Atoms [atom] -> agree (List.map known (a::rest))
            | Meet (principal,_) -> head_answer principal
            | _ -> None in
          (match declarations with
           | None -> None
           | Some declarations ->
             (match (try Some (declared_head declarations [] (Atoms [atom])) with Json.Error _ -> None) with
              | Some head -> head_answer head
              | None -> None))
        (* Any other atom is of another kind than the singleton, or an
           object, never equal to it. *)
        | Top,_ -> None
        | _,_ -> Some false in
      match known atom with Some result -> result=equal | None -> true) xs
    (* Equal to one number other than a zero, or to one string: that value
       (Lean's `observeAtom` and `tagMember`). *)
    |> List.map (fun atom -> match atom,singleton with
      | Num,NumLit b when equal && Int64.float_of_bits b <> 0.0 -> NumLit b
      | Str,StrLit s when equal -> StrLit s
      | _ -> atom))
  (* A union's arms each; an intersection's values are its principal's, so
     it goes where none of those can. *)
  | Union ts -> List.fold_left union (Atoms []) (List.map (restrict ?declarations singleton equal) ts)
  | Meet (principal,_) when restrict ?declarations singleton equal principal = Atoms [] -> Atoms []
  | Rigid _ | Meet _ -> t
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
(* The arms of `t` whose object may still be of them once the value of its
   field `key` answered `slice`: an arm is dropped only where it fixes the
   field, required, at a type none of whose values does. *)
let discriminate_fixed declarations t key slice =
  match declared_head declarations [] t with
  | Atoms atoms ->
    let fixed atom = match (try Some (declared_head declarations [] (Atoms [atom])) with Json.Error _ -> None) with
      | Some (Atoms [Shape {fields;_}]) | Some (Atoms [Exact fields]) ->
        List.exists (fun (f:Semantic.field) -> f.name = key && not f.optional) fields
      | _ -> false in
    let admits atom = not (fixed atom) ||
      (match (try Some (field_type declarations [] (Atoms [atom]) key) with Json.Error _ -> None) with
       | Some field -> slice field <> Atoms []
       | None -> true) in
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
(* The arms an immutable binding's object literal may be of, as TypeScript
   narrows a declared union on its initialization (the assignment-reduced
   type): an arm the literal's keys or literal-valued members rule out is
   dropped, the arm the literal is built at stays. A proposal: Lean checks
   the initializer against what is kept. *)
let assigned_arms declarations t (init:expr) = match t,init.node with
  | Atoms (_::_::_ as atoms),Alloc members ->
    (match List.filter (fun a -> discriminated_record declarations (Atoms [a]) members <> None) atoms with
     | [] -> t
     | kept -> Atoms kept)
  | _ -> t
(* A type's atoms through the declarations and unions that name them. *)
let flat_atoms declarations t =
  let rec go seen t = match t with
    | Union ts -> List.concat_map (go seen) ts
    | Atoms atoms -> List.concat_map (function
        | Named (id,args) when not (List.mem id seen) ->
          (match definition declarations id args with
           | body -> go (id::seen) body
           | exception Json.Error _ -> [Named (id,args)])
        | a -> [a]) atoms
    | Rigid _ | Meet _ -> [] in
  go [] t
let array_atom = function Shape {elements=Some _;_} -> true | _ -> false
(* An open record: a plain object whose keys its type does not bound, which
   may be an array carrying other keys. *)
let open_record_atom = function
  | Shape {elements=None;calls=[];_} -> true
  | _ -> false
let array_or_record_reason =
  "an array keeps its length in its store, not at a location a field of a record names, and an open record \
   may be an array carrying other keys, so no rule reads `length` on a union of an array and a record"
(* `length` read on a union of an array and an open record naming it: refused
   by name. *)
let refuse_length_union declarations pos t name =
  if name = Name "length" then
    let atoms = flat_atoms declarations t in
    let names_length = function
      | Shape {elements=None;calls=[];fields;_} ->
        List.exists (fun (f:Semantic.field) -> f.name = name) fields
      | _ -> false in
    if List.exists array_atom atoms && List.exists names_length atoms then
      explain pos ("a read of `length` on a union of an array and a record: " ^ array_or_record_reason)
let module_arity_reason =
  "its slot is its annotated signature, checked by its own unit, and the arity of an arrow is exact; \
   offering it more parameters would make that slot a claim (DESIGN.md, \"Method members are host-relative\")"
(* Names a `for...in` loop binds: the keys it steps over. *)
let for_in_keys : string list ref = ref []
let for_in_key_reason =
  "a read at a key the loop found may still miss, and that the object owns the key it yields relates \
   two values, which no type and no statement entry states"
(* Whether a signature's parameters, or its callbacks' results, write a
   binder beside an application mentioning it, as `then` and `catch` of
   `Promise` do (`TResult | PromiseLike<TResult>`). *)
let wrapped_binder (s:Semantic.signature) =
  let rec mentions r = function
    | Rigid q -> q = r
    | Union ts -> List.exists (mentions r) ts
    | Meet (t,ts) -> List.exists (mentions r) (t::ts)
    | Atoms atoms -> List.exists (function
        | Named (_,args) -> List.exists (mentions r) args
        | Shape sh -> List.exists (fun (c:Semantic.signature) ->
            List.exists (mentions r) (c.result :: c.params)) sh.calls
        | _ -> false) atoms in
  let binders = List.map (fun (q:Semantic.quantifier) -> q.identity) s.quantified in
  let rec wraps = function
    | Union ts ->
      List.exists (function
        | Rigid r when List.mem r binders -> List.exists (function
            | Atoms atoms -> List.exists (function Named _ as a -> mentions r (Atoms [a]) | _ -> false) atoms
            | _ -> false) ts
        | _ -> false) ts || List.exists wraps ts
    | Atoms atoms -> List.exists (function
        | Shape sh -> List.exists (fun (c:Semantic.signature) -> List.exists wraps (c.result :: c.params)) sh.calls
        | _ -> false) atoms
    | Rigid _ | Meet _ -> false in
  List.exists wraps s.params
let wrapped_binder_reason =
  "TypeScript infers such a binder through the application and fills one left unconstrained from its \
   default, and the producer does neither: a callback whose result is itself an application (a promise) \
   instantiates the binder at its bound"
(* Whether a signature's result applies a declaration to a union of one of
   the signature's binders and something else, as `catch` of `Promise` does
   (`Promise<T | TResult>`): every call's result then adds a binder. *)
let accumulating_binder (s:Semantic.signature) =
  let binders = List.map (fun (q:Semantic.quantifier) -> q.identity) s.quantified in
  match s.result with
  | Atoms atoms -> List.exists (function
      | Named (_,args) -> List.exists (function
          | Union ts -> List.length ts > 1 && List.exists (function
              | Rigid r -> List.mem r binders | _ -> false) ts
              && List.exists (function Rigid r -> not (List.mem r binders) | _ -> true) ts
          | _ -> false) args
      | _ -> false) atoms
  | _ -> false
let accumulating_binder_reason =
  "the family of applications grows with every call, so the graph truncates it at a colour budget, and an \
   instance of the binder is truncated one level before the type it is claimed at"
let generic_instances_reason =
  "the covering rule for quantified signatures relates schemes binding the same rows, which members of one \
   key declared alike (as many binders, the same bounds) do: members declared otherwise need an instance \
   table naming each source signature's image at the target's binders"
(* SKJS's `Closed<T>`, which the SKJS environment declares as the identity
   alias `T` (skjs-environment.d.ts). *)
let closed_alias declarations id =
  let suffix = "skjs-environment.d.ts#" in
  let rec contains i = i + String.length suffix <= String.length id
    && (String.sub id i (String.length suffix) = suffix || contains (i+1)) in
  contains 0 && List.exists (fun (d:Source.declaration) -> d.id = id && match d.parameters,d.expression with
    | [r],Rigid r' -> r = r'
    | _ -> false) declarations
(* Whether a type is, or names through its aliases, a `Closed<T>`. *)
let rec mentions_closed declarations seen t = match t with
  | Union ts -> List.exists (mentions_closed declarations seen) ts
  | Atoms atoms -> List.exists (function
      | Named (id,_) when closed_alias declarations id -> true
      | Named (id,args) when not (List.mem id seen) ->
        (match definition declarations id args with
         | body -> mentions_closed declarations (id::seen) body
         | exception Json.Error _ -> false)
      | _ -> false) atoms
  | Rigid _ | Meet _ -> false
let implicit_index_reason =
  "TypeScript admits a type literal whose named fields fit the index (an implicit index signature), but \
   a value of it may carry other keys of any type, so it meets no index"
let closed_reason =
  "the pipeline reads `Closed<T>` as `T` (the SKJS environment states it so), which promises less than \
   SKJS's closed type"
let receiver_reason =
  "that type admits a call passing any receiver, and the function requires its own"
let invariance_reason =
  "a writable element or field is invariant, as a write through the wider view would break the narrower \
   one; TypeScript relates them covariantly, which is unsound, and SKJS infers the narrower from a \
   later use"
let shape_test_reason =
  "the values of that shape are the meet of the type parameter with it (`T & number`, a meet row), \
   but a tag test refines only clause rows, and no rule narrows a parameter row to that meet \
   (`unknown` to a callable of no known signature)"
let family_test_reason =
  "the value is narrowed to that primitive family, and a tag test does not narrow a type parameter's \
   row to its meet with the family, the `T & number` of TypeScript, so it is no longer read as a `T`"
let primitive_shape shape = List.mem shape ["string";"number";"bigint";"symbol";"undefined";"boolean"]
let object_cell_reason =
  "a `let` without an initializer holds `undefined` until it is assigned, and is known to hold another \
   value only where every path into the read assigned one, with no step between that may write it (a \
   call, whose callee may write any location its operands reach)"
let forgotten_cell_reason =
  "a cell is known by its contract after a step that may write it (a call, whose callee may write any \
   location its operands reach, as the model states no reachability; a closure run later; a throw from \
   anywhere in a `try`)"
let equality_reason =
  "the value may be an object without a field, and the model states no object identity"
let dictionary_spread_reason =
  "the copy owns the keys the dictionary holds when it runs, which no type states: the result is a \
   dictionary only where every part says what it gives under the index's keys, by an index or its \
   exact keys"
let dictionary_presence_reason =
  "presence promotes an optional field of a record, not the index of a dictionary, so the read is \
   still at the index, which may miss"
let absent_key_reason =
  "the key may be absent, and a read of an absent key is stated by no clause the model reads"
let relational_reason =
  "`<` converts such an operand to a number or a string first (`undefined` to NaN, an object through its \
   `valueOf` or `toString`), and the comparison the model states is of two numbers or two strings, the primitive \
   order; an index read past the end is `undefined`, where TypeScript types it as the element"
let exact_optional_reason =
  "the pipeline reads `f?: T` exactly, as absent or a `T` (as `exactOptionalPropertyTypes` does), \
   where the default reading of TypeScript also admits a present `undefined`; `f?: T | undefined` states it"
let thenable_reason =
  "JavaScript adopts a thenable, calling its `then`, instead of settling to it, and a record type does \
   not rule out a `then`, its own or one on its prototype (a `PromiseLike` is one), so the model admits only a \
   realm promise or a primitive there"
let symbol_copy_reason =
  "the copy is stated at its string keys only, and JavaScript also copies an own enumerable \
   symbol-keyed property, so the result states no symbol key"
let copy_field_reason =
  "a field of the copy is allocated at the one type its value is claimed at, for every arm of the operand, \
   and a writable field is invariant, so the arms requiring it at different types (TypeScript types the \
   literal per arm of the contextual union) are not all met"
let extraction_reason =
  "a method is a member of its object, called with it as receiver, and read off it the function loses \
   that receiver; TypeScript types the read as a function, which is unsound"
(* Positions of the callees of calls, a method read among them. *)
let method_callees : Json.t list ref = ref []
(* Whether a read of `key` from a value of `t` finds a method: a host-relative
   member of its record, or of the prototype it reads through. *)
let method_member declarations t key =
  let rec go depth t = depth < 4 && List.exists (function
      | Shape {fields;_} | Exact fields ->
        (match List.find_opt (fun (f:Semantic.field) -> f.name = key) fields with
         | Some f -> f.host
         | None -> List.exists (fun (f:Semantic.field) -> f.name = Name proto_key && go (depth+1) f.read) fields)
      | _ -> false) (try flat_atoms declarations t with Json.Error _ -> []) in
  go 0 t
let mutable_tuple_length_reason =
  "the length of a mutable tuple is not fixed by its type, since `push` is allowed on it (an unsoundness \
   of TypeScript), so its `length` is a number"
(* Names a `typeof` test found of a shape where their type is a type
   parameter or `unknown`, with that shape; keys `in` found present in a
   dictionary, by name. *)
let shape_tests : (string * string) list ref = ref []
(* Fields of names a strict equality found `undefined`. *)
let undefined_fields : (string * string) list ref = ref []
let dictionary_keys : (string * string) list ref = ref []
let rec rigid_arm = function Rigid _ -> true | Union ts -> List.exists rigid_arm ts | _ -> false
(* Names found arrays by `Array.isArray` where they were `unknown`: such a
   value owns an array's store, but no type says it is an array of
   `Array.prototype`. *)
let open_array_tests : string list ref = ref []
let open_array_reason =
  "`Array.isArray(x)`, or `x instanceof Array`, on `unknown` finds that the value owns the store of an \
   array, not that it is an array of `Array.prototype`: the array invariant is a fact of every record and \
   dictionary type, and `unknown` is also the type a handler binds a thrown value at, of which the model \
   states nothing"
(* Keep the atoms of a `typeof` test's shape where it holds, and the others
   where it fails. *)
let rec typeof_slice shape holds = function
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
  (* A type parameter's value, where a test naming one primitive family
     holds: that family, as for `unknown` (TypeScript's `T & number`, of
     which the model states the `number`). *)
  | Rigid _ when holds && primitive_shape shape ->
    typeof_slice shape holds (Atoms [Top])
  (* A union's arms each; an intersection's values are its principal's, so
     it goes where none of those can. *)
  | Union ts -> List.fold_left union (Atoms []) (List.map (typeof_slice shape holds) ts)
  | Meet (t,_) when typeof_slice shape holds t = Atoms [] -> Atoms []
  | t -> t
(* Where `Array.isArray` holds, an open record's arm is an array of the realm:
   a record type is of objects meeting the array invariant, so one owning an
   array's store holds a possibly sparse store and `Array.prototype` (Lean's
   `arraySlice`). Such arms become `sparse ReadonlyArray<unknown>`; an array arm stays;
   `unknown` and a type parameter's arms, of which the invariant says nothing,
   stay as they are. *)
let any_array = array {required=[];optional_elements=[];rest=Some top;readonly=true;dense=false}
let array_slice declarations t =
  let sliced = typeof_slice "array" true t in
  let rec plain = function
    | Atoms _ -> true | Union ts -> List.for_all plain ts | Rigid _ | Meet _ -> false in
  if not (plain sliced) then sliced else
  let atoms = flat_atoms declarations sliced in
  if List.mem Top atoms || not (List.exists open_record_atom atoms) then sliced
  else match typeof_slice "array" true (Atoms atoms) with
    | Atoms kept -> union (ground (List.filter (fun a -> not (open_record_atom a)) kept)) any_array
    | _ -> sliced
(* Names an `instanceof` of a class tested where they were `unknown`: the
   test narrows nothing there, and a member read of one is refused with that
   reason rather than as a read of `unknown`. *)
let unknown_instance_tests : string list ref = ref []
let unknown_instance_reason =
  "`x instanceof C` does not narrow `unknown` to C: an object gets C's prototype without C's constructor \
   running (`Object.create(C.prototype)`, `Object.setPrototypeOf`, `Reflect.construct` with C as the new \
   target), so C's prototype on its chain is no evidence of C's fields, and the model assumes it of no value \
   a unit receives"
(* Keep the atoms that may own the key where `key in o` held, and those that
   may lack it where it failed: a record's required field is owned, a fresh
   literal's keys are exactly its fields', and a primitive owns none. *)
(* A plain record whose optional key was found present: the key is a field
   of it from then on, since an object's keys are fixed at its allocation.
   Lean checks the promoted record against the tested one (`promote`). *)
let present key =
  let promote = List.map (fun (f:Semantic.field) ->
    if f.name = Name key && f.optional then {f with optional=false} else f) in
  function
  | Shape ({calls=[];elements=None;indexes=[];_} as s) -> Shape {s with fields=promote s.fields}
  | Exact fields -> Exact (promote fields)
  | a -> a
let key_slice key holds = function
  | Atoms xs when not (List.mem Top xs) ->
    let field_of fields = List.find_opt (fun (f:Semantic.field) -> f.name = Name key) fields in
    let has = function
      | Shape s -> (match field_of s.fields with
        | Some f when not f.optional -> Some true | _ -> None)
      | Exact fields -> (match field_of fields with
        | Some f -> if f.optional then None else Some true
        (* A class instance may inherit the key from its prototype. *)
        | None -> if List.exists (fun (f:Semantic.field) -> f.name = Name proto_key) fields
          then None else Some false)
      | Ctors _ | Callable | Named _ | Top -> None
      | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _
      | Bigint | Symbol | BigintLit _ -> Some false in
    Atoms (List.filter_map (fun a -> match has a with
      | Some result -> if result = holds then Some a else None
      | None -> Some (if holds then present key a else a)) xs)
  | t -> t
(* Whether a field's contents can be asserted of an object of this type: a
   plain record that has the field, not optionally, or a union of such: a
   fact names the location the field is at, whichever record the object is. *)
let record_field declarations t field =
  let rec has seen t = match (try Some (declared_head declarations seen t) with Json.Error _ -> None) with
    | Some (Atoms (_::_ as atoms)) -> List.for_all (function
        | Shape {fields;calls=[];elements=None;indexes=[]} | Exact fields ->
          List.exists (fun (f:Semantic.field) -> f.name = Name field && not f.optional) fields
        | Named (id,_) as atom when not (List.mem id seen) -> has (id::seen) (Atoms [atom])
        | _ -> false) atoms
    | _ -> false in
  has [] t
(* A guard on a field of an immutable binding's object: what the field holds
   is known until a step may write it. *)
let refine_field declarations env name field refine =
  (* A read of an optional key that gave something other than `undefined`
     found the key present: the object's record arms have it from then on
     (Lean's `promote`, through the read's optional link). *)
  let env = match List.assoc_opt name env with
    | Some (Value t) when refine (Atoms [Undef]) = Atoms [] ->
      let rec arms seen t = match declared_head declarations seen t with
        | Atoms atoms -> List.concat_map (function
            | Named (id,_) as atom when not (List.mem id seen) -> arms (id::seen) (Atoms [atom])
            | a -> [a]) atoms
        | _ -> [] in
      let atoms = try arms [] t with Json.Error _ -> [] in
      let names = function
        | Shape {fields;calls=[];elements=None;indexes=[]} | Exact fields ->
          List.exists (fun (f:Semantic.field) -> f.name = Name field) fields
        | _ -> false in
      let optional = function
        | Shape {fields;_} | Exact fields ->
          List.exists (fun (f:Semantic.field) -> f.name = Name field && f.optional) fields
        | _ -> false in
      if atoms <> [] && List.for_all names atoms && List.exists optional atoms
      then refine_value env name (fun _ -> Atoms (List.map (present field) atoms))
      else env
    | _ -> env in
  match List.assoc_opt name env with
  | Some (Value t) when record_field declarations t field ->
    let key = field_key name field in
    let current = match List.assoc_opt key env with
      | Some (Value c) -> Some c
      | _ -> (try Some (field_type declarations [] t (Name field)) with Json.Error _ -> None) in
    (match current with Some c -> fact env key (refine c) | None -> env)
  | _ -> env
let rec branch_with ?(modules = fun _ -> None) ?(claimed = fun _ -> None) declarations env cond truth =
  let branch = branch_with ~modules ~claimed declarations in
  let refine_field = refine_field declarations in
  match cond.node with
  | Not e -> branch env e (not truth)
  (* A name as a condition is tested for truthiness; a Boolean's slice is
     its literal. *)
  | Id name -> refine_value env name (truthy_slice truth)
  (* Where some arm leaves the field optional or unnamed, so that nothing is
     known of what it holds, the test keeps the arms whose field may answer
     so (Lean's `fieldSlice` through the read's link): `IteratorResult` by
     `done`. *)
  | Read ({node=Id name;_},Name field) ->
    let env = match List.assoc_opt name env with
      | Some (Value t) when not (record_field declarations t field) ->
        refine_value env name (fun t -> discriminate_fixed declarations t (Name field) (truthy_slice truth))
      | _ -> env in
    refine_field env name field (truthy_slice truth)
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
    (if truth = equal && shape <> "array" && shape <> "object" then match List.assoc_opt name env with
      | Some b when rigid_arm (binding_type b) || binding_type b = top ->
        shape_tests := (name,shape) :: !shape_tests
      | _ -> ());
    let env = refine_value env name (if shape = "array" && truth = equal then array_slice declarations
      else typeof_slice shape (truth = equal)) in
    (if shape = "array" && truth = equal then match List.assoc_opt name env with
      | Some b when binding_type b = top ->
        open_array_tests := name :: !open_array_tests
      | _ -> ());
    env
  | HasKey ({node=Literal (LString key);_},{node=Id name;_}) ->
    (if truth then match List.assoc_opt name env with
      | Some b when List.exists (function
          | Shape {indexes=_::_;fields;_} -> not (List.exists (fun (f:Semantic.field) -> f.name = Name key) fields)
          | _ -> false) (flat_atoms declarations (binding_type b)) ->
        dictionary_keys := (name,key) :: !dictionary_keys
      | _ -> ());
    refine_value env name (key_slice key truth)
  (* `x instanceof C` is the same test of the class's key: primitives and
     fresh literals lack it; any other arm may have it or not. *)
  | InstanceTest (key,{node=Id name;_},_) ->
    (match List.assoc_opt name env with
     | Some b when truth && (match binding_type b with Atoms xs -> List.mem Top xs | _ -> false) ->
       unknown_instance_tests := name :: !unknown_instance_tests
     | _ -> ());
    refine_value env name (key_slice key truth)
  | TypeofTest (shape,equal,{node=Read ({node=Id name;_},Name field);_}) ->
    if shape = "undefined" && truth = equal then undefined_fields := (name,field) :: !undefined_fields;
    refine_field env name field (typeof_slice shape (truth = equal))
  (* `x == null` holds of null and undefined alike. *)
  | Equality ((LooseEqual | LooseUnequal as op),{node=Id name;_},{node=Literal (LNull | LUndefined);_})
  | Equality ((LooseEqual | LooseUnequal as op),{node=Literal (LNull | LUndefined);_},{node=Id name;_}) ->
    let equal = truth=(op=LooseEqual) in
    refine_value env name (fun t ->
      if equal then union (restrict ~declarations Nul true t) (restrict ~declarations Undef true t)
      else restrict ~declarations Undef false (restrict ~declarations Nul false t))
  (* A comparison with a singleton, a literal or a name or field holding one,
     narrows the other operand where it is a name, or a field of a name's
     object, and that object's arms, on both outcomes. Where it holds, one
     with a name or field holding one of several singletons narrows the
     other to the values that may equal one of them. *)
  | Equality ((StrictEqual | StrictUnequal as op),l,r) ->
    let equal = truth=(op=StrictEqual) in
    (match l.node,r.node with
     | Read ({node=Id o;_},Name k),Literal LUndefined | Literal LUndefined,Read ({node=Id o;_},Name k) when equal ->
       undefined_fields := (o,k) :: !undefined_fields
     | _ -> ());
    (* An immutable name, or a field of one: read again where Lean tests it
       against each singleton, which nothing between has changed. *)
    let immutable n = match List.assoc_opt n env with
      | Some (Value _) -> true | Some (Storage _) -> false | None -> modules n <> None in
    let reread (e:expr) = match e.node with
      | Id n | Read ({node=Id n;_},_) -> immutable n
      | _ -> false in
    (* An operand evaluated once into a slot of its own, a call say: Lean
       splits it there, against an immutable name. *)
    let saved (e:expr) = match e.node with
      | Literal _ | Id _ | Read ({node=Id _;_},_) -> false
      | _ -> true in
    let values (e:expr) = Option.bind (match e.node with
      | Literal lit -> Some (literal_type lit)
      | Id n -> (match List.assoc_opt n env with Some b -> Some (binding_type b) | None -> modules n)
      | Read ({node=Id n;_},Name f) ->
        (match List.assoc_opt (field_key n f) env,List.assoc_opt n env with
         | Some b,_ -> Some (binding_type b)
         | None,Some b -> (try Some (field_type declarations [] (binding_type b) (Name f)) with Json.Error _ -> None)
         (* A module value's field, an enum member: its declared type. *)
         | None,None -> Option.bind (modules n) (fun t ->
             try Some (field_type declarations [] t (Name f)) with Json.Error _ -> None))
      | _ -> claimed e.pos) (fun t -> match singleton_atom t,t with
        | Some a,_ -> Some ((fun t -> restrict ~declarations a equal t),true)
        | None,Atoms (_::_ as atoms) when equal
            && List.for_all (fun a -> singleton_atom (Atoms [a]) <> None) atoms ->
          Some ((fun t -> combine (List.map (fun a -> restrict ~declarations a true t) atoms)),false)
        | _ -> None) in
    (* What a field holds is known from a test against one singleton, whose
       saved read Lean observes; against several, from Lean's test of each,
       one read at a time, where both operands are read again there or the
       other is saved and this one is an immutable name. *)
    let narrow env (operand:expr) other = match values other,operand.node with
      | None,_ -> env
      (* Against a singleton, this operand is the one Lean tests: it learns
         nothing of the other's several values. *)
      | Some (_,false),_ when (match values operand with Some (_,true) -> true | _ -> false) -> env
      | Some (_,false),Id name when not (immutable name && (reread other || saved other)) -> env
      | Some (_,false),Read _ when not (reread operand && reread other) -> env
      | Some (_,true),Read _ when saved other -> env
      | Some (slice,_),Id name -> refine_value env name slice
      | Some (slice,_),Read ({node=Id name;_},key) ->
        let env = refine_value env name (fun t -> discriminate declarations t key slice) in
        (match key with
         | Name field -> refine_field env name field slice
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

(* An object literal with spreads, as a merge reads it: each alternative of
   what is built so far is its fields and whether its own keys are exactly
   theirs; a source's alternative may also state an index, the type of every
   own string key it does not name. *)
type alternative = { afields : Semantic.field list; exact : bool; index : ty option }

(* A method member is host-relative: its object may hold it on its
   prototype, which a spread does not copy. *)
let method_field (f:Semantic.field) = f.host

(* The alternatives a spread's operand gives: nothing from a primitive other
   than a string, a record's fields otherwise. *)
let string_key (f:Semantic.field) = match f.name with Name _ -> true | Key _ -> false
let rec source_alternatives declarations seen t = match t with
  | Atoms atoms -> List.concat_map (function
      | Nul | Undef | True | False | Num | NumLit _ | Bigint | BigintLit _ | Symbol ->
        [{afields=[];exact=true;index=None}]
      (* A copy takes no symbol-keyed property, a private slot's included
         (DESIGN.md, "Object literals"). *)
      | Exact fs -> [{afields=List.filter (fun (f:Semantic.field) -> f.name <> Name proto_key && string_key f) fs;
                      exact=true;index=None}]
      | Shape {fields;indexes;calls=[];elements=None} ->
        (* The string index states every own string key's type; a number
           index states only the canonical numeric ones', so a key it covers
           is left unstated, as an open record's is. *)
        [{afields=List.filter (fun (f:Semantic.field) ->
            not (method_field f) && f.name <> Name proto_key && string_key f) fields;exact=false;
          index=Option.map (fun (i:index_signature) -> i.value)
            (List.find_opt (fun (i:index_signature) -> i.keys=Strings) indexes)}]
      | Named (id,args) ->
        if List.mem id seen then unsupported "unguarded spread cycle";
        source_alternatives declarations (id::seen) (definition declarations id args)
      (* Each other operand's own enumerable properties are not what its
         type bounds. *)
      | Str | StrLit _ -> unsupported "a spread copies the own enumerable properties of a plain object; \
          a string's are its characters at index keys, which no record states"
      | Shape {elements=Some _;_} -> unsupported "a spread copies the own enumerable properties of a plain object; \
          an array's are its indices and whatever keys it carries, which no record states"
      | Shape _ | Callable -> unsupported "a spread copies the own enumerable properties of a plain object; \
          a function's or an indexed object's are whatever was assigned to it, which its type does not bound"
      | Ctors _ -> unsupported "a spread copies the own enumerable properties of a plain object; \
          a class value's are its static fields, which its construct signatures do not state"
      | _ -> unsupported "a spread copies the own enumerable properties of a plain object; one of a string, an array, a function or a class value is outside the fragment") atoms
  | Union ts -> List.concat_map (source_alternatives declarations seen) ts
  | Meet _ | Rigid _ -> unsupported "a spread of an intersection or a type parameter is outside the fragment"

(* A source's properties defined over an alternative's: a key the source
   surely has takes its type; one the alternative has keeps its own where the
   source never has it, or with the source's optional or index type where it
   may; a key only the source may have is optional where the alternative's
   keys are exact. A key either side may hold at an unknown type is not
   stated. *)
let merge_alternative (a:alternative) (b:alternative) : alternative =
  let find fs k = List.find_opt (fun (f:Semantic.field) -> f.name = k) fs in
  let names = List.fold_left (fun ns (f:Semantic.field) ->
    if List.mem f.name ns then ns else ns @ [f.name]) [] (a.afields @ b.afields) in
  let field name optional t = ({name;optional;read=t;write=Some t;host=false} : Semantic.field) in
  let fields = List.filter_map (fun k ->
    match find b.afields k with
    | Some f when not f.optional -> Some (field k false f.read)
    | bf ->
      let b_maybe = match bf,b.index,k with
        | Some f,_,_ -> Some f.read
        | None,Some t,Name _ -> Some t
        | None,_,_ -> None in
      let b_never = bf = None && b.exact in
      match find a.afields k with
      | Some f when not f.optional ->
        if b_never then Some (field k false f.read)
        else Option.map (fun t -> field k false (union f.read t)) b_maybe
      | Some f ->
        if b_never then Some (field k true f.read)
        else Option.map (fun t -> field k true (union f.read t)) b_maybe
      (* A key the alternative may hold at its index: a dictionary owns no
         prototype, so the key is optional at either side's type. *)
      | None -> (match a.index,k with
        | Some ta,Name _ -> Option.map (fun t -> field k true (union ta t)) b_maybe
        | _ -> if a.exact then Option.map (field k true) b_maybe else None)) names in
  (* Where a side states an index and each side says what it gives under
     every string key, by an index or by its exact keys, the result states
     the index, at what either side and the string-keyed fields hold, and so
     does every string-keyed field: Lean's merge of a dictionary. *)
  match a.index,b.index with
  | (Some _,_ | _,Some _) when (a.index <> None || a.exact) && (b.index <> None || b.exact) ->
    let keyed (f:Semantic.field) = match f.name with Name _ -> true | Key _ -> false in
    let v = List.fold_left union (Atoms [])
      (Option.to_list a.index @ Option.to_list b.index
       @ List.map (fun (f:Semantic.field) -> f.read) (List.filter keyed fields)) in
    { afields=List.map (fun (f:Semantic.field) ->
        if keyed f then {f with read=v; write=Some v} else f) fields;
      exact=a.exact && b.exact; index=Some v }
  | _ -> { afields=fields; exact=a.exact && b.exact; index=None }

let alternative_type (a:alternative) =
  match a.index with
  | Some v -> Atoms [Shape {fields=a.afields;
      indexes=[{keys=Strings;value=v;writable=Some v}];calls=[];elements=None}]
  | None ->
    if a.exact && List.for_all (fun (f:Semantic.field) -> not f.optional) a.afields
    then Atoms [Exact a.afields] else record a.afields

(* Evolving bindings, TypeScript's evolving `any`: an unannotated `let`
   initialized with `null` or `undefined`, and an unannotated local
   initialized with `[]`. Each is keyed by its initializer's position; its
   contract is the union of what is written into it (the values assigned to
   the `let`, the elements an array's `push`, `unshift` and index writes
   add), which a pass collects in [evolving_seen] and the next assumes from
   [evolving_assumed] (`infer_function`). *)
let evolving_assumed : (Json.t * Semantic.ty) list ref = ref []
let evolving_seen : (Json.t * Semantic.ty) list ref = ref []
let evolve key t =
  evolving_seen := (key,union (Option.value (List.assoc_opt key !evolving_seen) ~default:(Atoms []))
    (widen t)) :: List.remove_assoc key !evolving_seen
let evolved key = Option.value (List.assoc_opt key !evolving_assumed) ~default:(Atoms [])
(* One pass over a function. [offered] gives, for a named closure's creation,
   the further signatures its uses offer it; the pass reports them as
   [requests], and [infer_function] runs a second pass with them. *)
let infer_pass offered declarations module_functions (f:Source.fn) =
  let entries = ref [] and expressions = ref [] and instantiations = ref [] in
  (* A condition's operands are claimed before it is branched on: an operand
     Lean evaluates once into a slot of its own holds what it is claimed at. *)
  (* The evolving bindings in scope, by name: the key, and whether the
     binding is an array whose elements evolve. *)
  let evolving = ref [] in
  (* The immutable locals a statement added a key to, and those of them
     claimed with their exact keys while nothing else can reach the object. *)
  let grown_locals = ref [] and exact_locals = ref [] in
  let branch = branch_with declarations ~modules:(fun n ->
    try Option.map Lazy.force (List.assoc_opt n module_functions) with Json.Error _ -> None)
    ~claimed:(fun pos -> List.find_map (fun (x:expression) ->
      if x.pos = pos then Some x.type_ else None) !expressions) in
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
    | BlockBody ss -> allocated_in ss
    | _ -> None
  and allocated_in ss = match List.rev ss with
    | {statement=Return e;_} :: _ -> allocated e
    | {statement=If (_,a,_);_} :: _ -> allocated_in a
    | _ -> None in
  (* The allocations a constructor ends in, each arm's. *)
  let rec tails (body:expr) = match body.node with
    | Alloc _ | Build _ -> [body.pos]
    | BlockBody ss -> tails_in ss
    | _ -> []
  and tails_in ss = match List.rev ss with
    | {statement=Return e;_} :: _ -> tails e
    | {statement=If (_,a,b);_} :: _ -> tails_in a @ tails_in b
    | _ -> [] in
  (* Whether the constructor being typed is a class's fresh one, which a
     class extending it constructs: claimed also at the instance it
     allocates, whose own keys are exact. *)
  let fresh_constructor = ref false in
  (* Objects bound to a name: a class's prototype, read by its instances
     under the prototype key. *)
  let objects = ref [] in
  let named_closure n written (init:expr) = match written,init.node with
    | (None | Some (Atoms [Shape {calls=[_];fields=[];indexes=[];elements=None}])),Lambda (_,[],ps,_,false,_,_) ->
      closures := (n,(init.pos,List.map snd ps)) :: !closures
    | None,Alloc fs -> objects := (n,fs) :: !objects
    | Some _,Ctor {node=Lambda (None,[],ps,[],false,Some instance,body);_} when allocated body <> None ->
      let fs = Option.get (allocated body) in
      (* An instance's methods are its prototype chain's, the nearer first. *)
      let rec chain seen fs = match List.assoc_opt (Name proto_key) fs with
        | Some {node=Id p;_} when not (List.mem p seen) ->
          let own = Option.value (List.assoc_opt p !objects) ~default:[] in
          List.filter (fun (k,_) -> k <> Name proto_key) own
          @ List.filter (fun (k,_) -> not (List.mem_assoc k own)) (chain (p::seen) own)
        | _ -> [] in
      let fs = if List.mem_assoc (Name proto_key) fs then chain [] fs else fs in
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
            (field_type declarations [] s.result key)) with Json.Error _ -> None) with
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
          requests := (pos,{call_effect=s.call_effect;quantified=[];receiver=top;params=if longer then s.params else params;
                            variadic=None;rest_pack=None;result=s.result}) :: !requests)
        (List.filter (fun (s:Semantic.signature) -> s.quantified=[]) signatures)
    | _ -> () in
  (* A name no parameter or local binds is one of the file's functions. *)
  let resolve env n = match List.assoc_opt n env with
    | Some b -> binding_type b
    | None -> (match List.assoc_opt n module_functions with
      | Some g -> Lazy.force g | None -> Json.fail ("unbound name " ^ n)) in
  (* Object literals a spread copies, directly or as an arm of `&&`, `||`,
     `??` or a conditional: each is claimed with its exact keys, which is
     what tells the copy owns no other key. *)
  let exact_allocs = ref [] in
  let rec mark_exact (e:expr) = match e.node with
    | Alloc _ -> exact_allocs := e.pos :: !exact_allocs
    | Logical (_,_,b) | Coalesce (_,b) | Comma (_,b) -> mark_exact b
    | Conditional (_,a,b) -> mark_exact a; mark_exact b
    | Cast (("nonNull" | "satisfies"),_,e) -> mark_exact e
    | _ -> () in
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
  (* What [f] computes, leaving no claim behind: the elements an evolving
     array is given, seen before the call that gives them is typed. *)
  let quietly f =
    let saved = (!closures,!requests,!classes,!entries,!expressions,!instantiations,!instances,!arrows) in
    let result = try Some (f ()) with Json.Error _ -> None in
    let (a,b,c,d,e,g,h,i) = saved in
    closures := a; requests := b; classes := c; entries := d; expressions := e;
    instantiations := g; instances := h; arrows := i;
    result in
  let rec reads n (e:expr) =
    (match e.node with Id m -> m = n | _ -> false) || List.exists (reads n) (Source.children e) in
  let evolving_array (receiver:expr) = match receiver.node with
    | Id n -> (match List.assoc_opt n !evolving with Some (key,true) -> Some key | _ -> None)
    | _ -> None in
  let entry env span = match Json.list span with
    | start::_ ->
      (* A field's contents are claimed where its object is still one record. *)
      let bindings = List.filter (fun (n,_) -> not (is_field n) ||
        (match List.assoc_opt (owner n) env with
         | Some (Value t) -> record_field declarations t (field_of n)
         | _ -> false)) env in
      entries := {start;bindings} :: !entries
    | [] -> Json.fail "empty source span" in
  (* A step that may write a cell it does not name: a call, or a write. The
     cells are then known only by their contracts. Creating a closure runs
     nothing. *)
  let rec stirs (e:expr) = match e.node with
    | Call _ | Invoke _ | New _ | Apply _ | Bind _ | Write _ | IndexWrite _ | Assign _
    | Update _ | LogicalAssign _ | NullishAssign _ | ArrayAssign _ | ObjectAssign _ -> true
    | Lambda _ -> false
    | _ -> List.exists stirs (Source.children e) in
  (* Where two arms meet, a cell holds what either left in it. *)
  let join before left right =
    List.filter_map (fun (n,b) -> match b,List.assoc_opt n left,List.assoc_opt n right with
      | Storage (contract,_),Some (Storage (_,l)),Some (Storage (_,r)) -> Some (n,holding contract (union l r))
      (* A local an arm added a key to holds the object either arm left. *)
      | Value _,Some (Value l),Some (Value r) when List.mem n !grown_locals && l <> r ->
        Some (n,Value (union l r))
      | _ when is_field n -> None
      | _ -> Some (n,b)) before
    (* A field's contents are known after both arms where each knows them. *)
    @ List.filter_map (fun (n,b) -> match b,List.assoc_opt n right with
      | Value l,Some (Value r) when is_field n && List.mem_assoc (owner n) before ->
        Some (n,Value (union l r))
      | _ -> None) left in
  (* What is known after an expression ran, from what was known before: an
     assignment leaves its cell holding the value it wrote, its claim; a
     conditional, what either arm left; an operator, what its operands left,
     in order; any other step that may write a cell it does not name (a call,
     a write, a short circuit), each cell by its contract. The claims of the
     expression's parts are already made. *)
  (* A write adding a key to an immutable local's object: the value it adds
     is claimed at the new field's contract, and the local holds the grown
     object from the next statement on. Lean decides whether the local owns
     its object. *)
  let adds env (receiver:expr) t name = match receiver.node with
    | Id n -> (match List.assoc_opt n env with
      | Some (Value _) -> may_lack declarations t name
      | _ -> false)
    | _ -> false in
  let rec effects env (e:expr) = match e.node with
    | Lambda _ | Literal _ | Id _ -> env
    | Assign (n,rhs) ->
      let env = effects env rhs in
      let t = List.find_map (fun (x:expression) -> if x.pos = e.pos then Some x.type_ else None) !expressions in
      (match List.assoc_opt n env,t with
       | Some (Storage _),Some t -> assign env n t
       | Some (Storage _),None -> forget ~only:(( = ) n) env
       | _ -> env)
    | Conditional (c,a,b) ->
      let env = effects env c in
      join env (effects (branch env c true) a) (effects (branch env c false) b)
    | Arith _ | Equality _ | Not _ | Unary _ | Read _ | Index _ | Cast _ | TypeofTest _
    | HasKey _ | Alloc _ | ArrayLiteral _ | Comma _ ->
      List.fold_left effects env (Source.children e)
    | _ -> if stirs e then forget env else env in
  (* The contract an assignment target is read and written at: a local's
     storage contract, or the type of the field or named index, whose read is
     also the target's claim. *)
  (* A closure's statements are checked as a function body's are, by the
     statement checker below: a constructor's too, at a result where the
     closure has one, collecting the types its `return`s give. *)
  let block_statements = ref (fun (_:ty option) (_:ty list ref) env (_:stmt list) -> env) in
  (* The body the statement checker is in: its result, and where its
     `return`s' types are collected. *)
  let block_result = ref (Some f.result)
  and block_returned = ref (ref []) in
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
     operand, which TypeScript refuses. An element or field of a literal
     that is none of these (`[x.f] as const`) keeps its own type, as
     TypeScript's const context does. *)
  and const_type ?(nested = false) env (e:expr) = match e.node with
    | Literal l -> Some (literal_type l)
    | Id n -> Some (resolve env n)
    | Cast ("const",None,e) -> const_type ~nested env e
    | ArrayLiteral es ->
      let elements = List.map (const_type ~nested:true env) es in
      if List.mem None elements then None
      else Some (array {required=List.filter_map Fun.id elements;optional_elements=[];rest=None;readonly=true;dense=true})
    | Alloc fs ->
      let fields = List.map (fun (name,e) -> name,const_type ~nested:true env e) fs in
      if List.exists (fun (_,t) -> t = None) fields then None
      else Some (record (List.map (fun (name,t) ->
        {name;optional=false;read=Option.get t;write=None;host=false}) fields))
    | _ when nested -> quietly (fun () -> expr env e)
    | _ -> None
  (* `await e` and an async body's `return e` (the intrinsics `%Await%` and
     `%AsyncReturn%`) of a value that may be an object other than a promise
     the intrinsic names, or of a type parameter or `unknown`. *)
  and explain_thenable (e:expr) (target:expr) (signature:Semantic.signature) actuals =
    match target.node,signature.params,actuals with
    | Id ("%Await%" | "%AsyncReturn%" as n),[param],[actual] ->
      let rec shallow = function
        | Atoms xs -> xs | Union ts -> List.concat_map shallow ts | Rigid _ | Meet _ -> [] in
      let promises = List.filter_map (function Named (id,_) -> Some id | _ -> None) (shallow param) in
      let rec atoms seen = function
        | Union ts -> List.concat_map (atoms seen) ts
        | Atoms xs -> List.concat_map (function
            | Named (id,_) as a when List.mem id promises -> [a]
            | Named (id,args) as a when not (List.mem id seen) ->
              (try atoms (id::seen) (definition declarations id args) with Json.Error _ -> [a])
            | a -> [a]) xs
        | Rigid _ | Meet _ -> [Top] in
      let settled = function
        | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | BigintLit _ | Symbol -> true
        | Named (id,_) -> List.mem id promises
        | _ -> false in
      if not (List.for_all settled (atoms [] actual)) then
        explain e.pos (if n = "%Await%"
          then "an await of a non-promise object, or of a value of a type parameter or `unknown`: " ^ thenable_reason
          else "the result of an async function that may be an object other than a promise: " ^ thenable_reason
            ^ "; the promise of an async function is settled to a primitive or adopts a promise of one")
    | _ -> ()
  (* A name `Array.isArray` found an array of, where it was `unknown`, used
     where every array would do. *)
  and explain_open_array site env n expected =
    match expected with
    | Some x when List.mem n !open_array_tests ->
      let any_array = function
        | Shape {elements=Some {required=[];optional_elements=[];rest=Some (Atoms [Top] | Rigid _);_};
                 fields=[];indexes=[];calls=[]} -> true
        | _ -> false in
      let wanted = flat_atoms declarations x in
      let actual = try resolve env n with Json.Error _ -> Atoms [] in
      if wanted <> [] && List.for_all any_array wanted && actual = top
      then explain site ("`unknown` used as an array after `Array.isArray`: " ^ open_array_reason)
    | _ -> ()
  (* A record at an index signature, which TypeScript admits through an
     implicit index signature. *)
  and explain_record_at_index site env n expected =
    match expected with
    | Some x ->
      let named = try resolve env n with Json.Error _ -> Atoms [] in
      let actual = flat_atoms declarations named and wanted = flat_atoms declarations x in
      let record = function Shape {elements=None;calls=[];indexes=[];_} -> true | _ -> false in
      let dictionary = function Shape {elements=None;calls=[];indexes=_::_;_} -> true | _ -> false in
      if actual <> [] && List.for_all record actual && List.exists dictionary wanted
         && not (List.exists (fun a -> record a || a = Top) wanted) then
        explain site ("a record at an index signature: " ^ implicit_index_reason
          ^ (if mentions_closed declarations [] named then "; " ^ closed_reason else ""))
    | None -> ()
  (* A write at a key a dictionary may lack adds it. *)
  and dictionary_growth site t field =
    match flat_atoms declarations t with
    | [] -> ()
    | atoms -> if List.for_all (function
        | Shape {indexes=_::_;elements=None;calls=[];fields;_} ->
          not (List.exists (fun (f:Semantic.field) -> f.name = field) fields)
        | _ -> false) atoms then
      explain site ("a write adds the property '" ^ key_text field ^ "' where a dictionary may lack it: \
        another reference may hold the dictionary, and would see its keys change")
  and expr ?expected env e =
    let site = e.pos in
    let t = match e.node with
    | Id n ->
      Option.iter (fun expected -> Option.iter (fun c -> offer_class c expected)
        (List.assoc_opt n !classes)) expected;
      (* A named closure expected at a signature binding more parameters
         than it does is offered it, wherever it flows: an argument (as
         below), an annotated binding, a return, a field. *)
      (match expected with
       | Some (Atoms [Shape {calls=[o];fields=[];indexes=[];elements=None}])
         when List.mem_assoc n !closures && List.mem_assoc n env ->
         Option.iter (fun state -> state ()) (closure_offer n o)
       | _ -> ());
      (* A named function value, a module function or a parameter, where a
         signature binding more parameters than it does, or indifferent to
         the receiver it requires, is expected (a closure literal is offered
         such a signature instead). *)
      (match expected with
       | Some x when not (List.mem_assoc n !closures) ->
         let rec calls t = match t with
           | Meet (t,ts) -> List.concat_map calls (t::ts)
           | t -> List.concat_map (function Shape s -> s.calls | _ -> [])
                    (flat_atoms declarations t) in
         let own = if not (List.mem_assoc n env) && List.mem_assoc n module_functions
           then (try Some (Lazy.force (List.assoc n module_functions)) with Json.Error _ -> None)
           else (try Some (resolve env n) with Json.Error _ -> None) in
         (match own with
          | Some (Atoms [Shape {calls=[own];fields=[];indexes=[];elements=None}]) ->
            if List.exists (fun (c:Semantic.signature) ->
                List.length c.params > List.length own.params
                || (c.variadic <> None && own.variadic = None)) (calls x)
            then explain site ("a named function where a signature binding more parameters is expected: "
              ^ module_arity_reason)
            else if own.receiver <> top && List.exists (fun (c:Semantic.signature) -> c.receiver = top) (calls x)
            then explain site ("a function whose `this` is typed where a callback indifferent to its receiver is \
              expected: " ^ receiver_reason)
          | _ -> ())
       | _ -> ());
      (* A mutable array, or an instance with a writable field, at one whose
         element or field is wider. *)
      (match expected with
       | Some x ->
         let mutable_rest = function
           | Shape {elements=Some {required=[];optional_elements=[];rest=Some r;readonly=false;dense=true};_} -> Some r
           | _ -> None in
         let actual = flat_atoms declarations (resolve env n) and wanted = flat_atoms declarations x in
         let rests = List.filter_map mutable_rest actual and wanted_rests = List.filter_map mutable_rest wanted in
         if rests <> [] && List.length rests = List.length actual && wanted_rests <> []
            && List.for_all (fun r -> not (List.mem r wanted_rests)
                 && List.exists (fun w -> plausible_subtype r w) wanted_rests) rests
            && not (List.exists (function
                 | Shape {elements=Some {readonly=true;_};_} -> true | _ -> false) wanted) then
           explain site ("a mutable array at one of a wider element: " ^ invariance_reason);
         (match resolve env n, x with
          | Atoms [Named (a,xs)], Atoms [Named (b,ys)] when a = b && xs <> ys ->
            (match definition declarations a xs, definition declarations b ys with
             | Atoms [Shape s1], Atoms [Shape s2] ->
               if List.exists (fun (f:Semantic.field) -> f.write <> None && not f.host && List.exists (fun (g:Semantic.field) ->
                   g.name = f.name && g.read <> f.read) s2.fields) s1.fields then
                 explain site ("an instance at another whose writable field differs: " ^ invariance_reason)
             | _ -> ()
             | exception Json.Error _ -> ())
          | _ -> ())
       | None -> ());
      (* A value a type test found of a shape, where its type is a type
         parameter or `unknown`. *)
      (match expected, List.assoc_opt n !shape_tests with
       | Some x, Some shape when primitive_shape shape ->
         if rigid_arm x then
           explain site ("a `typeof x === \"" ^ shape ^ "\"` test on a value of a type parameter or `unknown`: "
             ^ family_test_reason)
       | Some x, Some shape when not (rigid_arm x) ->
         explain site ("a `typeof x === \"" ^ shape ^ "\"` test on a value of a type parameter or `unknown`: "
           ^ shape_test_reason)
       | _ -> ());
      (* A cell read at its contract where the use asks for less. *)
      (match expected, List.assoc_opt n env with
       | Some x, Some (Storage (contract,current)) when current = contract
           && not (plausible_subtype contract x) ->
         let atoms = flat_atoms declarations contract in
         if List.mem Undef atoms && List.exists (function
             | Shape _ | Exact _ | Named _ | Callable | Ctors _ -> true | _ -> false) atoms
            && plausible_subtype (Semantic.without_nullish contract) x
         then explain site ("a `let` holding an object read where it must be assigned: " ^ object_cell_reason)
         else explain site ("a cell read at its contract: " ^ forgotten_cell_reason)
       | _ -> ());
      (* An instance of a declaration with generic methods at an instance of
         another, `Promise<A>` at `PromiseLike<B>`: refused by name. Two
         instances of one declaration relate through their methods. *)
      (match expected with
       | Some x ->
         let generic_methods id args =
           match definition declarations id args with
           | Atoms [Shape sh] -> List.exists (fun (f:Semantic.field) -> match f.read with
               | Atoms [Shape {calls;_}] ->
                 List.exists (fun (c:Semantic.signature) -> c.quantified <> []) calls
               | _ -> false) sh.fields
           | _ -> false
           | exception Json.Error _ -> false in
         let apps t = match t with
           | Atoms atoms -> List.filter_map (function Named (id,args) -> Some (id,args) | _ -> None) atoms
           | _ -> [] in
         (match apps (resolve env n), apps x with
          | [a,xs], (_::_ as wanted) when not (List.mem (a,xs) wanted)
              && List.for_all (fun (b,ys) -> b <> a && generic_methods b ys
                   (* Instances that are one type, their arguments unused. *)
                   && (try
                         (* A method's receiver names the instance itself. *)
                         let unreceived = function
                           | Atoms [Shape sh] -> Atoms [Shape {sh with fields=List.map (fun (f:Semantic.field) ->
                               match f.read with
                               | Atoms [Shape m] -> {f with read=Atoms [Shape {m with calls=List.map
                                   (fun (c:Semantic.signature) -> {c with receiver=top}) m.calls}]}
                               | _ -> f) sh.fields}]
                           | t -> t in
                         unreceived (definition declarations b ys) <> unreceived (definition declarations a xs)
                       with Json.Error _ -> true)) wanted
              && generic_methods a xs ->
            explain site ("an instance of a declaration with generic methods at an instance of another: "
              ^ generic_instances_reason)
          | _ -> ())
       | None -> ());
      explain_record_at_index site env n expected;
      (* An array used as a record naming `length`. *)
      (match expected with
       | Some x when List.exists (function
             | Shape {elements=None;calls=[];fields;_} ->
               List.exists (fun (f:Semantic.field) -> f.name = Name "length") fields
             | _ -> false) (flat_atoms declarations x) ->
         (match flat_atoms declarations (resolve env n) with
          | [] -> ()
          | atoms -> if List.for_all array_atom atoms then
              explain site ("an array used as a record naming `length`: " ^ array_or_record_reason))
       | _ -> ());
      (* An open record `Array.isArray` found an array, used as one. *)
      explain_open_array site env n expected;
      (* A tuple expected at an iterable other than an array is read as the
         readonly array of its positions, whose prototype's iterator yields
         them: Lean checks the tuple within that view, and the view within
         the iterable. *)
      (match resolve env n, expected with
       | Atoms [Shape {elements=Some s;fields=[];indexes=[];calls=[]}],Some x
         when (s.required <> [] || s.optional_elements <> []) && s.rest = None
              && (match x with Atoms [Shape {elements=Some _;_}] -> false | _ -> true)
              && iterated_hint declarations x <> None ->
         array {required=[];optional_elements=[];
           rest=Some (combine (s.required @ s.optional_elements));readonly=true;dense=s.dense}
       | t,_ -> t)
    | Literal l -> literal_type l
    | Not e -> ignore (expr env e); bool
    | TypeofTest (_,_,e) -> ignore (expr env e); bool
    (* A string literal key is part of the test, not a claim site. *)
    | HasKey ({node=Literal (LString _);_},e) -> ignore (expr env e); bool
    | HasKey (k,e) -> ignore (expr env k); ignore (expr env e); bool
    | InstanceTest (_,e,proto) -> ignore (expr env e); ignore (expr env proto); bool
    (* A comparison is a Boolean; `+` with a string operand is a string;
       other arithmetic is of its operands' numeric family, bigint where the
       left one is all bigints, else number. *)
    | Arith (op,l,r) ->
      let left = expr env l in let right = expr env r in
      if relational op then begin
        (* Operands both numbers, both bigints or both strings are compared
           without a conversion; any other may be converted. *)
        let comparable t = match (try declared_head declarations [] t with Json.Error _ -> t) with
          | Atoms atoms -> List.for_all (function
              | Num | NumLit _ | Str | StrLit _ | Bigint | BigintLit _ -> true
              | _ -> false) atoms
          | Rigid _ | Union _ | Meet _ -> true in
        if not (comparable left && comparable right) then
          explain e.pos ("a relational comparison of operands that may not both be numbers or both \
            strings: " ^ relational_reason);
        bool
      end else operation_result declarations op left right
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
      let right = expr ~expected:contract env rhs in
      (match List.assoc_opt n !evolving with
       | Some (key,false) -> evolve key right
       | _ -> ());
      union (without_nullish current) right
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
        | _,Some (i,_,_,_) -> i
        | _,None -> 1 + List.fold_left (fun m (i,_,_) -> max m i) (-1) targets in
      let required = List.init width (fun i -> match List.find_opt (fun (j,_,_) -> j=i) targets,rest with
        | Some (_,n,Some _),_ -> union (contract n) (Atoms [Undef])
        | Some (_,n,None),_ -> contract n
        | None,Some (start,_,n,_) when i >= start ->
          (match declared_head declarations [] (contract n) with
           | Atoms [Shape {elements=Some s;_}] ->
             (match List.nth_opt s.required (i-start) with
              | Some t -> t | None -> Option.value s.rest ~default:Semantic.top)
           | _ -> Semantic.top)
        | None,_ -> Semantic.top) in
      let actual = expr ~expected:(array {required;optional_elements=[];rest=None;readonly=false;dense=true}) env rhs in
      List.iter (fun (_,n,d) -> Option.iter (fun d -> ignore (expr ~expected:(contract n) env d)) d) targets;
      (* The rest's fresh array is claimed at its local's contract where that
         is an array, which a fresh array meets, else at the positions it
         takes. *)
      Option.iter (fun (start,span,n,slice) ->
        if slice then
          (* A slice: its `%RestFrom:k%`'s fresh array, at the instance of
             the elements from the rest's index on. *)
          let element = slice_element declarations start actual in
          expressions := {pos=span;type_=array {required=[];optional_elements=[];rest=Some element;readonly=false;dense=true};
            instantiation=Some ["T",ValueArgument element]} :: !expressions
        else
        let claim = match Semantic.array_element (contract n),declared_head declarations [] actual with
          | Some _,_ -> contract n
          | None,Atoms [Shape {elements=Some s;_}] when s.optional_elements=[] && s.rest=None ->
            array {required=List.filteri (fun i _ -> i >= start) s.required;
                   optional_elements=[];rest=None;readonly=false;dense=true}
          | _ -> unsupported "an array rest needs one tuple of required positions: the rest of an array of unknown length is a slice" in
        expressions := {pos=span;type_=claim;instantiation=None} :: !expressions) rest;
      actual
    | Equality (op,l,r) ->
      let lt = expr env l and rt = expr env r in
      if (op = StrictEqual || op = StrictUnequal) && (rigid_arm lt || rigid_arm rt) then
        explain site ("strict equality with a value of a type parameter: " ^ equality_reason);
      bool
    | Alloc fs ->
      let contract = match Option.bind expected (object_hint declarations []) with
        | Some shape -> Some shape
        | None -> Option.bind expected (fun t -> discriminated_record declarations t fs) in
      let fields = List.map (fun (name,e) ->
        let hint = Option.bind contract (fun s -> List.find_opt (fun (f:Semantic.field) -> f.name=name) s.fields) in
        (* A key the contract names is built at its member's type; any other
           at the index. *)
        let expected = match hint,contract with
          | Some (f:Semantic.field),_ -> Some f.read
          | None,Some shape -> Option.map (fun (i:Semantic.index_signature) -> i.value)
              (index_for shape name)
          | None,_ -> None in
        (match hint,e.node with
         | Some f,Literal LUndefined when f.optional && not (Semantic.admits_undefined f.read) ->
           explain site ("an optional field given `undefined`: " ^ exact_optional_reason)
         | _ -> ());
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
        {name;optional=false;read=t;write=Some t;host=false}) fs in
      (* Where the contract is a dictionary, or has optional fields, the
         literal is claimed with its exact keys: that own-key bound is what
         lets it meet an index, or an optional field it leaves out. A class
         instance, which holds its prototype, is claimed with its exact keys
         too: the bound is what says a method is not its own, so a read of it
         continues at the prototype. A writable index is never met through an
         own-key bound, since code holding it may add keys: a literal meant
         for one is allocated at the dictionary itself, each field at its
         index's type. *)
      (match contract with
       | _ when List.mem_assoc (Name proto_key) fs || List.mem e.pos !exact_allocs -> Atoms [Exact fields]
       | Some {indexes=(_::_ as indexes);fields=contract_fields;_}
         when List.exists (fun (i:Semantic.index_signature) -> i.writable <> None) indexes ->
         (* The contract's optional fields it leaves out, which it lacks. *)
         let absent = List.filter (fun (f:Semantic.field) -> f.optional && not f.host &&
           not (List.mem_assoc f.name fs)) contract_fields in
         Atoms [Shape {fields=fields @ absent;indexes;calls=[];elements=None}]
       | Some {indexes=_::_;_} -> Atoms [Exact fields]
       | Some {fields=contract_fields;_}
         when List.exists (fun (f:Semantic.field) -> f.optional) contract_fields -> Atoms [Exact fields]
       | _ -> record fields)
    | Build parts ->
      List.iter (fun (name,(e:expr)) -> if name = None then
        match (match quietly (fun () -> expr env e) with
               | Some t -> (try flat_atoms declarations t with Json.Error _ -> [])
               | None -> []) with
        | atoms when List.exists (function Shape {indexes=_::_;_} -> true | _ -> false) atoms ->
          explain site ("a spread of a dictionary: " ^ dictionary_spread_reason)
        | atoms when List.exists (function
            | Shape {fields;_} | Exact fields ->
              List.exists (fun (f:Semantic.field) -> not (string_key f) && not f.host) fields
            | _ -> false) atoms ->
          explain site ("a spread of an object with a symbol-keyed property: " ^ symbol_copy_reason)
        | _ -> ()) parts;
      let contract = Option.bind expected (object_hint declarations []) in
      (* A field is built at the type the contract names for it, else at its
         own, widened, as a literal's field is. *)
      let field_of (name,e) =
        let hint = Option.bind contract (fun s ->
          List.find_opt (fun (f:Semantic.field) -> f.name=Name name) s.fields) in
        let expected = Option.map (fun (f:Semantic.field) -> f.read) hint in
        let inferred = expr ?expected env e in
        let t = Option.value expected ~default:(widen inferred) in
        ({name=Name name;optional=false;read=t;write=Some t;host=false} : Semantic.field) in
      let group fs = {afields=fs;exact=true;index=None} in
      let merge alts b = List.concat_map (fun a -> List.map (merge_alternative a) b) alts in
      let alts,fields = List.fold_left (fun (alts,fields) (name,e) -> match name with
        | Some name -> alts,fields @ [field_of (name,e)]
        | None ->
          let alts = match alts with
            | None -> [group fields]
            | Some alts -> if fields = [] then alts else merge alts [group fields] in
          mark_exact e;
          Some (merge alts (source_alternatives declarations [] (expr env e))),[]) (None,[]) parts in
      let alts = match alts with
        | None -> [group fields]
        | Some alts -> if fields = [] then alts else merge alts [group fields] in
      (* Expected at a union of records, an alternative whose keys are one
         arm's, with a written field that arm types otherwise than the field
         is built, is refused by name. *)
      (match expected,contract with
       | Some t,None when List.exists (fun (n,_) -> n = None) parts ->
         let arms = record_arms declarations [] t in
         let names fs = List.sort compare (List.map (fun (f:Semantic.field) -> f.name) fs) in
         let written = List.filter_map (fun (n,_) -> Option.map (fun n -> Name n) n) parts in
         if List.exists (fun (a:alternative) ->
             match List.filter (fun (s:shape) -> s.indexes = [] && names s.fields = names a.afields
                                  && List.for_all (fun (f:Semantic.field) -> not f.optional) s.fields) arms with
             | [arm] -> List.exists (fun (f:Semantic.field) -> List.mem f.name written &&
                 List.exists (fun (g:Semantic.field) -> g.name = f.name && g.read <> f.read) arm.fields) a.afields
             | _ -> false) alts
         then explain site ("a spread with a written field that the arms of the expected union type \
           differently: " ^ copy_field_reason)
       | _ -> ());
      combine (List.map alternative_type alts)
    (* `Object.assign(t, ...sources)`: each source copied over what the
       target and the sources before it give, as a spread is; a literal
       source is claimed with its exact keys, which says it owns no
       `__proto__`, a key the copy would set through a setter. *)
    | ObjectAssign (target,sources) ->
      mark_exact target;
      let merge alts b = List.concat_map (fun a -> List.map (merge_alternative a) b) alts in
      let alts = List.fold_left (fun alts (s:expr) ->
        mark_exact s;
        merge alts (source_alternatives declarations [] (expr env s)))
        (source_alternatives declarations [] (expr env target)) sources in
      combine (List.map alternative_type alts)
    | ArrayLiteral es ->
      (* One array arm of the expected type is the literal's contract: an
         optional array parameter, `readonly T[] | undefined`, is its array;
         a declaration's, such as a tuple alias at arguments, its equation's. *)
      let arrays = match expected with
        | Some (Atoms atoms) -> List.concat_map (fun atom -> match atom with
          | Shape {elements=Some s;_} -> [s]
          | Named _ ->
            (match (try Some (declared_head declarations [] (Atoms [atom])) with Json.Error _ -> None) with
             | Some (Atoms heads) -> List.filter_map (function Shape {elements=Some s;_} -> Some s | _ -> None) heads
             | _ -> [])
          | _ -> []) atoms
        | _ -> [] in
      let contract = match expected,arrays with
        | _,[s] -> Some s
        | _,_::_::_ when discriminated_array declarations arrays es <> None ->
          discriminated_array declarations arrays es
        | Some expected,_ ->
          Option.map (fun t -> {required=[];optional_elements=[];rest=Some t;readonly=true;dense=true})
            (iterated_hint declarations expected)
        | None,_ -> None in
      let types = List.mapi (fun i e ->
        let expected = Option.bind contract (fun s -> match List.nth_opt (s.required @ s.optional_elements) i with
          | Some t -> Some t | None -> s.rest) in expr ?expected env e) es in
      (match contract with
        | Some s -> array s
        | None -> array {required=[];optional_elements=[];rest=Some (widen (combine types));readonly=false;dense=true})
    (* A field a guard found holding less than its type is read at that. *)
    | Read (({node=Id name;_} as o),Name field) when List.mem_assoc (field_key name field) env ->
      let known = binding_type (List.assoc (field_key name field) env) in
      if List.mem (name,field) !undefined_fields then
        explain site ("an optional key found `undefined`, read at `undefined`: " ^ absent_key_reason);
      ignore (expr env o); known
    | Read ({node=Id name;_} as e,n) when List.mem name !unknown_instance_tests ->
      (match expr env e with
       | Atoms xs as t when List.mem Top xs ->
         (try field_type declarations [] t n with Json.Error _ -> unsupported unknown_instance_reason)
       | t -> field_type declarations [] t n)
    (* A `let` holding a union of objects is not narrowed by a test of its
       object: what a cell is known to hold is a union of primitives
       (`holding`), and an object's fields may change through an alias. A
       member only some arms have is refused by that reason. *)
    | Read (({node=Id name;_} as e),n)
      when (match List.assoc_opt name env with Some (Storage _) -> true | _ -> false) ->
      let t = expr env e in
      (try field_type declarations [] t n with Json.Error m
        when String.length m >= 27 && String.sub m 0 27 = "unsupported: missing field " ->
        unsupported ("a read of " ^ key_text n ^ " on a `let` holding a union of objects, some without it: \
          a test does not narrow a cell holding an object, whose known contents are primitive values")
        | Json.Error m when m = "unsupported: field read on non-object" ->
          unsupported ("a cell read at its contract: a read of " ^ key_text n ^ " on a `let` or an assigned \
            parameter holding a primitive beside an object, which a test does not narrow: what a cell is known \
            to hold is primitive values or merely no `undefined`"))
    | Read (e,n) ->
      let receiver = expr env e in
      if not (List.mem site !method_callees) && method_member declarations receiver n then
        explain site ("a method '" ^ key_text n ^ "' read off its object is not a function value: " ^ extraction_reason);
      (match e.node,n with
       | Id o,Name k when List.mem (o,k) !dictionary_keys && expected <> None ->
         explain site ("a read of a key `in` found in a dictionary: " ^ dictionary_presence_reason)
       | Id o,Name k when List.mem (o,k) !undefined_fields && expected <> None ->
         explain site ("an optional key found `undefined`, read at `undefined`: " ^ absent_key_reason)
       | _ -> ());
      refuse_length_union declarations site receiver n;
      (match expected with
       | Some x when n = Name "length"
           && List.exists (function
               | Shape {elements=Some {rest=None;readonly=false;_};_} -> true
               | _ -> false) (flat_atoms declarations receiver)
           && (match flat_atoms declarations x with
               | [] -> false
               | wanted -> List.for_all (function NumLit _ -> true | _ -> false) wanted) ->
         explain site ("the `length` of a mutable tuple read at its arity: " ^ mutable_tuple_length_reason)
       | _ -> ());
      (match e.node with
       | Id name when List.mem name !open_array_tests ->
         (try field_type declarations [] receiver n with Json.Error m ->
           explain site ("a member of `unknown` read as one of an array after `Array.isArray`: " ^ open_array_reason);
           (match receiver with
            | Atoms atoms when String.length m >= 27 && String.sub m 0 27 = "unsupported: missing field "
                && List.exists (function Shape {elements=Some _;_} -> true | _ -> false) atoms ->
              unsupported ("a read of " ^ key_text n ^ " on a union of an array and a record that does not state it: \
                a test that the value is an array keeps the record, a value of which may be an array carrying its keys")
            | _ -> Json.fail m))
       | _ ->
         (try field_type declarations [] receiver n with Json.Error m
           when String.length m >= 27 && String.sub m 0 27 = "unsupported: missing field "
                && (match receiver with
                    | Atoms atoms -> List.exists (function Shape {elements=Some _;_} -> true | _ -> false) atoms
                    | _ -> false) ->
           (* `Array.isArray` keeps a record arm on both outcomes: a value of
              the record's type may be an array carrying its keys. *)
           unsupported ("a read of " ^ key_text n ^ " on a union of an array and a record that does not state it: \
             a test that the value is an array keeps the record, a value of which may be an array carrying its keys")
           (* A field holding an object or `null` (`undefined`), which a
              guard found an object: what a field is known to hold is a union
              of primitives, and an object's contents may change through an
              alias, so the guard leaves it at its type. *)
           | Json.Error m when m = "unsupported: field read on non-object"
               && (match e.node with Read ({node=Id _;_},_) -> true | _ -> false) ->
             unsupported ("a field read at its contract: a read of " ^ key_text n ^ " through a field holding \
               an object beside null or undefined, which a test does not narrow: what a field is known to hold \
               is a union of primitive values (DESIGN.md, \"Current-content assertions\")")))
    | Index (e,key) -> let receiver=expr env e in let key=expr env key in
      (match e.node with
       (* An element of `unknown` read after `Array.isArray`: the test
          narrows nothing there, so the read is of no object. *)
       | Id name when List.mem name !open_array_tests && receiver = top ->
         unsupported ("`unknown` used as an array after `Array.isArray`, read at an element: " ^ open_array_reason)
       | _ -> index_type declarations [] receiver key)
    (* The right side runs after the receiver and the key: it sees what they
       assigned. *)
    | IndexWrite (receiver,key,rhs) ->
      Option.iter (fun k -> Option.iter (evolve k) (quietly (fun () -> expr env rhs))) (evolving_array receiver);
      let t = expr env receiver in
      let key_type = expr env key in
      (match key_type with
       | Atoms [StrLit k] -> dictionary_growth site t (Name k)
       | Atoms [NumLit bits] -> Option.iter (fun k -> dictionary_growth site t (Name k)) (number_key bits)
       | _ -> ());
      let name = match key_type with Atoms [StrLit k] -> Some (Name k) | _ -> None in
      let value = expr (effects (effects env receiver) key) rhs in
      (match name with
       | Some name when adds env receiver t name -> added_contract declarations t name rhs value
       | _ -> value)
    | Write (receiver,field,rhs) ->
      let t = expr env receiver in
      dictionary_growth site t field;
      let value = expr (effects env receiver) rhs in
      if adds env receiver t field then added_contract declarations t field rhs value else value
    | Assign (n,rhs) ->
      if not (List.mem_assoc n env) && List.mem_assoc n module_functions then
        unsupported ("assignment to module function " ^ n);
      (match lookup env n with
      | Storage (contract,_) ->
        let t = expr ~expected:contract env rhs in
        (* A value that reads the binding is what it may be for anything the
           binding may hold: its contract. *)
        let written () = if reads n rhs
          then (match quietly (fun () -> expr (forget env) rhs) with None -> Some t | s -> s)
          else Some t in
        (match List.assoc_opt n !evolving with
         | Some (key,false) -> Option.iter (evolve key) (written ())
         | Some (key,true) -> Option.iter (evolve key) (Option.bind (written ()) (fun t -> Semantic.array_element t))
         | None -> ());
        t
      | Value _ -> unsupported "assignment to immutable binding")
    | Ctor {node=Lambda (None,[],ps,[],false,Some result,body);_} ->
      (* The constructor's body under its parameters; `new` passes it no
         receiver it reads, and runs it later, when a cell it captures holds
         what its contract admits. The class value's type is its construct
         signature. *)
      let inner = List.fold_left (fun env (n,t) -> extend env n (Value t)) (forget env) ps in
      let fresh = !fresh_constructor in
      fresh_constructor := false;
      if fresh then exact_allocs := tails body @ !exact_allocs;
      let allocated_type = match body.node with
        | BlockBody ss ->
          let returned = ref [] in
          ignore (!block_statements (Some result) returned inner ss);
          combine (List.rev !returned)
        | _ -> expr ~expected:result inner body in
      (* A class offered construct signatures giving other instances is
         claimed at them too, beside its own; Lean checks the body at each. *)
      let own = {call_effect=Unrestricted;quantified=[];receiver=Semantic.top;params=List.map snd ps;variadic=None;rest_pack=None;result} in
      let extra = Option.value (List.assoc_opt e.pos offered) ~default:[] in
      (* A fresh constructor gives, first, the instance it allocates. *)
      let fresh_sig = if fresh then [{own with result=allocated_type}] else [] in
      Atoms [Ctors (fresh_sig @ own :: List.filter (fun s -> s <> own) (List.sort_uniq compare extra))]
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
        (* A parameter a block body assigns is a cell holding its argument,
           at its annotation, as a function's is. *)
        let assigned = match body.node with
          | BlockBody ss -> List.exists (assigns n) ss
          | _ -> false in
        extend env n (if assigned then cell t else Value t)) env (List.mapi (fun i p -> i,p) ps) in
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
      (* A generic closure's own ground bounds hold in its body, as a generic
         function's do: a member read through a bounded binder reads the
         bound's member. *)
      let enclosing_bounds = !rigid_bounds in
      rigid_bounds := List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
        | Some (ValueArgument b) when not (Semantic.mentions_rigid b) -> Some (q.identity,b)
        | Some (ValueArgument (Rigid t)) when t <> q.identity -> Some (q.identity,Rigid t)
        | _ -> None) quantified @ enclosing_bounds;
      let body_type = Fun.protect ~finally:(fun () -> rigid_bounds := enclosing_bounds) (fun () ->
        expr ?expected:(if written <> None then written else contextual) inner body) in
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
      let values = List.filter_map (fun (name,b) -> match b with
        | Value _ -> Some name | Storage _ -> None) inner in
      (* Rest binding materializes a source array wrapper in the lowered
         body. Allocation is allowed by the effect but the initial checker
         cannot yet certify that wrapper; do not propose an unprovable effect. *)
      let call_effect = if not rest && heap_preserving_expr values body &&
        List.for_all (fun (_,d) -> heap_preserving_expr values d) defaults
        then PreservesInputHeap else Unrestricted in
      let own = match element with
        | Some element -> variadic_arrow ~call_effect ~quantified ~receiver params element result
        | None -> quantified_arrow ~call_effect ~receiver quantified params result in
      (* A named closure passed where more parameters are offered is claimed
         at those signatures too, beside its own: calls through it discard
         the actuals past its parameters, and Lean checks its body at each. *)
      (* A closure literal expected at one signature binding more parameters
         than it does, whose leading positions its own take, is offered it
         where it is created, as a named one is offered by its uses. *)
      (* Expected at several signatures (a method whose rest is a union of
         tuples, `next(...[value]: [] | [TNext])`), it is offered each that
         binds more, beside its own, which takes the others. *)
      let implements_arity (s:Semantic.signature) =
        s.quantified=[] && s.variadic=None && List.length s.params = List.length ps in
      let longer (s:Semantic.signature) = s.quantified=[] && s.rest_pack=None
        && (match s.variadic with
            | None -> List.length s.params > List.length ps
            | Some _ -> List.length s.params >= List.length ps)
        && List.for_all2 plausible_subtype
             (List.filteri (fun i _ -> i < List.length ps) s.params) (List.map snd ps) in
      let from_context = match expected with
        | Some t -> (match (try declared_head declarations [] t with Json.Error _ -> t) with
          | Atoms [Shape {calls=[s];fields=[];indexes=[];elements=None}] when longer s -> [s]
          | Atoms [Shape {calls=(_::_::_ as calls);fields=[];indexes=[];elements=None}]
            when not (List.for_all implements_arity calls) -> List.filter longer calls
          | _ -> [])
        | None -> [] in
      let offered_here = match List.assoc_opt e.pos offered, from_context with
        | None,[] -> None
        | extra,context -> Some (Option.value extra ~default:[] @ context) in
      let own = match offered_here, own with
        | Some extra, Atoms [Shape ({calls=[call];_} as shape)] when quantified=[] && element=None ->
          Atoms [Shape {shape with calls=call :: List.filter (fun s -> s <> call)
            (List.sort_uniq compare (List.map (fun s -> {s with call_effect}) extra))}]
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
      (* An evolving array's `push` and `unshift` add their arguments. *)
      (match callee.node with
       | Read (o,Name ("push" | "unshift")) when spreads = [] ->
         Option.iter (fun k -> List.iter (fun a ->
           Option.iter (evolve k) (quietly (fun () -> expr env a))) args) (evolving_array o)
       | _ -> ());
      (* Explicit type arguments fix the callee's leading binders; the others
         are inferred from the receiver and the actuals. Lean checks that the
         claimed instance agrees with them. *)
      let infer_explicit ~receiver ?expected (signature:Semantic.signature) actuals =
        if List.length type_args > List.length signature.quantified then
          unsupported "more explicit type arguments than the callee has binders";
        if type_args = [] && accumulating_binder signature then
          explain (e:expr).pos ("a call instantiating a binder its result accumulates in an application \
            (`catch`'s `Promise<T | TResult>`): " ^ accumulating_binder_reason)
        else if type_args = [] && wrapped_binder signature then
          explain (e:expr).pos ("a call inferring a binder written beside an application of it (`R | PromiseLike<R>`): "
            ^ wrapped_binder_reason);
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
      method_callees := callee.pos :: !method_callees;
      (* A binder's value is called at its bound, as it is read there. *)
      let callee = match declared_head declarations [] (expr env callee) with
        | Rigid r -> (match rigid_bound r with
          | Some b -> declared_head declarations [] b
          | None -> Rigid r)
        | t -> t in
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
        (* Arity adaptation may retain a guarantee already inferred for the
           value; adding ignored parameters cannot manufacture an effect.
           Overload selection uses this type, never the callback's body. *)
        let supplies_effect (offered:Semantic.signature) =
          offered.call_effect=Unrestricted ||
          let known = match arg.node with
            | Id name -> quietly (fun () -> resolve env name)
            | _ -> List.find_map (fun (p:expression) ->
                if p.pos=arg.pos then Some p.type_ else None) !expressions in
          match known with
          | Some (Atoms [Shape {calls;_}]) -> List.exists (fun (s:Semantic.signature) ->
              s.call_effect=offered.call_effect) calls
          | _ -> false in
        let offered arity = match param with
          | Atoms [Shape {calls=[offered];fields=[];indexes=[];elements=None}] as t
              when offered.quantified=[] && offered.rest_pack=None && supplies_effect offered
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
           | Atoms [Shape {calls=[o];fields=[];indexes=[];elements=None}]
               when supplies_effect o -> closure_offer n o
           | _ -> None)
        (* A class value at a generic call's construct parameter, known only
           once the call's instance is: offered as where the parameter's type
           is expected. *)
        | Id n when List.mem_assoc n !classes ->
          Some (fun () -> offer_class (List.assoc n !classes) param)
        (* Any other named function is its annotated signature: one binding
           more parameters is not offered it. *)
        | Id n ->
          explain_open_array arg.pos env n (Some param);
          explain_record_at_index arg.pos env n (Some param);
          (match param, (try Some (resolve env n) with Json.Error _ -> None) with
           | Atoms [Shape {calls=[o];_}], Some (Atoms [Shape {calls=[own];fields=[];indexes=[];elements=None}])
               when List.length o.params > List.length own.params || (o.variadic <> None && own.variadic = None) ->
             explain arg.pos ("a named function where a signature binding more parameters is expected: "
               ^ module_arity_reason)
           | _ -> ());
          None
        | _ -> None in
      let param_at (s:Semantic.signature) i = match List.nth_opt s.params i with
        | Some p -> Some p
        | None -> s.variadic in
      (* Several candidate signatures (overloads, or a union's arms): an
         actual is built at a parameter every candidate states alike, as a
         single signature's actuals are, and typed on its own otherwise. *)
      let shared_actuals (candidates:Semantic.signature list) =
        List.mapi (fun i arg ->
          match List.map (fun s -> param_at s i) candidates with
          | Some p :: rest when List.for_all (fun q -> q = Some p) rest ->
            expr ~expected:p env arg,Some p
          | _ -> expr env arg,None) args in
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
           if List.mem i spreads then
             Option.iter (fun arm ->
               explain (e:expr).pos ("a spread argument of " ^ arm ^ ": " ^ iteration_reason))
               (non_array_arm declarations [] (expr env e))
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
           optional_elements=[];rest=None;readonly=false;dense=true} in
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
         (* The binders the receiver fixes alone (`push` of a `T[]`, the
            array's `T`): a fresh literal at a parameter they instantiate is
            built at it, as TypeScript's contextual type of it is. A hint:
            Lean checks the actual at the instance. *)
         let fixed = lazy (if not (Semantic.mentions_rigid signature.receiver) then None else
           try Some (Inference.infer ~expand:(expand_named declarations) ~receiver:receiver_type
                  {signature with params=[];variadic=None} []).substitution
           with Json.Error _ -> None) in
         let built (arg:expr) i = match arg.node,Lazy.force fixed,param_at signature i with
           | (Alloc _ | ArrayLiteral _),Some solution,Some p
             when not (List.exists (fun (_,a) -> a = ValueArgument top) solution) ->
             let t = Inference.substitute solution p in
             if Semantic.mentions_rigid t then None else Some t
           | _ -> None in
         let actuals = List.concat (List.mapi (fun i arg ->
           let actual = expr ?expected:(if List.mem i spreads then None else built arg i) env arg in
           if not (List.mem i spreads) then [actual]
           else if i < List.length signature.params then
             unsupported "a spread cannot fill fixed parameters of a variadic signature"
           else match Semantic.tuple_positions ~readonly:true actual, Semantic.array_element ~readonly:true actual with
             | Some positions,_ -> positions
             | None,Some element -> [union element (Atoms [Undef])]
             | _ -> unsupported "generic spread requires an array or a tuple of required positions") args) in
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
      (* Into fixed parameters, each spread's elements are read once every
         actual is evaluated, where the call reads them: so no actual after
         the first spread may run code. *)
      let last_only = spreads = [List.length args - 1] in
      if spread && not last_only then
        List.iteri (fun i (a:expr) ->
          if i > List.fold_left min max_int spreads then match a.node with
            | Id _ | Literal _ -> ()
            | _ -> unsupported "a spread into fixed parameters followed by an actual that runs code") args;
      (* A call writes a prefix of the declared positions. The rest are omitted,
         which is admissible exactly when each of their contracts admits
         `undefined`; Lean checks that premise for itself. *)
      (* A spread argument stands for the required elements of its operand's
         tuple contract: the call writes those positions. *)
      (* Counting the positions must not state the operand's claim twice, so a
         name is read from the environment and anything else is typed once,
         here, and not again below. *)
      let spread_types = List.map (fun i -> i,lazy (match List.nth args i with
        | { node = Id name; _ } -> resolve env name
        | operand -> expr env operand)) spreads in
      let spread_positions i =
        match Semantic.tuple_positions (Lazy.force (List.assoc i spread_types)) with
        | Some elements -> List.length elements
        | None -> unsupported "a spread argument needs a tuple of required positions" in
      (* The position each actual starts at: a spread writes as many as its
         tuple has. *)
      let offsets = List.rev (snd (List.fold_left (fun (at,acc) i ->
        (at + (if List.mem i spreads then spread_positions i else 1)),at :: acc)
        (0,[]) (List.init (List.length args) Fun.id))) in
      let written_positions =
        List.fold_left (+) 0 (List.mapi (fun i _ ->
          if List.mem i spreads then spread_positions i else 1) args) in
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
        List.iteri (fun i (e:expr) ->
          if List.mem i spreads then
            (match e.node with Id _ -> ignore (expr env e) | _ -> ())
          else let expected = match List.nth_opt signature.params (List.nth offsets i) with
            | Some t -> t
            | None -> (match signature.variadic with
              | Some t -> t
              | None -> unsupported "call has too many arguments") in
            ignore (expr ~expected env e)) args;
        offer signature;
        signature.result
      | Atoms [Shape {calls=[signature];_}]
          when signature.quantified<>[] && callable signature && (last_only || not spread) ->
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
           instantiates `K` at the tuple, not at `number[]`. A bound with one
           tuple arm of the literal's length among others, through its
           declarations (`S extends [number, number] | string`), is that arm,
           as TypeScript's contextual type makes the literal a tuple. *)
        let tuple_bound (arg:expr) = function
          | Rigid r -> (match List.find_opt (fun (q:Semantic.quantifier) -> q.identity = r)
                          signature.quantified with
            | Some {bound=Some (ValueArgument (Atoms [Shape {elements=Some {rest=None;_};fields=[];
                calls=[];indexes=[]}] as t));_} -> Some t
            | Some {bound=Some (ValueArgument t);_} ->
              let length = match arg.node with ArrayLiteral es -> List.length es | _ -> -1 in
              (match List.filter (function
                 | Shape {elements=Some {rest=None;required;optional_elements;_};fields=[];calls=[];indexes=[]} ->
                   List.length required <= length
                   && length <= List.length required + List.length optional_elements
                 | _ -> false) (flat_atoms declarations t) with
               | [arm] -> Some (Atoms [arm])
               | _ -> None)
            | _ -> None)
          | _ -> None in
        (* A fresh array literal at a parameter whose every binder is
           bounded by literal types is built at the parameter read at those
           bounds, as TypeScript keeps a fresh literal's literal type where a
           binder's constraint names literals: `pick<K extends 0 | 1>(e:
           Array<[K, number]>)` called with `[[0, 1]]` builds a pair whose
           first position is `0 | 1`, and `K` is inferred from it. *)
        let literal_bounds p =
          let literal = function
            | Nul | Undef | True | False | NumLit _ | StrLit _ | BigintLit _ -> true
            | _ -> false in
          let solution = List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
            | Some (ValueArgument (Atoms (_::_ as atoms) as t)) when List.for_all literal atoms ->
              Some (q.identity,ValueArgument t)
            | _ -> None) signature.quantified in
          if solution = [] then None
          else
            let t = Inference.substitute solution p in
            if Semantic.mentions_rigid t then None else Some t in
        let dictionary_bound = function
          | Rigid r -> (match List.find_opt (fun (q:Semantic.quantifier) -> q.identity = r)
                          signature.quantified with
            | Some {bound=Some (ValueArgument t);_} ->
              (match object_hint declarations [] t with
               | Some sh when List.exists (fun (i:Semantic.index_signature) -> i.keys = Semantic.Strings) sh.indexes -> Some t
               | _ -> None)
            | _ -> None)
          | _ -> None in
        (* A spread's actuals are its tuple's positions, which Lean reads
           and checks each at its parameter. *)
        let actuals=List.concat (List.mapi (fun i (arg:expr) ->
          if List.mem i spreads then begin
            (match arg.node with Id _ -> ignore (expr env arg) | _ -> ());
            match Semantic.tuple_positions (Lazy.force (List.assoc i spread_types)) with
            | Some positions -> positions
            | None -> unsupported "a spread argument needs a tuple of required positions"
          end else [match param_at signature (List.nth offsets i),stated with
          | Some p,_ when not (Semantic.mentions_rigid p) -> expr ~expected:p env arg
          | Some p,Some solution -> expr ~expected:(Inference.substitute solution p) env arg
          | Some p,None when (match arg.node with ArrayLiteral _ -> true | _ -> false)
                              && tuple_bound arg p <> None ->
            expr ?expected:(tuple_bound arg p) env arg
          | Some p,None when (match arg.node with ArrayLiteral _ -> true | _ -> false)
                              && literal_bounds p <> None ->
            expr ?expected:(literal_bounds p) env arg
          (* An object literal at a binder bounded by a union with one
             dictionary arm, `T extends Json`, is built at that arm, with
             its exact keys, as a record held in a variable could not be:
             TypeScript checks the fresh literal against the constraint. *)
          | Some p,None when (match arg.node with Alloc _ -> true | _ -> false)
                              && dictionary_bound p <> None ->
            expr ?expected:(dictionary_bound p) env arg
          | p,_ ->
            (match arg.node with Id n -> explain_open_array arg.pos env n p | _ -> ());
            expr env arg]) args) @
          List.init (max 0 (List.length signature.params - written_positions)) (fun _ -> Atoms [Undef]) in
        explain_thenable e target signature actuals;
        let substitution,result = infer_explicit ~receiver:receiver_type ?expected signature actuals in
        instance_of ~declared:callee target substitution;
        offer ~substitute:(Inference.substitute substitution) signature;
        if not (method_read target) then
        instantiations := (e.pos,List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
          substitution) :: !instantiations;
        result
      (* Quantified overloads use the same proposal/validation split as one
         quantified signature. Type the actuals once, infer an instance for
         each arity-compatible signature, then offer one matching contract.
         Only that signature is projected from the scheme; Lean independently
         checks both the projection and the call, including its receiver.
         A nonmatching proposal may still be emitted to locate the failed
         obligation; it is never acceptance. *)
      | Atoms [Shape ({calls=(_::_::_ as calls);_} as shape)]
          when not spread && List.for_all (fun (s:Semantic.signature) ->
            s.quantified<>[] && s.variadic=None && s.rest_pack=None) calls ->
        let usable = List.filter callable calls in
        let actuals = shared_actuals usable in
        let proposals = List.filter_map (fun (s:Semantic.signature) ->
          Option.map (fun (substitution,result) -> s,substitution,result)
            (quietly (fun () -> infer_explicit ~receiver:receiver_type ?expected s
              (List.map fst actuals @ List.init (max 0 (List.length s.params - List.length args))
                (fun _ -> Atoms [Undef]))))) usable in
        let matches_actuals ((s:Semantic.signature),substitution,_) =
          let at = Inference.substitute substitution in
          List.for_all Fun.id (List.mapi (fun i (arg,(t,_)) ->
            match List.nth_opt s.params i with
            | Some p -> plausible_subtype t (at p) || offer_to arg (at p) <> None
            | None -> false) (List.combine args actuals)) in
        let matching = List.filter matches_actuals proposals in
        let preferred = match List.find_opt (fun ((s:Semantic.signature),substitution,_) ->
            plausible_subtype receiver_type (Inference.substitute substitution s.receiver)) matching with
          | Some p -> Some p
          | None -> List.nth_opt matching 0 in
        (match preferred,proposals with
         | Some (s,substitution,result),_ | None,((s,substitution,result)::_) ->
           instance_of ~declared:(Atoms [Shape {shape with calls=[s]}]) target substitution;
           offer ~substitute:(Inference.substitute substitution) s;
           if not (method_read target) then
             instantiations := (e.pos,List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
               substitution) :: !instantiations;
           result
         | None,[] -> unsupported "quantified overloads have no inferable arity-compatible instance")
      (* Several advertised signatures on one value. The actuals are built
         as the usable signatures agree (`shared_actuals`), and the signature
         whose domains they match is proposed. Lean selects the row it checks
         and re-checks every argument obligation. *)
      | Atoms [Shape {calls=(_::_::_ as calls);_}]
          when List.for_all (fun (s:Semantic.signature) -> s.quantified=[]) calls
               && (last_only || not spread) ->
        no_type_arguments ();
        let usable = List.filter callable calls in
        let actuals = shared_actuals usable in
        (* A closure an offer would claim at the parameter matches it, as
           does an actual built at it. *)
        let matching = List.filter (fun (s:Semantic.signature) ->
          List.for_all Fun.id (List.mapi (fun i (arg,(t,built)) -> match param_at s i with
            | Some p -> built = Some p || plausible_subtype t p || offer_to arg p <> None
            | None -> false) (List.combine args actuals))) usable in
        (match matching,usable with
         | s :: _,_ -> offer s; s.result
         | [],(first :: rest) when List.for_all (fun (s:Semantic.signature) ->
             s.result = first.result) rest -> first.result
         | _ -> unsupported "overloaded call needs a signature its arguments match")
      (* A union of callables: the call is one of its arms' calls, whichever
         the value is, so it is valid when every arm takes the actuals, and
         its value is the union of the arms' results. The actuals are built
         as the arms agree (`shared_actuals`); Lean splits the saved callee
         and checks the call once per arm. *)
      | Atoms (_::_::_ as arms) when not spread && List.for_all (function
          | Semantic.Shape {calls=[s];_} -> s.quantified=[] && s.variadic=None
              && s.rest_pack=None && callable s
          | _ -> false) arms ->
        no_type_arguments ();
        let signatures = List.filter_map (function
          | Semantic.Shape {calls=[s];_} -> Some s | _ -> None) arms in
        ignore (shared_actuals signatures);
        List.fold_left (fun acc (s:Semantic.signature) -> union acc s.result)
          (Atoms []) signatures
      (* JavaScript drops actuals past the parameters, but the calculus's call
         takes no more actuals than its signature's positions. *)
      | Atoms [Shape {calls=[{variadic=None;rest_pack=None;params;_}];_}]
          when written_positions > List.length params ->
        unsupported "a call writes more positions than its callee's parameters, which TypeScript rejects"
      (* `(() => R) & { a: T }` is a function carrying fields, the model's
         callable object; the meet of an arrow and a record forms none. *)
      | Meet _ -> unsupported "a call of an intersection of a function type and a record, a callable with fields, which an annotation's meet does not form"
      | Atoms kinds when List.mem Callable kinds && List.for_all (function
          | Callable | Ctors [] -> true | _ -> false) kinds ->
        let location = match site with
          | Json.Array [Json.Number first;Json.Number last] -> "[" ^ first ^ "," ^ last ^ ")"
          | _ -> unsupported "call has an invalid source span" in
        unsupported ("call at " ^ location ^ ": value has no admitted call signature")
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
      (* A target of several signatures, `next(...[value]: [] | [TNext])`, is
         bound at the first that takes the prefix: the bound function's claim
         is one signature, which Lean selects among the target's. *)
      let fits (s:Semantic.signature) = s.quantified=[] && s.rest_pack=None && (s.variadic<>None
        || List.length args<=List.length s.params) in
      let callee = match callee with
        | Atoms [Shape ({calls=_::_::_ as calls;_} as shape)] when List.exists fits calls ->
          Atoms [Shape {shape with calls=[List.find fits calls]}]
        | t -> t in
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
         | Some element -> variadic_arrow ~call_effect:signature.call_effect rest element signature.result
         | None -> arrow ~call_effect:signature.call_effect rest signature.result)
      | _ -> unsupported "bind requires a single arrow and a valid argument prefix")
    | Conditional (c,a,b) -> ignore (expr env c);
      let left = expr ?expected (branch env c true) a in
      let right = expr ?expected (branch env c false) b in union left right
    | Coalesce (a,b) -> let left=expr env a in let right=expr ?expected env b in
      if expected <> None && rigid_arm left then
        explain site ("`??` on a value of a type parameter: its values other than null and undefined are \
          the meet `T & {}`, but no rule narrows a parameter row to its meet with the non-nullish values");
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
    | Cast (kind,annot,e) ->
      (match kind,e.node with
       | "nonNull",Index (_,{node=Id k;_}) when List.mem k !for_in_keys ->
         explain site ("a non-null assertion on a read at a for...in key: " ^ for_in_key_reason)
       | _ -> ());
      let actual=expr ?expected:annot env e in
      (match kind,annot with
        | "nonNull",None -> without_nullish actual
        | "satisfies",Some _ -> actual
        | "as",Some target -> target
        | _ -> unsupported "cast form")
    (* A closure's statements: the union of what its `return`s give, each
       checked at the closure's result where it has one. *)
    | BlockBody ss ->
      let returned = ref [] in
      ignore (!block_statements expected returned env ss);
      combine (List.rev !returned) in
    (* Block wrappers correspond to statement entries, not expression sites. *)
    (match e.node with
      | BlockBody _ -> ()
      | _ -> expressions := {pos=e.pos;type_=t;
          instantiation=List.assoc_opt e.pos !instantiations} :: !expressions); t
  (* A pattern binding [target] to a value of [t], in pattern order: a
     property at its field's read, an element at its position's, a rest at the
     tuple of the positions from its index on, claimed at its span; a
     default, which sees the earlier bindings, replaces the read's undefined
     slice. *)
  and bind ?(nested = false) env target t default =
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
    | PObject (props,rest) ->
      (* A nested pattern over a field holding an object beside `null`,
         which a guard found an object, reads it at its type. *)
      let read f = try field_type declarations [] t (Name f) with Json.Error m
        when nested && m = "unsupported: field read on non-object" ->
        unsupported ("a field read at its contract: a nested pattern's read of " ^ f ^ " through a field \
          holding an object beside null or undefined, which a test does not narrow: what a field is known \
          to hold is a union of primitive values (DESIGN.md, \"Current-content assertions\")") in
      let env = List.fold_left (fun env (f,target,d) ->
        bind ~nested:true env target (read f) d) env props in
      (match rest with
       | None -> env
       | Some (span,target) ->
         (* The source's other own enumerable properties, copied onto a fresh
            object: a merge dropping the properties' keys. *)
         let drop = List.map (fun (f,_,_) -> Name f) props in
         let sources = List.map (fun (a:alternative) ->
           {a with afields=List.filter (fun (f:Semantic.field) -> not (List.mem f.name drop)) a.afields})
           (source_alternatives declarations [] t) in
         let rest_t = combine (List.map (fun b ->
           alternative_type (merge_alternative {afields=[];exact=true;index=None} b)) sources) in
         expressions := {pos=span;type_=rest_t;instantiation=None} :: !expressions;
         bind env target rest_t None)
    | PArray (elems,rest) ->
      (* An array pattern reads an array's positions. Over another iterable
         (a string, a `Set`, an object with its own `[Symbol.iterator]`) it
         steps that iterable's iterator, which nothing here models. *)
      let position i = try index_type declarations [] t (number_literal (string_of_int i)) with Json.Error m
        when String.length m >= 27 && String.sub m 0 27 = "unsupported: missing field " ->
        unsupported "an array pattern over a value that may not be an array: it would step that value's own \
          iterator, which is not modeled; only an array's positions are read" in
      let env = List.fold_left (fun env (i,target,d) ->
        bind env target (position i) d) env elems in
      (match rest with
       | None -> env
       | Some (start,span,true,target) ->
         (* A slice: its `%RestFrom:k%`'s fresh array, at the instance of the
            elements from the rest's index on. *)
         let element = slice_element declarations start t in
         let rest_t = array {required=[];optional_elements=[];rest=Some element;readonly=false;dense=true} in
         expressions := {pos=span;type_=rest_t;instantiation=Some ["T",ValueArgument element]} :: !expressions;
         bind env target rest_t None
       | Some (start,span,false,target) ->
         let remaining = match declared_head declarations [] t with
           | Atoms [Shape {elements=Some s;_}] when s.optional_elements=[] && s.rest=None ->
             List.filteri (fun i _ -> i >= start) s.required
           | _ -> unsupported "an array rest needs one tuple of required positions: the rest of an array of unknown length is a slice" in
         let rest_t = array {required=remaining;optional_elements=[];rest=None;readonly=false;dense=true} in
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
    | {statement=Closing (_,body);_}::_ -> returns body
    | _ -> false
  and leaves l s = match s.statement with
    | Break (Some l') -> l = l'
    | If (_,a,b) -> List.exists (leaves l) (a @ b)
    | While (_,body,update) -> List.exists (leaves l) (body @ update)
    | ForOf (_,_,_,_,body) | Block (_,body) -> List.exists (leaves l) body
    | Try (body,handler,finalizer) -> List.exists (leaves l)
      (body @ (match handler with Some (_,h) -> h | None -> []) @ Option.value finalizer ~default:[])
    | Closing (close,body) -> List.exists (leaves l) (body @ close)
    | Declare _ | Destructure _ | Return _ | Effect _ | Throw _ | Break _ | Continue -> false in
  let after e env = effects env e in
  (* An assignment statement writes only the cell it names. *)
  let rec stirs_statement s = match s.statement with
    | Declare (_,bs) -> List.exists (fun (_,_,e) -> stirs e) bs
    | Destructure (target,d,init) -> List.exists stirs (init :: Option.to_list d @ pattern_defaults target)
    | Effect {node=Assign (_,rhs) | NullishAssign (_,_,rhs);_} -> stirs rhs
    | Return e | Effect e -> stirs e
    | If (c,a,b) -> stirs c || List.exists stirs_statement (a @ b)
    | While (c,body,update) -> stirs c || List.exists stirs_statement (body @ update)
    (* Each step of the loop calls its iteration intrinsic. *)
    | ForOf _ -> true
    | Block (_,body) -> List.exists stirs_statement body
    | Throw e -> stirs e
    | Try (body,handler,finalizer) -> List.exists stirs_statement
      (body @ (match handler with Some (_,h) -> h | None -> []) @ Option.value finalizer ~default:[])
    (* Closing calls the iterator's `return`. *)
    | Closing _ -> true
    | Break _ | Continue -> false in
  (* A point reached after any part of these statements ran: a cell they
     assign, or any cell where they may write one unseen, is known there by
     its contract. *)
  let havoc env body =
    if List.exists stirs_statement body then forget env
    else forget ~only:(fun n -> List.exists (assigns n) body) env in
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
      not (List.exists (fun (_,b) -> binding_type b = Atoms []) env))
      arrivals in
    match reachable with
    | [] ->
      (* Where every path that arrives knows a value of the empty type, the
         point is never reached, and so is what follows it: the fallback
         keeps that knowledge, so a later merge drops it too. *)
      (match List.find_map (List.find_opt (fun (n,b) ->
           not (is_field n) && binding_type b = Atoms [] && List.mem_assoc n fallback)) arrivals with
       | Some (n,b) -> List.map (fun (m,c) -> if m = n then m,b else m,c) fallback
       | None -> fallback)
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
    | ForOf (_,_,_,e,b) -> mentions n e || List.exists (stmt_mentions n) b
    | Try (b,h,f) -> List.exists (stmt_mentions n)
      (b @ (match h with Some (_,h) -> h | None -> []) @ Option.value f ~default:[])
    | Closing (c,b) -> List.exists (stmt_mentions n) (b @ c)
    | Break _ | Continue -> false in
  (* Whether [n] may reach a place other than the receiver of its own member
     reads and writes, as Lean's `escapesExpr` reads it: a binding, a field,
     an argument or the receiver of a call, a result, a closure. *)
  let rec escapes n (e:expr) = match e.node with
    | Id m -> m = n
    | Read ({node=Id _;_},_) -> false
    | Index ({node=Id _;_},key) -> escapes n key
    | Write ({node=Id _;_},_,rhs) -> escapes n rhs
    | IndexWrite ({node=Id _;_},key,rhs) -> escapes n key || escapes n rhs
    | Invoke ({node=Read ({node=Id m;_},_);_},args,_,_) -> m = n || List.exists (escapes n) args
    | ObjectAssign ({node=Id _;_},sources) -> List.exists (escapes n) sources
    | Lambda _ | Ctor _ -> mentions n e
    | _ -> List.exists (escapes n) (Source.children e) in
  (* Whether a statement among [ss] adds a key other than [keys] to the
     object [n] names: `n.k = e` or `n["k"] = e`. *)
  let rec grows_later n keys ss = List.exists (fun (s:stmt) -> match s.statement with
    | Effect {node=Write ({node=Id m;_},Name k,_);_}
    | Effect {node=IndexWrite ({node=Id m;_},{node=Literal (LString k);_},_);_} ->
      m = n && not (List.mem (Name k) keys)
    | Effect {node=ObjectAssign ({node=Id m;_},_::_);_} -> m = n
    | If (_,a,b) -> grows_later n keys a || grows_later n keys b
    | Block (_,b) -> grows_later n keys b
    | Try (b,h,f) -> grows_later n keys (b @ (match h with Some (_,h) -> h | None -> [])
        @ Option.value f ~default:[])
    | _ -> false) ss in
  (* The first use of an unannotated constant's fresh array, in the
     statements after its declaration: where it is the whole value expected
     at a type (an annotated constant's initializer, a returned value, an
     argument of a call to a function of one plain signature), that type;
     any other first use, none. `None` where it is not used. *)
  let rec first_use env n rest = Option.join (List.find_map Fun.id (uses env n rest))
  (* Each statement's use of the constant: `Some` of where its first
     mention in the statement is the whole value expected at a type, as
     [first_use] reads it. *)
  and uses env n rest =
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
      | Return e -> sink !block_result e
      | Effect e -> sink None e
      | _ -> if stmt_mentions n s then Some None else None in
    List.map at rest in
  let rec statements env ss =
    let rec record = function [] -> () | s :: rest -> Hashtbl.replace following s.span rest; record rest in
    record ss;
    List.fold_left (fun env s ->
    (* A grown local's exact keys are claimed only where nothing else can
       reach its object: from the first statement that may let it escape on
       (but a `return` of it, after which the body runs nothing), it is its
       record, so no other reference, and no callee that may add a key to a
       writable dictionary, learns which keys it lacks. *)
    let env = List.fold_left (fun env n ->
      let escaping = match s.statement with
        | Return {node=Id _;_} -> false
        | _ -> List.exists (escapes n) (Source.statement_children s) in
      if not escaping then env else begin
        exact_locals := List.filter ((<>) n) !exact_locals;
        List.map (fun (m,b) -> match b with
          | Value (Atoms atoms) when m = n -> m,Value (Atoms (List.map (function
              | Exact fields -> Shape {fields;indexes=[];calls=[];elements=None}
              | a -> a) atoms))
          | Value (Union ts) when m = n -> m,Value (Union (List.map (function
              | Atoms atoms -> Atoms (List.map (function
                  | Exact fields -> Shape {fields;indexes=[];calls=[];elements=None}
                  | a -> a) atoms)
              | t -> t) ts))
          | _ -> m,b) env
      end) env !exact_locals in
    let env = match s.statement with
      | While (c,body,update) -> loop_fix env c body update
      | ForOf _ -> forget env
      | _ -> env in
    (* A block has no entry of its own: its first statement's is. *)
    (match s.statement with
     | Block _ -> ()
     | _ -> entry env s.span);
    match s.statement with
    | Declare (mutable_,bs) -> List.fold_left (fun env (n,written,init) ->
      if String.ends_with ~suffix:".[[class]]" n then fresh_constructor := true;
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
      (* An evolving binding (TypeScript's evolving `any`): an unannotated
         `let` of `null` or `undefined` holds what is assigned to it, an
         unannotated `[]` the elements written into it. Its contract is the
         union of those, TypeScript's evolved type: a proposal, which Lean
         checks at every write. *)
      evolving := List.remove_assoc n !evolving;
      let committed = match written,init.node with
        | None,ArrayLiteral [] ->
          evolving := (n,(init.pos,true)) :: !evolving;
          Some (array {required=[];optional_elements=[];rest=Some (evolved init.pos);readonly=false;dense=true})
        | None,Literal (LNull | LUndefined) when mutable_ ->
          evolving := (n,(init.pos,false)) :: !evolving; committed
        | _ -> committed in
      (* A constant's object literal to which a later statement of its
         block adds a key is claimed with its exact keys: the bound says
         which keys it lacks, so a key added on one path only is optional
         where the paths join. *)
      exact_locals := List.filter ((<>) n) !exact_locals;
      (match mutable_,written,init.node with
       | false,None,Alloc fs when grows_later n (List.map fst fs)
             (Option.value (Hashtbl.find_opt following s.span) ~default:[]) ->
         exact_allocs := init.pos :: !exact_allocs;
         exact_locals := n :: !exact_locals
       (* A constant's object literal used whole where a type with an
          optional field it leaves out is expected is claimed with its exact
          keys, as a literal written there would be: the bound is what says
          it lacks the key. Not where it is also used as a writable
          dictionary. A proposal: Lean checks the bound at the allocation
          and every use against it. *)
       | false,None,Alloc fs ->
         let lacks_optional t = match object_hint declarations [] t with
           | Some {fields;indexes=[];_} -> List.exists (fun (f:Semantic.field) ->
               f.optional && not f.host && not (List.mem_assoc f.name fs)) fields
           | _ -> false in
         (* A holder of a writable dictionary some value meets may add
            keys, so no view learns from the bound which it lacks. *)
         let writable_dictionary t = match object_hint declarations [] t with
           | Some {indexes;_} -> List.exists (fun (i:Semantic.index_signature) ->
               match i.writable with Some (Atoms []) | None -> false | Some _ -> true) indexes
           | None -> false in
         let used = uses env n (Option.value (Hashtbl.find_opt following s.span) ~default:[]) in
         if List.exists (function Some (Some t) -> lacks_optional t | _ -> false) used
            && not (List.exists (function Some (Some t) -> writable_dictionary t | _ -> false) used) then
           exact_allocs := init.pos :: !exact_allocs
       | _ -> ());
      let initial = expr ?expected:(if committed <> None then committed else written) env init in
      if not mutable_ then named_closure n written init;
      let binding = match mutable_,written with
        (* TypeScript's declared type for an unannotated `let`: its
           initializer's type, widened, or an evolving one's evolved type.
           Lean checks the initializer and every assignment against it. *)
        | true,None ->
          (match init.node with
           | Literal (LNull | LUndefined) -> cell (union (widen initial) (evolved init.pos))
           | _ -> cell (widen initial))
        | true,Some contract -> cell contract
        (* A class's annotation is its own construct signature, which the
           parser writes; the class value's claim may offer more. *)
        | false,Some _ when (match init.node with Ctor _ -> true | _ -> false) -> Value initial
        (* A closure offered further signatures holds them beside its
           annotation's: the binding is the closure, claimed at all of them,
           which Lean checks against the annotation. *)
        | false,Some _ when List.mem_assoc init.pos offered -> Value initial
        | false,Some contract -> Value (assigned_arms declarations (arms declarations contract) init)
        (* An unannotated constant of a named union is held at its arms, as
           an annotated one is: a guard then keeps or drops each. *)
        | false,None -> Value (arms declarations initial) in
      extend (after init env) n binding) env bs
    (* The initializer, then each binding in pattern order: a property at its
       field's read, an element at its position's, a rest at the tuple of the
       positions from its index on, claimed at its span; a default, which
       sees the earlier bindings, replaces the read's undefined slice. *)
    | Destructure (target,default,init) ->
      let env = bind env target (expr env init) default in
      (* An array pattern reads its positions from a store, a step after
         which Lean keeps no fact of the heap: the fields' and cells'
         contents are known by their contracts again. *)
      let rec reads_store = function
        | PArray _ -> true
        | PName _ -> false
        | PObject (props,rest) -> List.exists (fun (_,t,_) -> reads_store t) props
            || (match rest with Some (_,t) -> reads_store t | None -> false) in
      if stirs_statement s || reads_store target then forget env else env
    | Return e -> !block_returned := expr ?expected:!block_result env e :: !(!block_returned); env
    (* An assignment statement leaves the cell holding the value written;
       `n ??= rhs`, the value it yields. *)
    | Effect ({node=Assign (n,rhs) | NullishAssign (n,_,rhs);_} as e) ->
      let t = expr env e in
      (match lookup env n with
       | Storage _ -> assign (after rhs env) n t
       | Value _ -> env)
    (* `Object.assign(o, …)` on a local: the local holds the copies. *)
    | Effect ({node=ObjectAssign ({node=Id n;_},_);_} as e)
      when (match List.assoc_opt n env with Some (Value _) -> true | _ -> false) ->
      let t = expr env e in
      let env = after e env in
      grown_locals := n :: !grown_locals;
      List.map (fun (m,b) -> if m=n then m,Value t else m,b) env
    | Effect ({node=Write ({node=Id n;_},_,_) | IndexWrite ({node=Id n;_},_,_);_} as e)
      when (match List.assoc_opt n env with Some (Value _) -> true | _ -> false) ->
      let t = binding_type (lookup env n) in
      let c = expr env e in
      let claimed (x:expr) = List.find_map (fun (y:expression) ->
        if y.pos = x.pos then Some y.type_ else None) !expressions in
      let receiver,name = match e.node with
        | Write (r,name,_) -> r,Some name
        | IndexWrite (r,key,_) -> r,(match claimed key with Some (Atoms [StrLit k]) -> Some (Name k) | _ -> None)
        | _ -> e,None in
      let before = env in
      let env = after e env in
      (match name with
       | Some name when adds before receiver t name ->
         grown_locals := n :: !grown_locals;
         List.map (fun (m,b) -> if m=n then m,Value (grown declarations t name c) else m,b) env
       | _ -> env)
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
    | ForOf (name,name_pos,iterate,iterable,body) ->
      (* The loop is the call of its iteration intrinsic on the iterable,
         claimed at the statement with its instance; the element, what the
         instance's step yields, at the name it binds. *)
      (match iterable.node with
       | Call ({node=Id "%ForIn%";_},_,_,_,_) -> for_in_keys := name :: !for_in_keys
       | _ -> ());
      let actual = expr env iterable in
      if iterate = "%Iterate%" then
        Option.iter (fun arm ->
          explain s.span ("a for...of loop over " ^ arm ^ ": " ^ iteration_reason))
          (non_array_arm declarations [] actual);
      let signature = match declared_head declarations [] (resolve env iterate) with
        | Atoms [Shape {calls=[signature];_}] -> signature
        | _ -> unsupported ("a for...of loop needs the " ^ iterate ^ " intrinsic") in
      let result,substitution = if signature.quantified = [] then signature.result,[] else
        let inferred = Inference.infer ~receiver:(Atoms [Undef]) signature [actual] in
        inferred.result,inferred.substitution in
      let element = match declared_head declarations [] result with
        | Atoms [Shape {calls=[{params=[];result;_}];_}] ->
          let yielded = match result with
            | Union ts -> ts
            | t -> [t] in
          (match List.concat_map (fun t -> match declared_head declarations [] t with
               | Atoms atoms -> List.filter_map (function
                   | Shape {fields;_} -> List.find_map (fun (f:field) ->
                       if f.name = Name "value" then Some f.read else None) fields
                   | _ -> None) atoms
               | _ -> []) yielded with
           | [t] -> t
           | _ -> unsupported (iterate ^ "'s step yields no one value"))
        | _ -> unsupported (iterate ^ " gives no step") in
      expressions := {pos=s.span;type_=result;
        instantiation=if signature.quantified = [] then None else
          Some (List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t) substitution)} :: !expressions;
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
    (* A program iterable's loop body. Its close runs after a `break` of the
       loop, a `return` or a throw out of the body, from any point of it: it
       knows each cell by its contract, and a `break` leaves the loop after
       it, knowing what a call leaves known. *)
    | Closing (close,body) ->
      let local after = List.filter (fun (n,_) -> List.mem_assoc n env) after in
      let marker = match !loops with (breaks,_) :: _ -> List.length !breaks | [] -> 0 in
      let completed = statements env body in
      (match !loops with
       | (breaks,_) :: _ ->
         let fresh = List.length !breaks - marker in
         breaks := List.mapi (fun i e -> if i < fresh then forget e else e) !breaks
       | [] -> ());
      ignore (statements (forget env) close);
      local completed
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
  (* A closure's statements, in their own context, restored after. *)
  block_statements := (fun result returned env ss ->
    let saved = (!block_result,!block_returned) in
    block_result := result; block_returned := returned;
    let restore () =
      let (r,t) = saved in block_result := r; block_returned := t in
    match statements env ss with
    | env -> restore (); env
    | exception ex -> restore (); raise ex);
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
  (* Likewise an entry, the closure body a guard's arm types twice. *)
  let seen = Hashtbl.create 64 in
  let entries = List.filter (fun x ->
    not (Hashtbl.mem seen x) && (Hashtbl.add seen x (); true)) (List.rev !entries) in
  {source=f;entries;expressions;arrows=List.rev !arrows},!requests
(* A named closure's claim is fixed where it is created, before the calls that
   offer it more parameters are reached: a first pass finds those offers, and
   the second states them at the creation. *)
let infer_function declarations module_functions (f:Source.fn) =
  (* A binder bounded by another reads through it: `U extends T` reads a
     member at `T`'s bound. *)
  rigid_bounds := List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
    | Some (ValueArgument b) when not (Semantic.mentions_rigid b) -> Some (q.identity,b)
    | Some (ValueArgument (Rigid t)) when t <> q.identity -> Some (q.identity,Rigid t)
    | _ -> None) f.quantified;
  (* An evolving binding's contract is what the body writes into it, which
     a pass finds under the contract the previous pass assumed: passes run
     until the contracts settle. A write whose value grows with the binding
     itself (a list consed onto it) never settles. *)
  let rec settled offered rounds =
    evolving_seen := [];
    let result = try Ok (infer_pass offered declarations module_functions f) with Json.Error m -> Error m in
    let grown = List.filter (fun (key,t) -> union (evolved key) t <> evolved key) !evolving_seen in
    match result,grown with
    | Ok result,[] -> result
    | Error m,[] -> raise (Json.Error m)
    | _,_ when rounds = 0 ->
      unsupported "an evolving binding's contract does not settle: a value written into it grows with the binding itself"
    | _ ->
      evolving_assumed := List.fold_left (fun acc (key,t) ->
        (key,union (evolved key) t) :: List.remove_assoc key acc) !evolving_assumed grown;
      settled offered (rounds - 1) in
  evolving_assumed := [];
  let claim,requests = settled [] 4 in
  if requests = [] then claim else
  let offered = List.map (fun pos -> pos,List.filter_map (fun (p,s) ->
    if p = pos then Some s else None) requests)
    (List.sort_uniq compare (List.map fst requests)) in
  fst (settled offered 4)
let infer program =
  let module_functions = List.map (fun (g:Source.fn) -> g.name,lazy (module_type g))
    program.Source.functions
    @ List.map (fun (name,t) -> name,lazy t) program.Source.values in
  let infer_with = infer_function program.Source.declarations in
  (* A class's instance members read the class as its own binding, `C.[[self]]`,
     at its construct signature: a module value of the initialization unit. *)
  let class_selves = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) ->
      let ctors = List.filter_map (fun (n,_,(e:expr)) -> match e.node with
        | Ctor _ -> Some n | _ -> None) bindings in
      List.filter_map (fun (n,written,_) -> match written with
        | Some t when List.mem n ctors || List.mem (n ^ ".[[class]]") ctors ->
          Some (n ^ ".[[self]]",lazy t)
        | _ -> None) bindings
    | _ -> []) program.Source.init in
  let init = match program.Source.init with
    | [] -> None
    | body -> Some (infer_with (module_functions @ class_selves)
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
