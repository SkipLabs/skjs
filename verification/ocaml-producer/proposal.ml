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
      | NumLit _,Num | StrLit _,Str -> true
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

(* Read permissions do not imply write permissions. All candidates still pass
   through reconstructed obligations, including readonly view conversion. *)
let definition declarations id args =
  (* An interface and its base as one object: disjoint fields, and the one
     index signature either states. A hint only: Lean's `inheritRows` gives
     the declaration's meaning. *)
  let merge base own = match meet_objects base own with
    | Some t -> t
    | None -> (match base,own with
      | Atoms [Shape inherited],Atoms [Shape local]
        when inherited.calls=[] && local.calls=[] && inherited.elements=None && local.elements=None
             && (inherited.string_index=None || local.string_index=None) ->
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
let rec field_type declarations seen t name = match t with
  | Atoms atoms -> combine (List.map (function
      | Shape {elements=Some _;_} when name=Name "length" -> Atoms [Num]
      (* Any other key of an array is read from its prototype. *)
      | Shape {elements=Some _;_} ->
        field_type declarations seen (Atoms [Named (array_prototype,[])]) name
      | Shape shape -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) shape.fields with
          | Some f -> if f.optional then union f.read (Atoms [Undef]) else f.read
          | None -> (match shape.string_index,name with
            | Some index,Name _ -> union index.value (Atoms [Undef])
            | _ -> unsupported ("missing field " ^ key_text name)))
      | Exact fields -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) fields with
          | Some f -> f.read
          | None -> unsupported ("missing field " ^ key_text name))
      | Named (id,args) ->
        if List.mem id seen then unsupported "unguarded field cycle";
        field_type declarations (id::seen) (definition declarations id args) name
      | _ -> unsupported "field read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> field_type declarations seen t name) ts)
  (* A value of an intersection is one of each operand: read as the first
     operand that has the field, a hint Lean checks. *)
  | Meet (t,ts) -> first_part (fun t -> field_type declarations seen t name) (t::ts)
  | Rigid _ -> unsupported "field read on rigid parameter"
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
          | Atoms [Str] -> (match shape.string_index with
              | Some index -> union index.value (Atoms [Undef])
              | None -> unsupported "dynamic string index requires a dictionary")
          | _ -> unsupported "record index requires a string key")
      | Exact _ as atom -> (match key with
          | Atoms [StrLit name] -> field_type declarations seen (Atoms [atom]) (Name name)
          | _ -> unsupported "record index requires a string key")
      | Named (id,args) ->
        if List.mem id seen then unsupported "unguarded index cycle";
        index_type declarations (id::seen) (definition declarations id args) key
      | _ -> unsupported "indexed read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> index_type declarations seen t key) ts)
  | Meet (t,ts) -> first_part (fun t -> index_type declarations seen t key) (t::ts)
  | Rigid _ -> unsupported "indexed read on rigid parameter"

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

(* Branch restrictions only affect immutable values. Unknown/rigid predicates
   conservatively retain their type; proof checking validates each narrower cut. *)
let restrict literal equal t = match t with
  | Atoms xs -> ground (List.filter (fun atom ->
      let known = match atom,literal with
        | Nul,LNull | Undef,LUndefined | True,LBool true | False,LBool false -> Some true
        | NumLit a,LNumber b -> Some (Int64.float_of_bits a = float_of_string b)
        | StrLit a,LString b -> Some (a=b)
        | (Top | Num | Str | Shape _ | Exact _ | Named _),_ -> None
        | _,_ -> Some false in
      match known with Some result -> result=equal | None -> true) xs)
  | Rigid _ | Union _ | Meet _ -> t
let rec branch env cond truth = match cond.node with
  | Not e -> branch env e (not truth)
  | Id name -> refine_value env name (function
      | Atoms xs as t when List.for_all (function True | False -> true | _ -> false) xs -> restrict (LBool truth) true t
      | t -> t)
  | TypeofTest (shape,equal,{node=Id name;_}) ->
    (* Keep the atoms of the tested shape on the arm where the test holds,
       and the others where it fails. *)
    let has = function
      | Num | NumLit _ -> Some (shape="number") | Str | StrLit _ -> Some (shape="string")
      | True | False -> Some (shape="boolean") | Undef -> Some (shape="undefined")
      | Bigint -> Some (shape="bigint") | Symbol -> Some (shape="symbol")
      | Shape s -> Some (shape="function" && s.calls<>[])
      | Exact _ -> Some false
      (* A class is a function to `typeof`. *)
      | Ctors _ -> Some (shape="function")
      | Nul -> Some false
      (* A declaration's shape is not known here: it stays on both arms. No
         value is an argument pack. *)
      | Top | Named _ -> None in
    refine_value env name (function
      | Atoms xs when not (List.mem Top xs) ->
        Atoms (List.filter (fun a -> match has a with
          | Some holds -> holds = (truth = equal) | None -> true) xs)
      | t -> t)
  | Equality ((StrictEqual | StrictUnequal as op),{node=Id name;_},{node=Literal lit;_})
  | Equality ((StrictEqual | StrictUnequal as op),{node=Literal lit;_},{node=Id name;_}) ->
    refine_value env name (restrict lit (truth=(op=StrictEqual)))
  | _ -> env

(* Expected types guide fresh construction only. They are never a shortcut
   claiming that an arbitrary expression already satisfies an annotation. *)
(* A module function as its callers see it: an ordinary function at exactly its
   annotated parameters and result. A rest parameter contributes its tuple's
   positions or its array's element. Generic ones are not reachable yet. *)
let module_type (g:Source.fn) =
  let tys = List.map snd g.params in
  match g.rest,List.rev tys with
  | true,last::before ->
    (match Semantic.tuple_positions last,Semantic.array_element last with
     | Some positions,_ -> quantified_arrow g.quantified (List.rev before @ positions) g.result
     | None,Some element -> variadic_arrow ~quantified:g.quantified (List.rev before) element g.result
     | _ -> unsupported "rest parameter contract of a module function")
  | _ -> quantified_arrow g.quantified tys g.result

(* One pass over a function. [offered] gives, for a named closure's creation,
   the further signatures its uses offer it; the pass reports them as
   [requests], and [infer_function] runs a second pass with them. *)
let infer_pass offered declarations module_functions (f:Source.fn) =
  let env0 = List.map (fun (n,t) -> n,Value t) f.params in
  (* Unannotated immutable locals bound to a closure without binders or a rest
     parameter: where the closure is created, and its parameters' types. *)
  let closures = ref [] and requests = ref [] in
  (* Classes declared here: where the class value is created, its
     constructor's parameters, its instance type, and its methods, each a key
     and the named closure the instance holds under it. *)
  let classes = ref [] in
  let named_closure n written (init:expr) = match written,init.node with
    | None,Lambda (_,[],ps,_,false,_,_) -> closures := (n,(init.pos,List.map snd ps)) :: !closures
    | Some _,Ctor {node=Lambda (None,[],ps,[],false,Some instance,{node=Alloc fs;_});_} ->
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
  (* A class value expected at a construct signature whose instance has a
     method taking more parameters than the class's own: the method's closure
     is claimed at those parameters too, with its own receiver, the instance,
     and the class value at a construct signature giving the expected
     instance. Calls through the member discard the extra actuals; Lean checks
     the method's body at each signature and the constructor's at each. *)
  let offer_class (pos,params,instance,methods) expected =
    match declared_head declarations [] expected with
    | Atoms [Ctors signatures] ->
      List.iter (fun (s:Semantic.signature) ->
        let member key = match (try Some (declared_head declarations []
            (field_type declarations [] s.result (Name key))) with Json.Error _ -> None) with
          | Some (Atoms [Shape {calls=[m];fields=[];string_index=None;elements=None}]) -> Some m
          | _ -> None in
        let widened = List.filter (fun (key,m) -> match member key with
          | Some offered -> (match closure_offer m {offered with receiver=instance} with
            | Some state -> state (); true
            | None -> false)
          | None -> false) methods in
        if widened <> [] then
          requests := (pos,{quantified=[];receiver=top;params;variadic=None;rest_pack=None;
                            result=s.result}) :: !requests)
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
    | start::_ -> entries := {start;bindings=env} :: !entries
    | [] -> Json.fail "empty source span" in
  let rec expr ?expected env e =
    let t = match e.node with
    | Id n ->
      Option.iter (fun expected -> Option.iter (fun c -> offer_class c expected)
        (List.assoc_opt n !classes)) expected;
      resolve env n
    | Literal l -> literal_type l
    | Not e -> ignore (expr env e); bool
    | TypeofTest (_,_,e) -> ignore (expr env e); bool
    | Arith (_,l,r) -> ignore (expr env l); ignore (expr env r); Atoms [Num]
    | Equality (_,l,r) -> ignore (expr env l); ignore (expr env r); bool
    | Alloc fs ->
      let contract = Option.bind expected (object_hint declarations []) in
      let fields = List.map (fun (name,e) ->
        let hint = Option.bind contract (fun s -> List.find_opt (fun (f:Semantic.field) -> f.name=Name name) s.fields) in
        (* A key the contract names is built at its member's type; any other
           at the index. *)
        let expected = match hint,contract with
          | Some (f:Semantic.field),_ -> Some f.read
          | None,Some {string_index=Some index;_} -> Some index.value
          | None,_ -> None in
        let inferred=expr ?expected env e in
        (* A method's closure offered further signatures is held at its own
           claim: a construct signature offering them reads them there. *)
        let widened = match e.node with
          | Id m -> (match List.assoc_opt m !closures with
            | Some (pos,_) -> List.mem_assoc pos offered | None -> false)
          | _ -> false in
        let t=if widened then inferred else Option.value expected ~default:(widen inferred) in
        {name=Name name;optional=false;read=t;write=Some t}) fs in
      (* Where the contract is a dictionary, or has optional fields, the
         literal is claimed with its exact keys: that own-key bound is what
         lets it meet an index, or an optional field it leaves out. *)
      (match contract with
       | Some {string_index=Some _;_} -> Atoms [Exact fields]
       | Some {fields=contract_fields;_}
         when List.exists (fun (f:Semantic.field) -> f.optional) contract_fields -> Atoms [Exact fields]
       | _ -> record fields)
    | ArrayLiteral es ->
      let contract = match expected with
        | Some (Atoms [Shape {elements=Some s;_}]) -> Some s
        | Some expected ->
          Option.map (fun t -> {required=[];optional_elements=[];rest=Some t;readonly=true})
            (iterated_hint declarations expected)
        | None -> None in
      let types = List.mapi (fun i e ->
        let expected = Option.bind contract (fun s -> match List.nth_opt (s.required @ s.optional_elements) i with
          | Some t -> Some t | None -> s.rest) in expr ?expected env e) es in
      (match contract with
        | Some s -> array s
        | None -> array {required=[];optional_elements=[];rest=Some (widen (combine types));readonly=false})
    | Read (e,n) -> field_type declarations [] (expr env e) n
    | Index (e,key) -> let receiver=expr env e in let key=expr env key in index_type declarations [] receiver key
    | IndexWrite (receiver,key,rhs) -> ignore (expr env receiver); ignore (expr env key); expr env rhs
    | Write (receiver,_,rhs) -> ignore (expr env receiver); expr env rhs
    | Assign (n,rhs) ->
      if not (List.mem_assoc n env) && List.mem_assoc n module_functions then
        unsupported ("assignment to module function " ^ n);
      (match lookup env n with
      | Storage contract -> expr ~expected:contract env rhs
      | Value _ -> unsupported "assignment to immutable binding")
    | Ctor {node=Lambda (None,[],ps,[],false,Some result,body);_} ->
      (* The constructor's body under its parameters; `new` passes it no
         receiver it reads. The class value's type is its construct signature. *)
      let inner = List.fold_left (fun env (n,t) -> extend env n (Value t)) env ps in
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
             let inferred = Inference.infer ~expand:(expand_named declarations) ~receiver:Semantic.top signature
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
      let body_type = expr ?expected:written inner body in
      (* Without a result annotation the result is the body's, widened as
         TypeScript widens an inferred return type. It is a claim: Lean checks
         the body against it. *)
      let result = match written with
        | Some result -> result
        | None when quantified <> [] -> unsupported "a quantified closure needs its result annotation"
        | None -> widen body_type in
      let params = List.mapi (fun i (_,t) ->
        if List.mem_assoc i defaults then union t (Atoms [Undef]) else t) ps in
      (* A tuple rest is one binding and several positions: the signature
         carries the elements, the body reads the tuple. An array rest is one
         binding and any number of positions, each at its element type. *)
      let params,element = if not rest then params,None else
        match List.rev params with
        | last :: fixed ->
          (match Semantic.tuple_positions last,Semantic.array_element last with
           | Some elements,_ -> List.rev fixed @ elements,None
           | None,Some element -> List.rev fixed,Some element
           | _ -> unsupported "a rest parameter needs a tuple of required positions or a mutable array")
        | [] -> unsupported "a rest parameter needs a parameter" in
      let own = match element with
        | Some element -> variadic_arrow ~quantified ~receiver params element result
        | None -> quantified_arrow ~receiver quantified params result in
      (* A named closure passed where more parameters are offered is claimed
         at those signatures too, beside its own: calls through it discard
         the actuals past its parameters, and Lean checks its body at each. *)
      let own = match List.assoc_opt e.pos offered, own with
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
       | Some (Atoms [Shape {calls=(_::_::_ as calls);fields=[];string_index=None;elements=None}] as contract)
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
        | Call (c,r,a,s) -> c,r,a,s,[]
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
          | Atoms [Shape {calls=[offered];fields=[];string_index=None;elements=None}] as t
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
           | Atoms [Shape {calls=[o];fields=[];string_index=None;elements=None}] -> closure_offer n o
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
           claim is inserted into the source's argument list. *)
        let actuals=List.map (expr env) args @
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
    | Cast (kind,annot,e) -> let actual=expr ?expected:annot env e in
      (match kind,annot with
        | "nonNull",None -> without_nullish actual
        | "satisfies",Some _ -> actual
        | "as",Some target -> target
        | _ -> unsupported "cast form")
    | DoneBody -> Atoms [Undef]
    | ReturnBody body -> entry env e.pos; expr ?expected env body
    | SequenceBody (init,body) -> entry env e.pos; ignore (expr env init); expr ?expected env body
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
      | DoneBody | ReturnBody _ | SequenceBody _ | LetBody _ | IfBody _ -> ()
      | _ -> expressions := {pos=e.pos;type_=t;
          instantiation=List.assoc_opt e.pos !instantiations} :: !expressions); t
  in
  let rec returns ss = match List.rev ss with
    | {statement=Return _;_}::_ -> true
    | {statement=If (_,a,b);_}::_ -> returns a && returns b
    | _ -> false in
  let rec statements env ss = List.fold_left (fun env s ->
    entry env s.span;
    match s.statement with
    | Declare (mutable_,bs) -> List.fold_left (fun env (n,written,init) ->
      let initial = expr ?expected:written env init in
      if not mutable_ then named_closure n written init;
      let binding = match mutable_,written with
        | true,None -> unsupported "mutable binding requires an explicit fixed storage contract"
        | true,Some contract -> Storage contract
        (* A class's annotation is its own construct signature, which the
           parser writes; the class value's claim may offer more. *)
        | false,Some _ when (match init.node with Ctor _ -> true | _ -> false) -> Value initial
        | false,Some contract -> Value contract
        | false,None -> Value initial in
      extend env n binding) env bs
    | Return e -> ignore (expr ~expected:f.result env e); env
    | Effect e -> ignore (expr env e); env
    | If (c,a,b) -> ignore (expr env c);
      ignore (statements (branch env c true) a); ignore (statements (branch env c false) b);
      (* The rest of the block runs only where an arm that always returns was
         not taken. *)
      (match returns a,returns b with
       | true,false -> branch env c false
       | false,true -> branch env c true
       | _ -> env)
    | While (c,body) -> ignore (expr env c);
      ignore (statements (branch env c true) body); env
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
      ignore (statements (extend env name (Value element)) body); env
    | Break | Continue -> env) env ss in
  ignore (statements env0 f.body);
  let expressions = List.map (fun (x:expression) -> match List.assoc_opt x.pos !instances with
    | Some instance -> {x with type_=instance}
    | None -> x) (List.rev !expressions) in
  {source=f;entries=List.rev !entries;expressions;arrows=List.rev !arrows},!requests
(* A named closure's claim is fixed where it is created, before the calls that
   offer it more parameters are reached: a first pass finds those offers, and
   the second states them at the creation. *)
let infer_function declarations module_functions f =
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
  (* A function reads a module constant at its annotation; the initialization
     unit is what establishes it. *)
  let module_constants = List.concat_map (fun (s:Source.stmt) -> match s.statement with
    | Declare (false,bindings) -> List.map (fun (n,written,_) -> n,lazy (match written with
        | Some t -> t
        | None -> unsupported ("module constant " ^ n ^ " is read by a function, so it needs an annotation")))
      bindings
    | _ -> []) program.Source.init in
  let infer_with = infer_function program.Source.declarations in
  let init = match program.Source.init with
    | [] -> None
    | body -> Some (infer_with module_functions
        {quantified=[];name="";name_pos=Json.Null;params=[];rest=false;
         result=Atoms [Undef];body}) in
  {program;init;functions=List.map (infer_with (module_functions @ module_constants))
    program.Source.functions}
