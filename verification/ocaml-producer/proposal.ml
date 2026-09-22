open Semantic
open Environment
open Source
open Inference

type entry = { start: Json.t; bindings: (string * binding) list }
(* A call site's validated substitution travels with its claim. It is proposal
   output for Lean to re-check, never an acceptance fact. *)
type expression = { pos: Json.t; type_: ty; instantiation: (string * ty) list option }
(* One closure advertising several signatures has one body and a separate
   obligation at each: the interior claims are collected once per signature,
   keyed by the closure's span and ordered with the signatures. *)
type overlay = { row_entries: entry list; row_expressions: expression list }
type function_claim = { source: fn; entries: entry list; expressions: expression list;
                        arrows: (Json.t * overlay list) list }
type t = { program: program; functions: function_claim list }
let unsupported s = Json.fail ("unsupported: " ^ s)
let combine = List.fold_left union (Atoms [])
let literal_type = function
  | LNull -> Atoms [Nul] | LUndefined -> Atoms [Undef]
  | LBool true -> Atoms [True] | LBool false -> Atoms [False]
  | LNumber s -> number_literal s | LString s -> Atoms [StrLit s]

(* Read permissions do not imply write permissions. All candidates still pass
   through reconstructed obligations, including readonly view conversion. *)
let rec field_type t name = match t with
  | Atoms atoms -> combine (List.map (function
      | Shape {elements=Some _;_} when name="length" -> Atoms [Num]
      | Shape shape -> (match List.find_opt (fun (f:Semantic.field) -> f.name=name) shape.fields with
          | Some f -> if f.optional then union f.read (Atoms [Undef]) else f.read
          | None -> unsupported ("missing field " ^ name))
      | _ -> unsupported "field read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> field_type t name) ts)
  | Rigid _ -> unsupported "field read on rigid parameter"
let rec index_type receiver key = match receiver with
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
      | Shape shape -> (match key with Atoms [StrLit name] -> field_type (Atoms [Shape shape]) name
          | _ -> unsupported "record index requires a string singleton")
      | _ -> unsupported "indexed read on non-object") atoms)
  | Union ts -> combine (List.map (fun t -> index_type t key) ts)
  | Rigid _ -> unsupported "indexed read on rigid parameter"

(* Branch restrictions only affect immutable values. Unknown/rigid predicates
   conservatively retain their type; proof checking validates each narrower cut. *)
let restrict literal equal t = match t with
  | Atoms xs -> ground (List.filter (fun atom ->
      let known = match atom,literal with
        | Nul,LNull | Undef,LUndefined | True,LBool true | False,LBool false -> Some true
        | NumLit a,LNumber b -> Some (Int64.float_of_bits a = float_of_string b)
        | StrLit a,LString b -> Some (a=b)
        | (Top | Num | Str | Shape _),_ -> None
        | _,_ -> Some false in
      match known with Some result -> result=equal | None -> true) xs)
  | Rigid _ | Union _ -> t
let rec branch env cond truth = match cond.node with
  | Not e -> branch env e (not truth)
  | Id name -> refine_value env name (function
      | Atoms xs as t when List.for_all (function True | False -> true | _ -> false) xs -> restrict (LBool truth) true t
      | t -> t)
  | Equality ((StrictEqual | StrictUnequal as op),{node=Id name;_},{node=Literal lit;_})
  | Equality ((StrictEqual | StrictUnequal as op),{node=Literal lit;_},{node=Id name;_}) ->
    refine_value env name (restrict lit (truth=(op=StrictEqual)))
  | _ -> env

(* Expected types guide fresh construction only. They are never a shortcut
   claiming that an arbitrary expression already satisfies an annotation. *)
let infer_function (f:Source.fn) =
  let entries = ref [] and expressions = ref [] and instantiations = ref [] in
  let arrows = ref [] in
  let entry env span = match Json.list span with
    | start::_ -> entries := {start;bindings=env} :: !entries
    | [] -> Json.fail "empty source span" in
  let rec expr ?expected env e =
    let t = match e.node with
    | Id n -> binding_type (lookup env n)
    | Literal l -> literal_type l
    | Not e -> ignore (expr env e); bool
    | Arith (_,l,r) -> ignore (expr env l); ignore (expr env r); Atoms [Num]
    | Equality (_,l,r) -> ignore (expr env l); ignore (expr env r); bool
    | Alloc fs ->
      let contract = match expected with Some (Atoms [Shape s]) when s.elements=None -> Some s | _ -> None in
      let fields = List.map (fun (name,e) ->
        let hint = Option.bind contract (fun s -> List.find_opt (fun (f:Semantic.field) -> f.name=name) s.fields) in
        let expected = Option.map (fun (f:Semantic.field) -> f.read) hint in
        let inferred=expr ?expected env e in
        let t=Option.value expected ~default:(widen inferred) in
        {name;optional=false;read=t;write=Some t}) fs in record fields
    | ArrayLiteral es ->
      let contract = match expected with Some (Atoms [Shape {elements=Some s;_}]) -> Some s | _ -> None in
      let types = List.mapi (fun i e ->
        let expected = Option.bind contract (fun s -> match List.nth_opt (s.required @ s.optional_elements) i with
          | Some t -> Some t | None -> s.rest) in expr ?expected env e) es in
      (match contract with
        | Some s -> array s
        | None -> array {required=[];optional_elements=[];rest=Some (widen (combine types));readonly=false})
    | Read (e,n) -> field_type (expr env e) n
    | Index (e,key) -> let receiver=expr env e in let key=expr env key in index_type receiver key
    | IndexWrite (receiver,key,rhs) -> ignore (expr env receiver); ignore (expr env key); expr env rhs
    | Write (receiver,_,rhs) -> ignore (expr env receiver); expr env rhs
    | Assign (n,rhs) -> (match lookup env n with
      | Storage contract -> expr ~expected:contract env rhs
      | Value _ -> unsupported "assignment to immutable binding")
    | Lambda (quantified,ps,defaults,result,body) ->
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
      ignore (expr ~expected:result inner body);
      let params = List.mapi (fun i (_,t) ->
        if List.mem_assoc i defaults then union t (Atoms [Undef]) else t) ps in
      let own = quantified_arrow quantified params result in
      (* A contract advertising several signatures is implemented by this one
         closure. Propose that contract and state what the body claims under
         each signature; Lean checks every one of them. *)
      let implements (s:Semantic.signature) =
        s.quantified=[] && List.length s.params=List.length ps in
      (match expected with
       | Some (Atoms [Shape {calls=(_::_::_ as calls);fields=[];elements=None}] as contract)
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
    | Call (callee,receiver,args) ->
      let callee = expr env callee in
      Option.iter (fun e -> ignore (expr env e)) receiver;
      (* A call writes a prefix of the declared positions. The rest are omitted,
         which is admissible exactly when each of their contracts admits
         `undefined`; Lean checks that premise for itself. *)
      let callable (signature:Semantic.signature) =
        let declared = List.length signature.params and written = List.length args in
        written <= declared
        && List.for_all Semantic.admits_undefined
             (List.filteri (fun i _ -> i >= written) signature.params) in
      (match callee with Atoms [Shape {calls=[signature];_}]
          when signature.quantified=[] && callable signature ->
        List.iteri (fun i e ->
          ignore (expr ~expected:(List.nth signature.params i) env e)) args;
        signature.result
      | Atoms [Shape {calls=[signature];_}]
          when signature.quantified<>[] && callable signature ->
        (* Omission contributes undefined to inference, but no expression or
           claim is inserted into the source's argument list. *)
        let actuals=List.map (expr env) args @
          List.init (List.length signature.params - List.length args) (fun _ -> Atoms [Undef]) in
        let inferred=Inference.infer signature actuals in
        instantiations := (e.pos,List.map (fun ((r:Semantic.rigid),t) -> r.spelling,t)
          inferred.substitution) :: !instantiations;
        inferred.result
      (* Several advertised signatures on one value. The actuals are typed on
         their own — contextual construction inside such a call is not guided —
         and the signature whose domains they match is proposed. Lean selects
         the row it checks and re-checks every argument obligation. *)
      | Atoms [Shape {calls=(_::_::_ as calls);_}]
          when List.for_all (fun (s:Semantic.signature) -> s.quantified=[]) calls ->
        let actuals = List.map (expr env) args in
        let usable = List.filter callable calls in
        let matching = List.filter (fun (s:Semantic.signature) ->
          let declared = List.filteri (fun i _ -> i < List.length actuals) s.params in
          declared = actuals) usable in
        (match matching,usable with
         | s :: _,_ -> s.result
         | [],(first :: rest) when List.for_all (fun (s:Semantic.signature) ->
             s.result = first.result) rest -> first.result
         | _ -> unsupported "overloaded call needs a signature its arguments match")
      | _ -> unsupported "call requires a single arrow the arguments can call")
    | WithFields (fn,initial,ft,bag) ->
      ignore (expr ~expected:ft env fn); ignore (expr ~expected:bag env initial);
      (match ft,bag with
        | Atoms [Shape f],Atoms [Shape b] when f.fields=[] && f.elements=None && b.calls=[] && b.elements=None ->
          Atoms [Shape {b with calls=f.calls}]
        | _ -> unsupported "function field construction requires a callable and a record contract")
    | Bind (callee,receiver,args) ->
      let callee=expr env callee in ignore (expr env receiver);
      (match callee with Atoms [Shape {calls=[signature];_}]
          when signature.quantified=[] && List.length args<=List.length signature.params ->
        let rec prefix ps args = match ps,args with
          | rest,[] -> rest
          | p::ps,e::es -> ignore (expr ~expected:p env e); prefix ps es
          | [],_::_ -> unsupported "bind argument prefix exceeds arity" in
        arrow (prefix signature.params args) signature.result
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
      expr ?expected (extend env name (Value (Option.value written ~default:initial))) body
    | IfBody (result,c,a,b) -> entry env e.pos; ignore (expr env c);
      let left=expr ~expected:result (branch env c true) a in
      let right=expr ~expected:result (branch env c false) b in union left right in
    (* Block wrappers correspond to statement entries, not expression sites. *)
    (match e.node with
      | DoneBody | ReturnBody _ | SequenceBody _ | LetBody _ | IfBody _ -> ()
      | _ -> expressions := {pos=e.pos;type_=t;
          instantiation=List.assoc_opt e.pos !instantiations} :: !expressions); t
  in
  let rec statements env ss = List.fold_left (fun env s ->
    entry env s.span;
    match s.statement with
    | Declare (mutable_,bs) -> List.fold_left (fun env (n,written,init) ->
      let initial = expr ?expected:written env init in
      let binding = match mutable_,written with
        | true,None -> unsupported "mutable binding requires an explicit fixed storage contract"
        | true,Some contract -> Storage contract
        | false,Some contract -> Value contract
        | false,None -> Value initial in
      extend env n binding) env bs
    | Return e -> ignore (expr ~expected:f.result env e); env
    | Effect e -> ignore (expr env e); env
    | If (c,a,b) -> ignore (expr env c);
      ignore (statements (branch env c true) a); ignore (statements (branch env c false) b); env
    | While (c,body) -> ignore (expr env c);
      ignore (statements (branch env c true) body); env
    | Break | Continue -> env) env ss in
  ignore (statements (List.map (fun (n,t) -> n,Value t) f.params) f.body);
  {source=f;entries=List.rev !entries;expressions=List.rev !expressions;
   arrows=List.rev !arrows}
let infer program = {program;functions=List.map infer_function program.Source.functions}
