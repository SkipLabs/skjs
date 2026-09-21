open Semantic
open Environment
open Source

type entry = { start: Json.t; bindings: (string * binding) list }
type expression = { pos: Json.t; type_: ty }
type function_claim = { source: fn; entries: entry list; expressions: expression list }
type t = { program: program; functions: function_claim list }
let unsupported s = Json.fail ("unsupported: " ^ s)

(* Inference only constructs immutable candidates. It has no validation token
   and cannot publish acceptance. The validator independently reconstructs all
   obligations from the source, including writes and declared return types. *)
let infer_function (f:Source.fn) =
  let entries = ref [] and expressions = ref [] in
  let entry env span = match Json.list span with
    | start::_ -> entries := {start;bindings=env} :: !entries
    | [] -> Json.fail "empty source span" in
  let rec expr env e =
    let t = match e.node with
    | Id n -> binding_type (lookup env n)
    | Literal l -> (match l with
      | LNull -> Atoms [Nul] | LUndefined -> Atoms [Undef]
      | LBool true -> Atoms [True] | LBool false -> Atoms [False]
      | LNumber _ -> Atoms [Num] | LString _ -> Atoms [Str])
    | Not e -> ignore (expr env e); bool
    | Arith (_,l,r) -> ignore (expr env l); ignore (expr env r); Atoms [Num]
    | Equality (_,l,r) -> ignore (expr env l); ignore (expr env r); bool
    | Alloc fs -> record (List.map (fun (name,e) -> let t=widen (expr env e) in {name;optional=false;read=t;write=Some t}) fs)
    | Read (e,n) -> (match expr env e with
      | Atoms [Shape shape] -> (match List.find_opt (fun (f:Semantic.field) -> f.name=n) shape.fields with
        | Some f -> f.read | None -> unsupported ("missing field " ^ n))
      | _ -> unsupported "read requires a known record shape")
    | Write (receiver,_,rhs) -> ignore (expr env receiver); expr env rhs
    | Assign (n,rhs) -> (match lookup env n with
      | Storage _ -> expr env rhs
      | Value _ -> unsupported "assignment to immutable binding")
    | Lambda (ps,result,body) ->
      let inner = List.fold_left (fun env (n,t) -> extend env n (Value t)) env ps in
      ignore (expr inner body); arrow (List.map snd ps) result
    | Call (callee,receiver,args) ->
      let callee = expr env callee in
      Option.iter (fun e -> ignore (expr env e)) receiver;
      let args = List.map (expr env) args in
      (match callee with Atoms [Shape {calls=[signature];_}] when List.length signature.params=List.length args -> signature.result
      | _ -> unsupported "call requires a single arrow with matching arity")
    | Conditional (c,a,b) -> ignore (expr env c);
      let left = expr env a in let right = expr env b in union left right in
    expressions := {pos=e.pos;type_=t} :: !expressions; t
  in
  let rec statements env ss = List.fold_left (fun env s ->
    entry env s.span;
    match s.statement with
    | Declare (mutable_,bs) -> List.fold_left (fun env (n,written,init) ->
      let initial = expr env init in
      let binding = match mutable_,written with
        | true,None -> unsupported "mutable binding requires an explicit fixed storage contract"
        | true,Some contract -> Storage contract
        | false,Some contract -> Value contract
        | false,None -> Value initial in
      extend env n binding) env bs
    | Return e | Effect e -> ignore (expr env e); env
    | If (c,a,b) -> ignore (expr env c);
      ignore (statements env a); ignore (statements env b); env) env ss in
  ignore (statements (List.map (fun (n,t) -> n,Value t) f.params) f.body);
  {source=f;entries=List.rev !entries;expressions=List.rev !expressions}
let infer program = {program;functions=List.map infer_function program.Source.functions}
