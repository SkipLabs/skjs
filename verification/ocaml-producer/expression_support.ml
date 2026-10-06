open Semantic
open Environment
open Source
open Type_queries
open Proposal_diagnostics
module Make (S : Analysis_state.Scope) = struct
open Analysis_state.View(S)
open Analysis_context.Make(S)
  let target_contract (expr:Analysis_state.expression_infer) env (target:expr) = match target.node with
    | Id n ->
      ignore (expr env target);
      (match lookup env n with
       | Storage (contract,_) -> contract
       | Value _ -> Proposal_diagnostics.unsupported "assignment to immutable binding")
    | _ -> expr env target
  (* The type `e as const` gives its operand: a literal its own type, an
     array literal the readonly tuple of its elements', an object literal
     readonly fields of theirs; a name keeps its type. None for any other
     operand, which TypeScript refuses. An element or field of a literal
     that is none of these (`[x.f] as const`) keeps its own type, as
     TypeScript's const context does. *)
  let rec const_type (expr:Analysis_state.expression_infer) ?(nested = false) env (e:expr) = match e.node with
    | Literal l -> Some (literal_type l)
    | Id n -> Some (resolve env n)
    | Cast ("const",None,e) -> const_type expr ~nested env e
    | ArrayLiteral es ->
      let elements = List.map (const_type expr ~nested:true env) es in
      if List.mem None elements then None
      else Some (array {required=List.filter_map Fun.id elements;optional_elements=[];rest=None;readonly=true;presence=Dense})
    | Alloc fs ->
      let fields = List.map (fun (name,e) -> name,const_type expr ~nested:true env e) fs in
      if List.exists (fun (_,t) -> t = None) fields then None
      else Some (record (List.map (fun (name,t) ->
        {name;optional=false;read=Option.get t;write=None;host=false;receivers=[]}) fields))
    | _ when nested -> quietly (fun () -> expr env e)
    | _ -> None
  (* `await e` and an async body's `return e` (the intrinsics `%Await%` and
     `%AsyncReturn%`) of a value that may be an object other than a promise
     the intrinsic names, or of a type parameter or `unknown`. *)
  let explain_thenable (e:expr) (target:expr) (signature:Semantic.signature) actuals =
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
  let explain_open_array site env n expected =
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
  let explain_record_at_index site env n expected =
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
  let dictionary_growth site t field =
    match flat_atoms declarations t with
    | [] -> ()
    | atoms -> if List.for_all (function
        | Shape {indexes=_::_;elements=None;calls=[];fields;_} ->
          not (List.exists (fun (f:Semantic.field) -> f.name = field) fields)
        | _ -> false) atoms then
      explain site ("a write adds the property '" ^ key_text field ^ "' where a dictionary may lack it: \
        another reference may hold the dictionary, and would see its keys change")

end
