(* refinement.ml proposes branch environments from the test and current field facts. *)
open Semantic
open Environment
open Source
open Type_queries
open Proposal_types
open Refinement
module Make (S : Analysis_state.Scope) = struct
open Analysis_state.View(S)
  let execution (e:Source.expr) = match Hashtbl.find_opt executions (!current_point,e.pos) with
    | Some plan -> plan
    | None -> Json.fail ("missing expression execution plan at " ^ !current_point ^
        " for " ^ Json.encode e.pos)

  let branch env cond truth = branch_with diagnostics !rigid_bounds declarations ~modules:(fun n ->
    try Option.map Lazy.force (List.assoc_opt n module_functions) with Json.Error _ -> None)
    ~claimed:(fun pos -> List.find_map (fun (x:expression) ->
      if x.point = !current_point && x.pos = pos then Some x.type_ else None) !expressions) env cond truth

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
      | _ -> None) left

  let claimed_type span = List.find_map (fun (x:expression) ->
    if x.point = !current_point && x.pos=span then Some x.type_ else None) !expressions

  let refine_test env condition test truth =
    match Hashtbl.find_opt expression_hints condition with
    | None -> env
    | Some cond -> (match test with
      | Execution.Truthy -> branch env cond truth
      | Execution.Nullish | Execution.Defined ->
        let refine t = match test,truth with
          | Execution.Nullish,true -> union (restrict Nul true t) (restrict Undef true t)
          | Execution.Nullish,false -> restrict Undef false (restrict Nul false t)
          | Execution.Defined,true -> restrict Undef false t
          | Execution.Defined,false -> restrict Undef true t
          | Execution.Truthy,_ -> t in
        (match cond.node with Id name -> refine_value env name refine | _ -> env))

  let restore_optional original env =
    let env=List.remove_assoc "?." env in
    match List.assoc_opt "?." original with None -> env | Some binding -> env @ ["?.",binding]

  let rec run_execution ?(observe = fun _ _ -> ()) env = function
    | Execution.Observe (source,evaluate) -> observe source env; run_execution ~observe env evaluate
    | Execution.Atom (_,operation) -> (match operation.Execution.impact with
      | Execution.None_ -> env
      | Execution.Havoc -> forget env
      | Execution.CellWrite (name,value) ->
        (match List.assoc_opt name env,claimed_type value with
         | Some (Storage _),Some t -> assign env name t
         | Some (Storage _),None -> forget ~only:(( = ) name) env
         | _ -> env)
      | Execution.CellUpdate (name,source) ->
        (match List.assoc_opt name env,Hashtbl.find_opt expression_hints source with
         | Some (Storage (contract,_)),Some {node=Update (op,_,rhs,_);_} ->
           let right=match rhs with None -> contract | Some rhs ->
             Option.value (claimed_type rhs.pos) ~default:contract in
           assign env name (operation_result declarations op contract right)
         | Some (Storage _),_ -> forget ~only:(( = ) name) env
         | _ -> env))
    | Execution.Sequence (_,binding,evaluate,next) ->
      let env=run_execution ~observe env evaluate in
      let optional=binding.Execution.name="?." in
      let original=env in
      let env=if optional then
        let t=Option.value (claimed_type (Execution.source evaluate)) ~default:top in
        List.remove_assoc "?." env @ ["?.",Value t] else env in
      let env=run_execution ~observe env next in
      if optional then restore_optional original env else env
    | Execution.Choose (_,condition,test,binding,evaluate,yes,no) ->
      let env=run_execution ~observe env evaluate in
      let original=env in
      let optional=binding.Execution.name="?." in
      let env=if optional then
        let t=Option.value (claimed_type (Execution.source evaluate)) ~default:top in
        List.remove_assoc "?." env @ ["?.",Value t] else env in
      let path truth =
        let env=refine_test env condition test truth in
        if optional then refine_value env "?." (fun t ->
          if truth then union (restrict Nul true t) (restrict Undef true t)
          else without_nullish t) else env in
      let left=run_execution ~observe (path true) yes
      and right=run_execution ~observe (path false) no in
      let result=join env left right in
      if optional then restore_optional original result else result

  let effects env (e:expr) = run_execution env (execution e)

  let expression_entry root source fallback =
    let (_,plan,initial)=root in
    let entries=Hashtbl.create 16 in
    let observe span env=match Hashtbl.find_opt entries span with
      | None -> Hashtbl.add entries span env
      | Some previous ->
        let impossible env=List.exists (fun (n,b) -> not (is_field n) && binding_type b=Atoms []) env in
        let env=if impossible previous then env else if impossible env then previous else
          join previous previous env in
        Hashtbl.replace entries span env in
    ignore (run_execution ~observe initial plan);
    Option.value (Hashtbl.find_opt entries source) ~default:fallback

end
