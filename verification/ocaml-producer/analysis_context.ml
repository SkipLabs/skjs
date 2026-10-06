(* refinement.ml supplies branch refinement through the execution interpreter's input interface. *)
(* execution_analysis.ml interprets expression schedules to provide effect states and operand-entry environments. *)
(* closure_offers.ml tracks named closures and class constructors and records signatures offered by their uses. *)
(* claim_collection.ml collects entry claims and instances through point-specific publication operations. *)
open Environment
open Source
open Type_queries
module Make (S : Analysis_state.Scope) = struct
open Analysis_state.View(S)
include Closure_offers.Make(S)
module Execution_inputs : Execution_analysis.Inputs = struct
  let declarations = declarations
  let current_point () = (!local).Analysis_state.current_point
  let execution_at source = Hashtbl.find_opt executions (current_point (),source)
  let expression_hint source = Hashtbl.find_opt expression_hints source
  let claimed_type source = List.find_map (fun (x:Proposal_types.expression) ->
    if x.Proposal_types.point = current_point () && x.Proposal_types.pos = source
    then Some x.Proposal_types.type_ else None) (!local).Analysis_state.expressions
  let grew name = List.mem name (!local).Analysis_state.grown_locals
  let branch env cond truth = Refinement.branch_with diagnostics !rigid_bounds declarations
    ~modules:(fun name ->
      try Option.map Lazy.force (List.assoc_opt name module_functions) with Json.Error _ -> None)
    ~claimed:claimed_type env cond truth
end
include Execution_analysis.Make(Execution_inputs)
module Claim_inputs : Claim_collection.Inputs = struct
  let declarations = declarations
  let is_local name = List.mem_assoc name env0
  let module_type name = Option.map Lazy.force (List.assoc_opt name module_functions)
  let publish_instance source type_ =
    (!local).Analysis_state.instances <- (((!local).Analysis_state.current_point,source),type_) :: (!local).Analysis_state.instances
  let publish_entry start bindings =
    (!local).Analysis_state.entries <- {Proposal_types.point=(!local).Analysis_state.current_point;start;bindings} :: (!local).Analysis_state.entries
  let speculate f = Analysis_state.speculate S.state f
end
include Claim_collection.Make(Claim_inputs)
  let resolve env n = match List.assoc_opt n env with
    | Some b -> binding_type b
    | None -> (match List.assoc_opt n module_functions with
      | Some g -> Lazy.force g | None -> Json.fail ("unbound name " ^ n))

  let rec mark_exact (e:expr) = match e.node with
    | Alloc _ -> (!local).Analysis_state.exact_allocs <- e.pos :: (!local).Analysis_state.exact_allocs
    | Logical (_,_,b) | Coalesce (_,b) | Comma (_,b) -> mark_exact b
    | Conditional (_,a,b) -> mark_exact a; mark_exact b
    | Cast (("nonNull" | "satisfies"),_,e) -> mark_exact e
    | _ -> ()

  let rec reads n (e:expr) =
    (match e.node with Id m -> m = n | _ -> false) || List.exists (reads n) (Source.children e)

  let evolving_array (receiver:expr) = match receiver.node with
    | Id n -> (match List.assoc_opt n (!local).Analysis_state.evolving with Some (key,true) -> Some key | _ -> None)
    | _ -> None

  let adds env (receiver:expr) t name = match receiver.node with
    | Id n -> (match List.assoc_opt n env with
      | Some (Value _) -> may_lack declarations t name
      | _ -> false)
    | _ -> false

end
