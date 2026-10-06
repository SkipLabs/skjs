(* execution_analysis.ml interprets expression schedules to provide effect states and operand-entry environments. *)
(* closure_offers.ml tracks named closures and class constructors and records signatures offered by their uses. *)
(* claim_collection.ml collects entry claims and instances and restores claims after speculative inference. *)
open Environment
open Source
open Type_queries
module Make (S : Analysis_state.Scope) = struct
open Analysis_state.View(S)
include Closure_offers.Make(S)
include Execution_analysis.Make(S)
include Claim_collection.Make(S)
  let resolve env n = match List.assoc_opt n env with
    | Some b -> binding_type b
    | None -> (match List.assoc_opt n module_functions with
      | Some g -> Lazy.force g | None -> Json.fail ("unbound name " ^ n))

  let rec mark_exact (e:expr) = match e.node with
    | Alloc _ -> exact_allocs := e.pos :: !exact_allocs
    | Logical (_,_,b) | Coalesce (_,b) | Comma (_,b) -> mark_exact b
    | Conditional (_,a,b) -> mark_exact a; mark_exact b
    | Cast (("nonNull" | "satisfies"),_,e) -> mark_exact e
    | _ -> ()

  let rec reads n (e:expr) =
    (match e.node with Id m -> m = n | _ -> false) || List.exists (reads n) (Source.children e)

  let evolving_array (receiver:expr) = match receiver.node with
    | Id n -> (match List.assoc_opt n !evolving with Some (key,true) -> Some key | _ -> None)
    | _ -> None

  let adds env (receiver:expr) t name = match receiver.node with
    | Id n -> (match List.assoc_opt n env with
      | Some (Value _) -> may_lack declarations t name
      | _ -> false)
    | _ -> false

end
