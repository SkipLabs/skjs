open Semantic
(* Value snapshots and storage contracts have different constructors. The
   environment is persistent; reads never expose a way to alter storage types. *)
type binding = Value of ty | Storage of ty
let binding_type = function Value t | Storage t -> t
let lookup env name = match List.assoc_opt name env with
  | Some b -> b | None -> Json.fail ("unbound name " ^ name)
let extend env name binding =
  if List.mem_assoc name env then Json.fail ("unsupported: shadowing " ^ name);
  env @ [name,binding]

(* Only immutable values are refined. Mutable reads still expose their fixed
   contract; heap contents require a separate alias/effect analysis. *)
let refine_value env name refine = List.map (fun (n,b) ->
  if n=name then n,(match b with Value t -> Value (refine t) | Storage _ -> b)
  else n,b) env
