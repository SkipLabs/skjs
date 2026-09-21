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
