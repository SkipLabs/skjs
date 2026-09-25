open Semantic
(* Value snapshots and storage contracts have different constructors. The
   environment is persistent; reads never expose a way to alter storage types.
   A cell carries its fixed contract and what it is proposed to hold here:
   the contract, or a narrower primitive type after an assignment or a guard,
   which Lean checks as a fact about the cell's current contents on every
   edge into the point claiming it. *)
type binding = Value of ty | Storage of ty * ty
let binding_type = function Value t | Storage (_,t) -> t
let cell contract = Storage (contract,contract)
let lookup env name = match List.assoc_opt name env with
  | Some b -> b | None -> Json.fail ("unbound name " ^ name)
let extend env name binding =
  if List.mem_assoc name env then Json.fail ("unsupported: shadowing " ^ name);
  env @ [name,binding]

(* The contents Lean can know of a cell: a union of primitive atoms, its
   supported current-content predicates. Anything else is read at the
   contract. *)
let knowable = function
  | Atoms xs -> List.for_all (function
      | Nul | Undef | True | False | Num | NumLit _ | Str | StrLit _ -> true
      | _ -> false) xs
  | Rigid _ | Union _ | Meet _ -> false
let holding contract t = if knowable t then Storage (contract,t) else cell contract

(* A branch refines an immutable value, and a cell's known contents where
   the refinement is a primitive predicate. Heap contents of objects require
   a separate alias/effect analysis. *)
let refine_value env name refine = List.map (fun (n,b) ->
  if n=name then n,(match b with
    | Value t -> Value (refine t)
    | Storage (contract,current) -> holding contract (refine current))
  else n,b) env
(* After an assignment, the cell holds the value written. *)
let assign env name t = List.map (fun (n,b) ->
  if n=name then n,(match b with Storage (contract,_) -> holding contract t | Value _ -> b)
  else n,b) env
(* Where a step may write cells unseen (a call, a closure run later, a loop's
   other iterations), a cell is known only by its contract. *)
let forget ?(only=fun _ -> true) env = List.map (fun (n,b) -> match b with
  | Storage (contract,_) when only n -> n,cell contract
  | _ -> n,b) env
