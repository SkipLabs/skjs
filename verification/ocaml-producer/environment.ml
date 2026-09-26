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
(* A declaration may hide an outer value of its name, as Lean hides its slot:
   the outer binding stays, under a key no source name spells, until the
   block that hid it ends (`unshadow`), and what was known of its fields is
   forgotten. A cell is not hidden. *)
let hidden_prefix name = name ^ "\001"
let is_hidden n = String.contains n '\001'
let is_field n = String.contains n '\000'
let owner n = String.sub n 0 (String.index n '\000')
let extend env name binding =
  match List.assoc_opt name env with
  | None -> env @ [name,binding]
  | Some (Storage _) -> Json.fail ("unsupported: shadowing " ^ name)
  | Some (Value _) ->
    let depth = List.length (List.filter (fun (n,_) ->
      String.starts_with ~prefix:(hidden_prefix name) n) env) in
    let hidden = hidden_prefix name ^ string_of_int depth in
    List.filter_map (fun (n,b) ->
      if n = name then Some (hidden,b)
      else if is_field n && owner n = name then None
      else Some (n,b)) env @ [name,binding]
(* Where a block ends, each value it hid is its name's again, and the
   hiding binding and what was known of its fields are gone. *)
let unshadow before env =
  let fresh = List.filter (fun (n,_) -> is_hidden n && not (List.mem_assoc n before)) env in
  List.fold_left (fun env (h,_) ->
    let name = String.sub h 0 (String.index h '\001') in
    List.filter_map (fun (n,b) ->
      if n = h then Some (name,b)
      else if n = name || (is_field n && owner n = name) then None
      else Some (n,b)) env)
    env (List.sort (fun (a,_) (b,_) -> compare b a) fresh)

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
(* What a field of an immutable binding's object currently holds, where a
   guard found it: an entry named by the object's name and the field joined
   by a NUL, which no name contains, holding a union of primitive atoms. Lean
   checks it on every edge into a point claiming it, as a current-content
   fact about the field. *)
let field_key name field = name ^ "\000" ^ field
let field_of n = let i = String.index n '\000' in String.sub n (i+1) (String.length n - i - 1)
let fact env key t =
  let rest = List.remove_assoc key env in
  if knowable t && t <> Atoms [] then rest @ [key,Value t] else rest
(* Where a step may write cells unseen (a call, a closure run later, a loop's
   other iterations), a cell is known only by its contract, and no field's
   contents are known. A step that assigns only locals keeps the fields. *)
let forget ?only env = List.filter_map (fun (n,b) -> match b,only with
  | _,None when is_field n -> None
  | Storage (contract,_),None -> Some (n,cell contract)
  | Storage (contract,_),Some only when only n -> Some (n,cell contract)
  | _ -> Some (n,b)) env
