open Semantic
open Type_queries


(* An object literal with spreads, as a merge reads it: each alternative of
   what is built so far is its fields and whether its own keys are exactly
   theirs; a source's alternative may also state an index, the type of every
   own string key it does not name. *)
type alternative = { afields : Semantic.field list; exact : bool; index : ty option }

(* A method member is host-relative: its object may hold it on its
   prototype, which a spread does not copy. *)
let method_field (f:Semantic.field) = f.host

(* The alternatives a spread's operand gives: nothing from a primitive other
   than a string, a record's fields otherwise. *)
let string_key (f:Semantic.field) = match f.name with Name _ -> true | Key _ -> false
let rec source_alternatives declarations seen t = match t with
  | Atoms atoms -> List.concat_map (function
      | Nul | Undef | True | False | Num | NumLit _ | Bigint | BigintLit _ | Symbol ->
        [{afields=[];exact=true;index=None}]
      (* A copy takes no symbol-keyed property, a private slot's included
         (DESIGN.md, "Object literals"). *)
      | Exact fs -> [{afields=List.filter (fun (f:Semantic.field) -> f.name <> Name proto_key && string_key f) fs;
                      exact=true;index=None}]
      | Shape {fields;indexes;calls=[];elements=None} ->
        (* The string index states every own string key's type; a number
           index states only the canonical numeric ones', so a key it covers
           is left unstated, as an open record's is. *)
        [{afields=List.filter (fun (f:Semantic.field) ->
            not (method_field f) && f.name <> Name proto_key && string_key f) fields;exact=false;
          index=Option.map (fun (i:index_signature) -> i.value)
            (List.find_opt (fun (i:index_signature) -> i.keys=Strings) indexes)}]
      | Named (id,args) ->
        if List.mem id seen then Proposal_diagnostics.unsupported "unguarded spread cycle";
        source_alternatives declarations (id::seen) (definition declarations id args)
      (* Each other operand's own enumerable properties are not what its
         type bounds. *)
      | Str | StrLit _ -> Proposal_diagnostics.unsupported "a spread copies the own enumerable properties of a plain object; \
          a string's are its characters at index keys, which no record states"
      | Shape {elements=Some _;_} -> Proposal_diagnostics.unsupported "a spread copies the own enumerable properties of a plain object; \
          an array's are its indices and whatever keys it carries, which no record states"
      (* A function's own enumerable properties are whatever was assigned to
         it: its type states its fields, and no other key. *)
      | Shape {fields;indexes=[];calls=_::_;elements=None} ->
        [{afields=List.filter (fun (f:Semantic.field) ->
            not (method_field f) && f.name <> Name proto_key && string_key f) fields;exact=false;index=None}]
      | Shape _ | Callable -> Proposal_diagnostics.unsupported "a spread copies the own enumerable properties of a plain object; \
          a value that may be a class, or a function with an index signature, owns what its type does not state"
      | Ctors _ -> Proposal_diagnostics.unsupported "a spread copies the own enumerable properties of a plain object; \
          a class value's are its static fields, which its construct signatures do not state"
      | _ -> Proposal_diagnostics.unsupported "a spread copies the own enumerable properties of a plain object; one of a string, an array, a function or a class value is outside the fragment") atoms
  | Union ts -> List.concat_map (source_alternatives declarations seen) ts
  | Meet _ | Rigid _ -> Proposal_diagnostics.unsupported "a spread of an intersection or a type parameter is outside the fragment"

(* A source's properties defined over an alternative's: a key the source
   surely has takes its type; one the alternative has keeps its own where the
   source never has it, or with the source's optional or index type where it
   may; a key only the source may have is optional where the alternative's
   keys are exact. A key either side may hold at an unknown type is not
   stated. *)
let merge_alternative (a:alternative) (b:alternative) : alternative =
  let find fs k = List.find_opt (fun (f:Semantic.field) -> f.name = k) fs in
  let names = List.fold_left (fun ns (f:Semantic.field) ->
    if List.mem f.name ns then ns else ns @ [f.name]) [] (a.afields @ b.afields) in
  let field name optional t = ({name;optional;read=t;write=Some t;host=false;receivers=[]} : Semantic.field) in
  let fields = List.filter_map (fun k ->
    match find b.afields k with
    | Some f when not f.optional -> Some (field k false f.read)
    | bf ->
      let b_maybe = match bf,b.index,k with
        | Some f,_,_ -> Some f.read
        | None,Some t,Name _ -> Some t
        | None,_,_ -> None in
      let b_never = bf = None && b.exact in
      match find a.afields k with
      | Some f when not f.optional ->
        if b_never then Some (field k false f.read)
        else Option.map (fun t -> field k false (union f.read t)) b_maybe
      | Some f ->
        if b_never then Some (field k true f.read)
        else Option.map (fun t -> field k true (union f.read t)) b_maybe
      (* A key the alternative may hold at its index: a dictionary owns no
         prototype, so the key is optional at either side's type. *)
      | None -> (match a.index,k with
        | Some ta,Name _ -> Option.map (fun t -> field k true (union ta t)) b_maybe
        | _ -> if a.exact then Option.map (field k true) b_maybe else None)) names in
  (* Where a side states an index and each side says what it gives under
     every string key, by an index or by its exact keys, the result states
     the index, at what either side and the string-keyed fields hold, and so
     does every string-keyed field: Lean's merge of a dictionary. *)
  match a.index,b.index with
  | (Some _,_ | _,Some _) when (a.index <> None || a.exact) && (b.index <> None || b.exact) ->
    let keyed (f:Semantic.field) = match f.name with Name _ -> true | Key _ -> false in
    let v = List.fold_left union (Atoms [])
      (Option.to_list a.index @ Option.to_list b.index
       @ List.map (fun (f:Semantic.field) -> f.read) (List.filter keyed fields)) in
    { afields=List.map (fun (f:Semantic.field) ->
        if keyed f then {f with read=v; write=Some v} else f) fields;
      exact=a.exact && b.exact; index=Some v }
  | _ -> { afields=fields; exact=a.exact && b.exact; index=None }

let alternative_type (a:alternative) =
  match a.index with
  | Some v -> Atoms [Shape {fields=a.afields;
      indexes=[{keys=Strings;value=v;writable=Some v}];calls=[];elements=None}]
  | None ->
    if a.exact && List.for_all (fun (f:Semantic.field) -> not f.optional) a.afields
    then Atoms [Exact a.afields] else record a.afields

