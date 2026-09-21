open Semantic

(* A substitution is proposal state for one call. Its domain is exactly the
   signature's quantified rigid identities; it is never embedded in [ty]. *)
type substitution = (rigid * ty) list

type instantiation = {
  substitution: substitution;
  params: ty list;
  result: ty;
  bounds: (ty * ty) list;
}

let unsupported s = Json.fail ("unsupported: " ^ s)

let rec substitute solution = function
  | Rigid identity as original ->
    Option.value (List.assoc_opt identity solution) ~default:original
  | Atoms atoms -> Atoms (List.map (substitute_atom solution) atoms)
  | Union types -> List.fold_left union (Atoms []) (List.map (substitute solution) types)
and substitute_atom solution = function
  | Shape shape -> Shape (substitute_shape solution shape)
  | atom -> atom
and substitute_shape solution shape = {
  fields=List.map (fun field -> {field with
    read=substitute solution field.read;
    write=Option.map (substitute solution) field.write}) shape.fields;
  calls=List.map (substitute_signature solution) shape.calls;
  elements=Option.map (fun sequence -> {
    sequence with
    required=List.map (substitute solution) sequence.required;
    optional_elements=List.map (substitute solution) sequence.optional_elements;
    rest=Option.map (substitute solution) sequence.rest}) shape.elements;
}
and substitute_signature solution signature =
  (* A nested quantifier shadows only its own identities. Outer solutions still
     pass through the nested scheme's bounds and body. *)
  let local = List.map (fun q -> q.identity) signature.quantified in
  let solution = List.filter (fun (identity,_) -> not (List.mem identity local)) solution in
  { quantified=List.map (fun q -> {q with bound=Option.map (substitute solution) q.bound})
      signature.quantified;
    params=List.map (substitute solution) signature.params;
    result=substitute solution signature.result }

let infer (signature:signature) actuals =
  if signature.quantified=[] then unsupported "generic inference requires a quantified signature";
  if List.length signature.params<>List.length actuals then
    unsupported "generic call argument count differs from its signature";
  let domain = List.map (fun q -> q.identity) signature.quantified in
  let solution = ref [] in
  let propose identity actual =
    if not (List.mem identity domain) then ()
    else match List.assoc_opt identity !solution with
      | None -> solution := (identity,actual) :: !solution
      | Some previous when previous=actual -> ()
      | Some _ -> unsupported ("incompatible inferences for " ^ identity.spelling) in
  let constrain expected actual = match expected with
    | Rigid identity -> propose identity actual
    | _ -> () in
  List.iter2 constrain signature.params actuals;
  List.iter (fun q -> if not (List.mem_assoc q.identity !solution) then
    unsupported ("cannot infer " ^ q.identity.spelling ^ " from call arguments"))
    signature.quantified;
  let substitution = List.rev !solution in
  let params = List.map (substitute substitution) signature.params in
  let result = substitute substitution signature.result in
  let bounds = List.filter_map (fun q -> Option.map (fun upper ->
    (List.assoc q.identity substitution,substitute substitution upper)) q.bound)
    signature.quantified in
  {substitution;params;result;bounds}
