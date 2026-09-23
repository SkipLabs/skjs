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
  string_index=Option.map (fun (index:Semantic.index_signature) -> {
    value=substitute solution index.value;
    writable=Option.map (substitute solution) index.writable}) shape.string_index;
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
    receiver=substitute solution signature.receiver;
    params=List.map (substitute solution) signature.params;
    variadic=Option.map (substitute solution) signature.variadic;
    result=substitute solution signature.result }

(* These are proposal constraints, not semantic type nodes or acceptance facts.
   Edges retain dependencies until all concrete bounds have propagated. *)
type variable = { identity: rigid; mutable lower: ty list; mutable upper: ty list }

(* Compute representable primitive intersections for upper-only inference.
   Different structural shapes are not assumed disjoint. A missing meet leaves
   a candidate to be validated, rather than inventing an intersection type. *)
let meet_atom a b =
  if a=b then Some [a] else match a,b with
  | Top,x | x,Top -> Some [x]
  | Num,NumLit _ -> Some [b] | NumLit _,Num -> Some [a]
  | Str,StrLit _ -> Some [b] | StrLit _,Str -> Some [a]
  | Shape _,_ | _,Shape _ -> None
  | (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _),
    (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _) -> Some []

let meet a b =
  if a=b then Some a else match a,b with
  | Atoms xs,Atoms ys ->
    let rec collect acc = function
      | [] -> Some (ground acc)
      | (x,y)::rest -> (match meet_atom x y with
          | Some atoms -> collect (atoms @ acc) rest
          | None -> None) in
    collect [] (List.concat_map (fun x -> List.map (fun y -> x,y) ys) xs)
  | _ -> None (* General intersections/rigid meets have no representation yet. *)

let upper_candidate = function
  | [] -> None
  | first::rest ->
    let intersection = List.fold_left (fun acc t -> Option.bind acc (fun a -> meet a t))
      (Some first) rest in
    Some (Option.value intersection ~default:first)

let infer ?receiver (signature:signature) actuals =
  if signature.quantified=[] then unsupported "generic inference requires a quantified signature";
  let domains = match signature.variadic with
    | None when List.length signature.params = List.length actuals -> signature.params
    | Some element when List.length signature.params <= List.length actuals ->
        signature.params @ List.init (List.length actuals - List.length signature.params) (fun _ -> element)
    | None | Some _ -> unsupported "generic call argument count differs from its signature" in
  let variables = List.map (fun (q:quantifier) ->
    {identity=q.identity;lower=[];upper=[]}) signature.quantified in
  let find identity = List.find_opt (fun (v:variable) -> v.identity=identity) variables in
  let local = function Rigid identity -> find identity | Atoms _ | Union _ -> None in
  let edges = ref [] in
  let add xs t = List.sort_uniq compare (t::xs) in
  (* constrain left right records left <= right. Callback parameters reverse
     the direction; callback results preserve it, at every nesting depth. *)
  let rec constrain left right = match local left,local right with
    | Some x,Some y -> edges := (x,y)::!edges
    | None,Some y -> y.lower <- add y.lower left
    | Some x,None -> x.upper <- add x.upper right
    | None,None -> (match left,right with
      | Atoms [Shape {calls=[a];fields=[];string_index=None;elements=None}],
      Atoms [Shape {calls=[e];fields=[];string_index=None;elements=None}]
        when a.quantified=[] && e.quantified=[]
          && List.length a.params=List.length e.params ->
      constrain e.receiver a.receiver;
      List.iter2 constrain e.params a.params;
      constrain a.result e.result
      | _ -> ()) (* Unsupported structure contributes no guessed constraints;
                    Lean still checks the entire substituted signature. *) in
  List.iter2 constrain actuals domains;
  (* The receiver is an input like the actuals: the one passed must fit the
     signature's. *)
  Option.iter (fun r -> constrain r signature.receiver) receiver;
  List.iter (fun (q:quantifier) ->
    Option.iter (constrain (Rigid q.identity)) q.bound) signature.quantified;
  let saturate () =
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter (fun (lower,upper) ->
        let lows=List.sort_uniq compare (lower.lower @ upper.lower)
        and highs=List.sort_uniq compare (lower.upper @ upper.upper) in
        if lows<>upper.lower || highs<>lower.upper then changed := true;
        upper.lower <- lows;
        lower.upper <- highs) !edges
    done in
  saturate ();
  let join = function [] -> None | first::rest -> Some (List.fold_left union first rest) in
  (* If U has a chosen lower-bound join, an upper-only T <= U must also fit
     that choice. Propagating only U's declared uppers would miss this case. *)
  List.iter (fun (lower,upper) ->
    Option.iter (fun chosen -> lower.upper <- add lower.upper chosen) (join upper.lower)) !edges;
  saturate ();
  (* Each saturation only copies its finite seed sets, so it terminates
     even with cycles. Prefer joined lower bounds; upper-only candidates use a
     representable meet. Contradictions remain Lean obligations, not refusals. *)
  let substitution = List.map (fun v ->
    let candidate = match join v.lower with
      | Some _ as chosen -> chosen
      | None -> upper_candidate v.upper in
    match candidate with
    | Some t -> v.identity,t
    | None -> unsupported ("cannot infer " ^ v.identity.spelling ^ " from call arguments or bounds")) variables in
  let params = List.map (substitute substitution) signature.params in
  let result = substitute substitution signature.result in
  let bounds = List.filter_map (fun (q:quantifier) -> Option.map (fun upper ->
    (List.assoc q.identity substitution,substitute substitution upper)) q.bound)
    signature.quantified in
  {substitution;params;result;bounds}
