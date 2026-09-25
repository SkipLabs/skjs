open Semantic

(* A substitution is proposal state for one call. Its domain is exactly the
   signature's quantified rigid identities; it is never embedded in [ty]. *)
type substitution = (rigid * type_argument) list

type instantiation = {
  substitution: substitution;
  result: ty;
}

let unsupported s = Json.fail ("unsupported: " ^ s)

let rec substitute solution = function
  | Rigid identity as original ->
    (match List.assoc_opt identity solution with
    | None -> original
    | Some (ValueArgument t) -> t
    | Some (PackArgument _) -> unsupported ("pack substitution used as a value type: " ^ identity.spelling))
  | Atoms atoms -> Atoms (List.map (substitute_atom solution) atoms)
  | Union types -> List.fold_left union (Atoms []) (List.map (substitute solution) types)
and substitute_atom solution = function
  | Shape shape -> Shape (substitute_shape solution shape)
  | Exact fields -> Exact (List.map (fun (field:Semantic.field) -> {field with
      read=substitute solution field.read;
      write=Option.map (substitute solution) field.write}) fields)
  | Named (id,args) -> Named (id,List.map (substitute solution) args)
  | Ctors signatures -> Ctors (List.map (substitute_signature solution) signatures)
  | (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
    | Bigint | Symbol) as atom -> atom
and substitute_pack solution = function
  | PackParameter identity as original ->
    (match List.assoc_opt identity solution with
    | None -> original
    | Some (PackArgument p) -> p
    | Some (ValueArgument _) -> unsupported ("value substitution used as an argument pack: " ^ identity.spelling))
  | Pack sequence -> Pack (substitute_sequence solution sequence)
and substitute_sequence solution sequence = {
  sequence with
  required=List.map (substitute solution) sequence.required;
  optional_elements=List.map (substitute solution) sequence.optional_elements;
  rest=Option.map (substitute solution) sequence.rest}
and substitute_argument solution = function
  | ValueArgument t -> ValueArgument (substitute solution t)
  | PackArgument p -> PackArgument (substitute_pack solution p)
and substitute_shape solution shape = {
  fields=List.map (fun field -> {field with
    read=substitute solution field.read;
    write=Option.map (substitute solution) field.write}) shape.fields;
  string_index=Option.map (fun (index:Semantic.index_signature) -> {
    value=substitute solution index.value;
    writable=Option.map (substitute solution) index.writable}) shape.string_index;
  calls=List.map (substitute_signature solution) shape.calls;
  elements=Option.map (substitute_sequence solution) shape.elements;
}
and substitute_signature solution signature =
  (* A nested quantifier shadows only its own identities. Outer solutions still
     pass through the nested scheme's bounds and body. *)
  let local = List.map (fun q -> q.identity) signature.quantified in
  let solution = List.filter (fun (identity,_) -> not (List.mem identity local)) solution in
  { quantified=List.map (fun q -> {q with bound=Option.map (substitute_argument solution) q.bound})
      signature.quantified;
    receiver=substitute solution signature.receiver;
    params=List.map (substitute solution) signature.params;
    variadic=Option.map (substitute solution) signature.variadic;
    rest_pack=Option.map (substitute_pack solution) signature.rest_pack;
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
  | Ctors a,Ctors b -> Some [Ctors (a @ b)]
  | Shape _,_ | _,Shape _ | Exact _,_ | _,Exact _ | Named _,_ | _,Named _
  | Ctors _,_ | _,Ctors _ -> None
  | Bigint,Bigint -> Some [Bigint] | Symbol,Symbol -> Some [Symbol]
  | (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | Symbol),
    (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | Symbol) -> Some []

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

(* [expand] gives a declaration's equation, to compare a class instance with
   the interface application a signature names (`new () => Mapper<K, V, K2, V2>`). *)
let infer ?receiver ?expected ?(expand = fun _ -> None) (signature:signature) actuals =
  if signature.quantified=[] then unsupported "generic inference requires a quantified signature";
  if signature.rest_pack<>None then unsupported "pack inference requires an argument-list candidate";
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
  let rec constrain ?(depth=0) left right =
    let constrain = constrain ~depth:(depth+1) in
    match local left,local right with
    | Some x,Some y -> edges := (x,y)::!edges
    | None,Some y -> y.lower <- add y.lower left
    | Some x,None -> x.upper <- add x.upper right
    | None,None when depth > 8 -> ()
    | None,None -> (match left,right with
      (* One declaration's applications: their arguments, both ways, as no
         variance is known here. *)
      | Atoms [Named (a,xs)],Atoms [Named (b,ys)] when a=b && List.length xs=List.length ys ->
      List.iter2 (fun x y -> constrain x y; constrain y x) xs ys
      | Atoms [Named _],_ | _,Atoms [Named _] ->
      let open_ t = match t with Atoms [Named _] -> expand t | _ -> Some t in
      (match open_ left,open_ right with
       | Some l,Some r when l<>left || r<>right -> constrain l r
       | _ -> ())
      (* A construct signature: parameters contravariant, instance covariant. *)
      | Atoms [Ctors [a]],Atoms [Ctors [e]] when a.quantified=[] && e.quantified=[] ->
      List.iteri (fun i p -> match List.nth_opt e.params i with
        | Some q -> constrain q p | None -> ()) a.params;
      constrain a.result e.result
      (* Records: each field the expected one names, at the actual's. *)
      | Atoms [Shape ({calls=[];elements=None;_} as a)],
      Atoms [Shape ({calls=[];elements=None;_} as e)] when e.fields<>[] ->
      List.iter (fun (f:field) -> match List.find_opt (fun (g:field) -> g.name=f.name) a.fields with
        | Some g -> constrain g.read f.read
        | None -> ()) e.fields
      | Atoms [Shape {calls=(_::_ as calls);fields=[];string_index=None;elements=None}],
      Atoms [Shape {calls=[e];fields=[];string_index=None;elements=None}]
        when e.quantified=[] && List.exists (fun (a:signature) -> a.quantified=[]
          && List.length a.params<=List.length e.params) calls ->
      (* A callback may take fewer parameters than it is offered: the
         positions it has are compared, the rest it ignores. Of several
         signatures, the first that fits is compared. *)
      let a = List.find (fun (a:signature) -> a.quantified=[]
        && List.length a.params<=List.length e.params) calls in
      constrain e.receiver a.receiver;
      List.iteri (fun i p -> constrain (List.nth e.params i) p) a.params;
      constrain a.result e.result
      (* An array's elements: a readonly target reads them, so covariantly; a
         writable one also takes writes, so both ways. *)
      | Atoms [Shape {elements=Some l;fields=[];calls=[];string_index=None}],
      Atoms [Shape {elements=Some r;fields=[];calls=[];string_index=None}]
        when List.length l.required=List.length r.required
          && List.length l.optional_elements=List.length r.optional_elements ->
      let pair x y = constrain x y; if not r.readonly then constrain y x in
      List.iter2 pair l.required r.required;
      List.iter2 pair l.optional_elements r.optional_elements;
      (match l.rest,r.rest with Some x,Some y -> pair x y | _ -> ())
      | _ -> ()) (* Unsupported structure contributes no guessed constraints;
                    Lean still checks the entire substituted signature. *) in
  List.iter2 (fun actual domain -> constrain actual domain) actuals domains;
  (* The receiver is an input like the actuals: the one passed must fit the
     signature's. *)
  Option.iter (fun r -> constrain r signature.receiver) receiver;
  (* Where the call's value is expected at a type, its result must fit it, as
     TypeScript infers from the return position too. *)
  Option.iter (fun t -> constrain signature.result t) expected;
  List.iter (fun (q:quantifier) ->
    Option.iter (function
      | ValueArgument t -> constrain (Rigid q.identity) t
      | PackArgument _ -> unsupported "pack inference requires an argument-list candidate") q.bound) signature.quantified;
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
  (* A literal joined with its primitive is the primitive: `0 | number` is
     `number`, the type a callback annotated with `number` states. *)
  let absorb = function
    | Atoms atoms when List.mem Top atoms -> Atoms [Top]
    | Atoms atoms ->
      Atoms (List.filter (function
        | NumLit _ -> not (List.mem Num atoms)
        | StrLit _ -> not (List.mem Str atoms)
        | _ -> true) atoms)
    | t -> t in
  let join = function [] -> None | first::rest -> Some (absorb (List.fold_left union first rest)) in
  (* If U has a chosen lower-bound join, an upper-only T <= U must also fit
     that choice. Propagating only U's declared uppers would miss this case. *)
  List.iter (fun (lower,upper) ->
    Option.iter (fun chosen -> lower.upper <- add lower.upper chosen) (join upper.lower)) !edges;
  saturate ();
  (* Each saturation only copies its finite seed sets, so it terminates
     even with cycles. Prefer joined lower bounds; upper-only candidates use a
     representable meet. Contradictions remain Lean obligations, not refusals. *)
  let substitution = List.map (fun v ->
    (* A variable below and above one type, as an invariant position makes
       it, is that type. Otherwise a graph bound is a legal (possibly less
       precise) instantiation for every value below it. Choosing it is only a
       proposal: Lean checks both the concrete argument against the
       instantiated parameter and the substitution against every bound. *)
    let declared_upper = List.find_opt (function
      | Atoms [Named (_,[])] -> true | _ -> false) v.upper in
    let candidate = match join v.lower,declared_upper with
      | Some t,_ when List.mem t v.upper -> Some t
      | _,(Some _ as chosen) -> chosen
      | (Some _ as chosen),None -> chosen
      | None,None -> upper_candidate v.upper in
    (* With no candidate at all, TypeScript infers `unknown`. *)
    v.identity,ValueArgument (Option.value candidate ~default:top)) variables in
  let result = substitute substitution signature.result in
  {substitution;result}
