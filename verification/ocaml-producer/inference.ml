open Semantic

(* A substitution is proposal state for one call. Its domain is exactly the
   signature's quantified rigid identities; it is never embedded in [ty]. *)
type substitution = (rigid * type_argument) list

type instantiation = {
  substitution: substitution;
  result: ty;
}

let unsupported s = Json.fail ("unsupported: " ^ s)

(* [meet] rebuilds an intersection of a declaration's equation (`Meet`) once
   its operands are substituted: by default it stays one, for the
   declaration's expansion to resolve (`Type_queries.definition`). *)
let rec substitute ?meet solution = function
  | Rigid identity as original ->
    (match List.assoc_opt identity solution with
    | None -> original
    | Some (ValueArgument t) -> t
    | Some (PackArgument _) -> unsupported ("pack substitution used as a value type: " ^ identity.spelling))
  | Atoms atoms -> Atoms (List.map (substitute_atom ?meet solution) atoms)
  | Union types -> List.fold_left union (Atoms []) (List.map (substitute ?meet solution) types)
  | Meet (t,ts) ->
    let t = substitute ?meet solution t and ts = List.map (substitute ?meet solution) ts in
    (match meet with Some meet -> meet t ts | None -> Meet (t,ts))
and substitute_atom ?meet solution = function
  | Shape shape -> Shape (substitute_shape ?meet solution shape)
  | Exact fields -> Exact (List.map (fun (field:Semantic.field) -> {field with
      read=substitute ?meet solution field.read;
      write=Option.map (substitute ?meet solution) field.write;
      receivers=List.map (substitute ?meet solution) field.receivers}) fields)
  | Named (id,args) -> Named (id,List.map (substitute ?meet solution) args)
  | Ctors signatures -> Ctors (List.map (substitute_signature ?meet solution) signatures)
  | (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
    | Bigint | Symbol | BigintLit _ | Callable) as atom -> atom
and substitute_pack ?meet solution = function
  | PackParameter identity as original ->
    (match List.assoc_opt identity solution with
    | None -> original
    | Some (PackArgument p) -> p
    | Some (ValueArgument _) -> unsupported ("value substitution used as an argument pack: " ^ identity.spelling))
  | Pack sequence -> Pack (substitute_sequence ?meet solution sequence)
and substitute_sequence ?meet solution sequence = {
  sequence with
  required=List.map (substitute ?meet solution) sequence.required;
  optional_elements=List.map (substitute ?meet solution) sequence.optional_elements;
  rest=Option.map (substitute ?meet solution) sequence.rest}
and substitute_argument ?meet solution = function
  | ValueArgument t -> ValueArgument (substitute ?meet solution t)
  | PackArgument p -> PackArgument (substitute_pack ?meet solution p)
and substitute_shape ?meet solution shape = {
  fields=List.map (fun field -> {field with
    read=substitute ?meet solution field.read;
    write=Option.map (substitute ?meet solution) field.write;
    receivers=List.map (substitute ?meet solution) field.receivers}) shape.fields;
  indexes=List.map (fun (index:Semantic.index_signature) -> {index with
    value=substitute ?meet solution index.value;
    writable=Option.map (substitute ?meet solution) index.writable}) shape.indexes;
  calls=List.map (substitute_signature ?meet solution) shape.calls;
  elements=Option.map (substitute_sequence ?meet solution) shape.elements;
}
and substitute_signature ?meet solution signature =
  (* A nested quantifier shadows only its own identities. Outer solutions still
     pass through the nested scheme's bounds and body. *)
  let local = List.map (fun q -> q.identity) signature.quantified in
  let solution = List.filter (fun (identity,_) -> not (List.mem identity local)) solution in
  { signature with quantified=List.map (fun q -> {q with
      bound=Option.map (substitute_argument ?meet solution) q.bound;
      default=Option.map (substitute ?meet solution) q.default})
      signature.quantified;
    receiver=substitute ?meet solution signature.receiver;
    params=List.map (substitute ?meet solution) signature.params;
    variadic=Option.map (substitute ?meet solution) signature.variadic;
    rest_pack=Option.map (substitute_pack ?meet solution) signature.rest_pack;
    result=substitute ?meet solution signature.result }

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
  | Bigint,BigintLit _ -> Some [b] | BigintLit _,Bigint -> Some [a]
  | Ctors a,Ctors b -> Some [Ctors (a @ b)]
  | Shape _,_ | _,Shape _ | Exact _,_ | _,Exact _ | Named _,_ | _,Named _
  | Ctors _,_ | _,Ctors _ | Callable,_ | _,Callable -> None
  | Bigint,Bigint -> Some [Bigint] | Symbol,Symbol -> Some [Symbol]
  | (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | Symbol | BigintLit _),
    (Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | Symbol | BigintLit _) -> Some []

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
  let local = function Rigid identity -> find identity | Atoms _ | Union _ | Meet _ -> None in
  let edges = ref [] in
  let add xs t = List.sort_uniq compare (t::xs) in
  (* constrain left right records left <= right. Callback parameters reverse
     the direction; callback results preserve it, at every nesting depth. *)
  let callable = function Shape {calls=_::_;_} -> true | _ -> false in
  (* The binders of generic methods compared below: they are bound there, so
     a bound mentioning one fixes no binder of the call. *)
  let foreign = ref [] in
  let alien t = !foreign <> []
    && substitute (List.map (fun id -> id,ValueArgument (Atoms [])) !foreign) t <> t in
  let rec constrain ?(depth=0) left right =
    let constrain = constrain ~depth:(depth+1) in
    match local left,local right with
    | Some x,Some y -> edges := (x,y)::!edges
    | None,Some y -> if not (alien left) then y.lower <- add y.lower left
    | Some x,None -> if not (alien right) then x.upper <- add x.upper right
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
      (* A construct signature: parameters contravariant, instance covariant.
         A class's own signature is its first; the others it is offered give
         an interface's instance, which fixes no binder the own one does not. *)
      | Atoms [Ctors (a::_)],Atoms [Ctors [e]] when a.quantified=[] && e.quantified=[] ->
      List.iteri (fun i p -> match List.nth_opt e.params i with
        | Some q -> constrain q p | None -> ()) a.params;
      constrain a.result e.result
      (* Records: each field the expected one names, at the actual's. *)
      | Atoms [Shape ({calls=[];elements=None;_} as a)],
      Atoms [Shape ({calls=[];elements=None;_} as e)] when e.fields<>[] ->
      List.iter (fun (f:field) -> match List.find_opt (fun (g:field) -> g.name=f.name) a.fields with
        | Some g -> constrain g.read f.read
        | None -> ()) e.fields
      (* Dictionaries: each index the expected one states, at the actual's
         index over the same keys, read covariantly, and a writable one
         written too. *)
      | Atoms [Shape ({calls=[];elements=None;_} as a)],
      Atoms [Shape ({calls=[];elements=None;fields=[];_} as e)] when e.indexes<>[] ->
      List.iter (fun (i:index_signature) ->
        match List.find_opt (fun (j:index_signature) -> j.keys=i.keys) a.indexes with
        | Some j -> constrain j.value i.value; if i.writable <> None then constrain i.value j.value
        | None -> ()) e.indexes
      | Atoms [Shape {calls=(_::_ as calls);fields=[];indexes=[];elements=None}],
      Atoms [Shape {calls=[e];fields=[];indexes=[];elements=None}]
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
      (* Two generic methods binding as many parameters, `then` of
         `Promise<number>` at `then` of `PromiseLike<T>`: compared with the
         source's binders renamed to the target's, parameters contravariant
         and results covariant. *)
      | Atoms [Shape {calls=[a];fields=[];indexes=[];elements=None}],
      Atoms [Shape {calls=[e];fields=[];indexes=[];elements=None}]
        when a.quantified<>[] && List.length a.quantified=List.length e.quantified
          && List.length a.params=List.length e.params ->
      let renaming = List.map2 (fun (x:quantifier) (y:quantifier) ->
        x.identity,ValueArgument (Rigid y.identity)) a.quantified e.quantified in
      foreign := List.map (fun (q:quantifier) -> q.identity) e.quantified @ !foreign;
      let a = substitute_signature renaming {a with quantified=[]} in
      List.iter2 (fun p q -> constrain q p) a.params e.params;
      constrain a.result e.result
      (* Callables at a union with one callable arm, an optional callback
         (`((reason: any) => R | PromiseLike<R>) | null | undefined`): the
         callables are compared with that arm, as the other arms admit no
         function. *)
      | Atoms xs,Atoms ys
        when (List.length xs > 1 || List.length ys > 1)
          && List.exists callable xs && List.length (List.filter callable ys) = 1 ->
      constrain (Atoms (List.filter callable xs)) (Atoms (List.filter callable ys))
      (* An array's elements: a readonly target reads them, so covariantly; a
         writable one also takes writes, so both ways. *)
      | Atoms [Shape {elements=Some l;fields=[];calls=[];indexes=[]}],
      Atoms [Shape {elements=Some r;fields=[];calls=[];indexes=[]}]
        when List.length l.required=List.length r.required
          && List.length l.optional_elements=List.length r.optional_elements ->
      let pair x y = constrain x y; if not r.readonly then constrain y x in
      List.iter2 pair l.required r.required;
      List.iter2 pair l.optional_elements r.optional_elements;
      (match l.rest,r.rest with Some x,Some y -> pair x y | _ -> ())
      (* A tuple at an array of any length: each of its positions is an
         element (`[string, number]` at `readonly T[]` gives `T` both). *)
      | Atoms [Shape {elements=Some l;fields=[];calls=[];indexes=[]}],
      Atoms [Shape {elements=Some ({required=[];optional_elements=[];rest=Some y;_} as r);
                    fields=[];calls=[];indexes=[]}] ->
      List.iter (fun x -> constrain x y; if not r.readonly then constrain y x)
        (l.required @ l.optional_elements @ Option.to_list l.rest)
      (* Records at a union of records, a discriminated one: each record at
         the one arm whose literal-typed required fields it holds at the same
         literals, as TypeScript matches a discriminated union's constituent
         (`{ kind: "some"; value: number }` at `Option<T>` gives `T :=
         number`). A record matching no arm, or several, fixes nothing. *)
      | Atoms (_::_ as xs),Atoms (_::_::_ as ys)
        when List.for_all (function Shape {calls=[];elements=None;_} -> true | _ -> false) (xs @ ys) ->
        let literal = function
          | Atoms [(StrLit _ | NumLit _ | True | False | Nul | Undef | BigintLit _)] -> true
          | _ -> false in
        let matches x y = match x,y with
          | Shape a,Shape e ->
            let tags = List.filter (fun (f:field) -> not f.optional && literal f.read) e.fields in
            tags <> [] && List.for_all (fun (f:field) ->
              List.exists (fun (g:field) -> g.name=f.name && g.read=f.read) a.fields) tags
          | _ -> false in
        List.iter (fun x -> match List.filter (matches x) ys with
          | [y] -> constrain (Atoms [x]) (Atoms [y])
          | _ -> ()) xs
      (* A union is below a type where each of its parts is. *)
      | Union parts,_ -> List.iter (fun part -> constrain part right) parts
      (* A type below a union of several bare binders, `T | U`, is taken
         below each: an instance at least as wide as the one needed. *)
      | _,Union arms when arms <> [] && List.for_all (fun a -> local a <> None) arms ->
        List.iter (fun arm -> constrain left arm) arms
      (* A union with one bare binder among its arms, `A | null` or
         `Promise<T> | U`, as TypeScript infers it: each part of the actual
         goes to an arm of its own kind (an object part to an object arm
         over a binder, any part to an arm naming it), and every other part
         to the binder, so `string | null` gives `A := string`. An arm no
         part reaches receives the empty type, so the binders it holds are
         inferred as `never` where nothing else constrains them. *)
      | _,Union arms when List.length (List.filter (fun a -> local a <> None) arms) = 1 ->
        let rec pieces = function
          | Atoms xs -> List.map (fun x -> Atoms [x]) xs
          | Union ts -> List.concat_map pieces ts
          | t -> [t] in
        let objective = function
          | Named _ | Shape _ | Exact _ | Ctors _ | Callable -> true
          | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
          | Bigint | Symbol | BigintLit _ -> false in
        (* An object part goes to an arm whose binders it can fix; a
           ground arm takes only a part it names. *)
        let open_arm = Semantic.mentions_rigid in
        let heads piece arm = match piece,arm with
          | Atoms [x],Atoms ys when objective x && open_arm arm -> List.exists objective ys
          | Atoms [x],Atoms ys -> List.mem x ys
          | _ -> false in
        (* The actual through its declarations, `Maybe<string>` as
           `string | null`, where that tells some part apart: a declaration
           none of whose atoms an arm names goes whole. *)
        let named = List.concat_map (function
          | Atoms xs as a when not (Semantic.mentions_rigid a) -> xs
          | _ -> []) arms in
        let rec opened depth t = if depth = 0 then t else match t with
          | Atoms [Named _] -> (match expand t with Some e -> opened (depth-1) e | None -> t)
          | Union ts -> List.fold_left union (Atoms []) (List.map (opened (depth-1)) ts)
          | t -> t in
        let parts = pieces (match opened 4 left with
          | Atoms xs as o when List.exists (fun x -> List.mem x named) xs -> o
          | _ -> left) in
        let owner piece = match List.find_opt (fun a -> local a = None && heads piece a) arms with
          | Some a -> a
          | None -> List.find (fun a -> local a <> None) arms in
        (* A part holding a generic member, a library interface read as its
           shape, is no instance a claim can state: where one would go to the
           bare binder, the union proposes nothing. *)
        let rec generic = function
          | Atoms atoms -> List.exists (function
              | Shape sh -> List.exists (fun (s:signature) -> s.quantified <> []) sh.calls
                  || List.exists (fun (f:field) -> generic f.read) sh.fields
              | _ -> false) atoms
          | Union ts -> List.exists generic ts
          | Rigid _ | Meet _ -> false in
        if not (List.exists (fun piece -> generic piece && local (owner piece) <> None) parts) then
        List.iter (fun arm ->
          let received = List.filter (fun piece -> owner piece = arm) parts in
          match received with
          | [] -> let rec binders = function
              | Rigid _ as t -> Option.to_list (local t)
              | Union ts -> List.concat_map binders ts
              | Atoms atoms -> List.concat_map (function
                  | Named (_,args) -> List.concat_map binders args
                  | _ -> []) atoms
              | Meet _ -> [] in
            List.iter (fun (v:variable) -> v.lower <- add v.lower (Atoms [])) (binders arm)
          | received -> List.iter (fun piece -> constrain piece arm) received) arms
      (* A type below an intersection is below each operand: `"fixed"` at
         `T & "fixed"` is a lower bound of `T`. *)
      | _,Meet (t,ts) -> List.iter (fun part -> constrain left part) (t::ts)
      | _ -> ()) (* Unsupported structure contributes no guessed constraints;
                    Lean still checks the entire substituted signature. *) in
  List.iter2 (fun actual domain -> constrain actual domain) actuals domains;
  (* The receiver is an input like the actuals: the one passed must fit the
     signature's. *)
  Option.iter (fun r -> constrain r signature.receiver) receiver;
  (* Where the call's value is expected at a type, its result must fit it, as
     TypeScript infers from the return position too. *)
  Option.iter (fun t -> constrain signature.result t) expected;
  let unconstrained = List.filter_map (fun (v:variable) ->
    if v.lower = [] && v.upper = []
       && not (List.exists (fun ((a:variable),(b:variable)) ->
         a.identity = v.identity || b.identity = v.identity) !edges)
    then Some v.identity else None) variables in
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
        | BigintLit _ -> not (List.mem Bigint atoms)
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
  let primitive = function
    | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Bigint | BigintLit _ -> true
    | _ -> false in
  (* An array of any length whose elements are primitives. *)
  let plain_array = function
    | Shape {elements=Some {required=[];optional_elements=[];rest=Some (Atoms xs);_};
             fields=[];calls=[];indexes=[]} -> List.for_all primitive xs
    | _ -> false in
  (* Whether a declared bound has an arm that is an array of any length,
     through its declarations. *)
  let rec has_arm ?(depth=0) arm t = depth < 4 && match t with
    | Atoms atoms -> List.exists (function
        | Named _ as a -> (match expand (Atoms [a]) with
          | Some e -> has_arm ~depth:(depth+1) arm e
          | None -> false)
        | a -> arm a) atoms
    | Union ts -> List.exists (has_arm ~depth:(depth+1) arm) ts
    | _ -> false in
  let has_plain_array = has_arm (function Shape {elements=Some {rest=Some _;_};_} -> true | _ -> false) in
  (* A tuple: an array of fixed positions. *)
  let tuple = function
    | Shape {elements=Some {rest=None;_};fields=[];calls=[];indexes=[]} -> true
    | _ -> false in
  let substitution = List.map (fun v ->
    (* A variable below and above one type, as an invariant position makes
       it, is that type. Otherwise a graph bound is a legal (possibly less
       precise) instantiation for every value below it. Choosing it is only a
       proposal: Lean checks both the concrete argument against the
       instantiated parameter and the substitution against every bound. *)
    let declared_upper = List.find_opt (function
      | Atoms [Named (_,[])] -> true | _ -> false) v.upper in
    let candidate = match join v.lower,declared_upper with
      (* A join of primitives an explicit bound of literals does not admit
         (`number` at `K extends 0 | 1`): the bound, as TypeScript keeps the
         literals the constraint names. *)
      | Some (Atoms xs),_ when xs <> [] && List.exists (function
               | Atoms ys -> ys <> [] && List.for_all primitive ys
                 && List.exists (fun x -> not (List.mem x ys)) xs
                 && List.for_all (fun x -> List.mem x ys || List.exists (fun y -> match x,y with
                     | Num,NumLit _ | Str,StrLit _ | Bigint,BigintLit _ -> true
                     | _ -> false) ys) xs
               | _ -> false) v.upper -> upper_candidate v.upper
      | Some t,_ when List.mem t v.upper -> Some t
      (* Primitives below a declared bound: the binder is what they are, as
         TypeScript infers it, not the bound (`Y extends boolean | string`
         at "hello" is "hello"), and so are arrays of primitives
         (`S extends number[] | string` at `[1, 2, 3]` is `number[]`), and
         tuples below a bound with a tuple arm (`S extends [number, number]
         | string` at `[1, 2]` is `[number, number]`). *)
      | Some (Atoms atoms as t),Some bound when atoms <> [] && List.for_all (fun a ->
          primitive a || (plain_array a && has_plain_array bound)
          || (tuple a && has_arm tuple bound)) atoms -> Some t
      | _,(Some _ as chosen) -> chosen
      | (Some _ as chosen),None -> chosen
      | None,None -> upper_candidate v.upper in
    (* Literals inferred for an unbounded binder that the result does not
       return bare widen, as TypeScript widens such a binder's literal
       candidates (`box<T>(x: T): Box<T>` at `42` is `Box<number>`, while
       `id<T>(x: T): T` at `42` is `42`). *)
    let rec bare = function
      | Rigid r -> r = v.identity
      | Union ts -> List.exists bare ts
      | Atoms _ | Meet _ -> false in
    let unbounded = List.exists (fun (q:quantifier) -> q.identity = v.identity && q.bound = None)
      signature.quantified
      (* Nor a binder another's bound names, whose choice that one fits. *)
      && not (List.exists (fun ((a:variable),(b:variable)) ->
        a.identity = v.identity || b.identity = v.identity) !edges) in
    (* The widened type must still be below every upper bound met. *)
    let admitted w = List.for_all (fun u -> match u,w with
      | Atoms us,Atoms ws -> List.mem Top us || List.for_all (fun x -> List.mem x us) ws
      | _ -> false) v.upper in
    let candidate = match candidate with
      | Some t when unbounded && candidate = join v.lower && not (bare signature.result)
                    && admitted (widen t) -> Some (widen t)
      | c -> c in
    (* With no candidate at all, TypeScript infers `unknown`. *)
    v.identity,ValueArgument (Option.value candidate ~default:top)) variables in
  (* A binder no actual, receiver or expected type constrains takes its
     declared default, at the other binders' instances, as TypeScript does
     (`then`'s `TResult2 = never`). A default names only earlier binders, so
     one pass in declaration order instantiates each. *)
  let substitution = List.fold_left (fun substitution (q:quantifier) ->
    match q.default with
    | Some default when List.mem q.identity unconstrained ->
      List.map (fun (identity,argument) ->
        if identity = q.identity then identity,ValueArgument (substitute substitution default)
        else identity,argument) substitution
    | _ -> substitution) substitution signature.quantified in
  let result = substitute substitution signature.result in
  {substitution;result}
