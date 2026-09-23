open Json
open Semantic
open Environment
open Source
open Proposal
let unsupported s = fail ("unsupported: " ^ s)
let encode (proposal : Proposal.t) =
  (* The graph is just the existing SourceClaims wire format, interned structurally. *)
  (* Empty reserved rows are references, never producer-authored equations.
     Lean replaces them from the snapshotted declarations before extraction. *)
  let imports = proposal.program.imports in
  let rows = ref ([Array [String "nul"]; Array [Object ["boolLit",Object ["value",Bool true]]];
                   Array [Object ["boolLit",Object ["value",Bool false]]]; Array [String "undef"]]
                  @ List.map (fun _ -> Array []) imports)
  in
  let imported_label id args =
    if args <> [] then unsupported "parameterized imported graph needs substitution";
    let rec find i = function
      | [] -> unsupported ("unknown imported declaration " ^ id)
      | (d:Source.imported_definition)::rest ->
        if d.id=id then i+4 else find (i+1) rest in
    find 0 imports in
  let intern row =
    let rec find n = function [] -> rows := !rows @ [row]; n
      | r::rs -> if r=row then n else find (n+1) rs in find 0 !rows
  in
  let rec labels = function Rigid _ | Union _ -> unsupported "rigid type nested in a graph type"
    | Atoms atoms -> Array (List.map int (List.sort_uniq compare (List.map atom_label atoms)))
  and atom_label = function
    | Nul -> 0 | True -> 1 | False -> 2 | Undef -> 3
    | Num -> intern (Array [String "num"]) | Str -> intern (Array [String "str"])
    | NumLit bits -> intern (Array [Object ["numLit",Object ["bits",String (Printf.sprintf "%Lu" bits)]]])
    | StrLit value -> intern (Array [Object ["strLit",Object ["value",String value]]])
    | Top -> intern (Array [String "top"])
    | Named (id,args) -> imported_label id args
    | Shape shape ->
      let writes,reads = List.partition (fun (f:Semantic.field) -> f.write <> None) shape.fields in
      let fields writable fs = Array (List.map (fun (f:Semantic.field) ->
        if f.optional then unsupported "optional presence has no SourceClaims encoding yet";
        if writable && f.write <> Some f.read then unsupported "asymmetric read/write capability export";
        Array [String f.name;labels f.read]) fs) in
      let fields,views = fields true writes,fields false reads in
      List.iter (fun (a:Semantic.signature) ->
        if a.quantified <> [] then unsupported "quantified callable claim encoding") shape.calls;
      (* Fixed arrows and variadic signatures of one value share its clause; the
         variadic list is left out when empty, its one spelling of none. *)
      let fixed = List.filter (fun (a:Semantic.signature) -> a.variadic = None) shape.calls in
      let arrows = Array (List.map (fun (a:Semantic.signature) ->
        Array [labels a.receiver;Array [Array (List.map labels a.params);labels a.result]]) fixed) in
      let variadic = List.filter_map (fun (a:Semantic.signature) ->
        Option.map (fun element -> Array [labels a.receiver;Array [Array (List.map labels a.params);
          Array [labels element;labels a.result]]]) a.variadic) shape.calls in
      let calls = ("arrows",arrows) :: (if variadic = [] then [] else ["variadic",Array variadic]) in
      let clause = match shape.elements with
        | Some sequence ->
          if shape.fields <> [] || shape.calls <> [] || shape.string_index <> None
          then unsupported "array with additional fields, indexes or calls";
          let store = intern (Array [Object ["list",Object ["first",Object [
            "required",Array (List.map labels sequence.required);
            "optional",Array (List.map labels sequence.optional_elements);
            "rest",(match sequence.rest with None -> Null | Some t -> labels t);
            "readonly",Bool sequence.readonly];"rest",Array []]]]) in
          let storage = Array [Array [String "[]";Array [int store]]] in
          Object ["refs",Object ["first",(if sequence.readonly then Array [] else storage);
            "rest",Array [];"views",(if sequence.readonly then storage else Array [])]]
        | None -> match shape.fields,shape.string_index,shape.calls with
          | _,Some index,[] ->
            if index.writable <> None then unsupported "mutable string index signature";
            Object ["dict",Object ["first",fields;"rest",Array [];"views",views;
              "indexes",Array [labels index.value]]]
          | _,None,[] -> Object ["refs",Object ["first",fields;"rest",Array [];"views",views]]
          | [],None,_ -> Object ["arrs",Object calls]
          | _,_,_ ->
            if reads <> [] then unsupported "callable with readonly fields";
            Object ["callable",Object (["first",fields;"rest",Array []] @ calls)] in
      intern (Array [clause])
  in
  (* A callable whose signature mentions a rigid parameter has no graph row:
     it is exported in the scheme form, with its own binders (possibly none),
     so a returned closure can retain an outer binder in its result. *)
  let rec contains_symbolic = function
    | Rigid _ -> true
    | Union ts -> List.exists contains_symbolic ts
    | Atoms atoms -> List.exists (function
        | Named (_,args) -> List.exists contains_symbolic args
        | Shape s ->
          List.exists (fun (f:Semantic.field) -> contains_symbolic f.read
            || Option.fold ~none:false ~some:contains_symbolic f.write) s.fields
          || Option.fold ~none:false ~some:(fun (i:Semantic.index_signature) ->
              contains_symbolic i.value || Option.fold ~none:false ~some:contains_symbolic i.writable) s.string_index
          || List.exists (fun (a:Semantic.signature) ->
              List.exists contains_symbolic (a.receiver :: a.result :: a.params @ Option.to_list a.variadic)
              || List.exists (fun (q:Semantic.quantifier) ->
                  Option.fold ~none:false ~some:contains_symbolic q.bound) a.quantified) s.calls
          || (match s.elements with None -> false | Some e ->
              List.exists contains_symbolic (e.required @ e.optional_elements @ Option.to_list e.rest))
        | _ -> false) atoms
  in
  let rec claim_type = function
    | Rigid n -> Object ["param",String n.spelling]
    | Atoms [Shape {fields=[];string_index=None;calls=[signature];elements=None}]
        when signature.quantified <> [] || List.exists contains_symbolic
          (signature.receiver :: signature.result :: signature.params @ Option.to_list signature.variadic) ->
      let type_params = Array (List.map (fun (q:Semantic.quantifier) -> Object [
        "name",String q.identity.spelling;
        "bound",(match q.bound with None -> Null | Some t -> claim_type t)])
        signature.quantified) in
      Object ["scheme",Object ["typeParams",type_params;
        "this",claim_type signature.receiver;
        "params",Array (List.map claim_type signature.params);
        "rest",(match signature.variadic with None -> Null | Some t -> claim_type t);
        "result",claim_type signature.result]]
    | Atoms [Shape {fields=[];string_index=None;calls=[];elements=Some
        {required=[];optional_elements=[];rest=Some element;readonly=false}}]
        when contains_symbolic element -> Object ["array",claim_type element]
    | Atoms (_::_::_ as atoms) when contains_symbolic (Atoms atoms) ->
      let rigid, ground = List.partition (fun a -> contains_symbolic (Atoms [a])) atoms in
      let parts = List.map (fun a -> Atoms [a]) rigid @
        (if ground=[] then [] else [Atoms ground]) in
      Object ["union", Array (List.map claim_type parts)]
    | Union ts when List.exists contains_symbolic ts ->
      let rigid, ground = List.partition contains_symbolic ts in
      Object ["union", Array (List.map claim_type (rigid @ ground))]
    | (Atoms _ | Union _) as t -> labels t
  in
  (* The substitution is exported so Lean re-checks the elimination it names,
     rather than re-inferring one of its own. A site that calls no quantified
     callable omits the field: unlike `current`, its absence asserts nothing. *)
  let instantiate = function
    | None -> []
    | Some subst -> ["instantiate",Array (List.map (fun (name,t) ->
        Object ["name",String name; "type",claim_type t]) subst)]
  in
  let point t extra = Object (extra @ ["type",claim_type t; "current",Null])
  in
  let named (n,b) = point (binding_type b) ["name",String n]

  in
  let functions = List.map (fun (f : Proposal.function_claim) ->
    let source = f.source in
    let expressions row = Array (List.map (fun (e : Proposal.expression) ->
      Object (["pos",e.pos; "type",claim_type e.type_; "current",Null]
        @ instantiate e.instantiation)) row) in
    (* One set of interior claims per advertised signature, in signature order,
       stated only by a closure that advertises more than one. *)
    let entries es = Array (List.map (fun (e : Proposal.entry) ->
      Object ["start",e.start;"bindings",Array (List.map named e.bindings)]) es) in
    let arrows = if f.arrows = [] then [] else
      ["arrows",Array (List.map (fun (pos,rows) ->
        Object ["pos",pos;"rows",Array (List.map (fun (o : Proposal.overlay) ->
          Object ["expressions",expressions o.row_expressions;
                  "entries",entries o.row_entries]) rows)]) f.arrows)] in
    Object (["name",String source.name; "namePos",source.name_pos;
      "params",Array (List.map (fun (n,t) -> named (n,Value t)) source.params);
      "result",claim_type source.result;
      "entries",entries f.entries;
      "expressions",expressions f.expressions]
      @ arrows)) proposal.functions in
  Object ["file",proposal.program.file; "sourceSha256",proposal.program.digest;
    "types",Array !rows; "functions",Array functions]
