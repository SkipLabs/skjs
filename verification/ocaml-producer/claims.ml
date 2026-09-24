open Json
open Semantic
open Environment
open Source
open Proposal
(* A property key as the claim wire spells it: the decoding of
   `Source.property_key`. *)
let key_json = function
  | Name name -> String name
  | Key i -> Object ["symbol",int i]

let unsupported s = fail ("unsupported: " ^ s)
let encode (proposal : Proposal.t) =
  (* The graph is just the existing SourceClaims wire format, interned structurally. *)
  (* Empty reserved rows are references, never producer-authored equations.
     Lean replaces them from the snapshotted declarations before extraction. *)
  let declarations = proposal.program.declarations in
  let rows = ref ([Array [String "nul"]; Array [Object ["boolLit",Object ["value",Bool true]]];
                   Array [Object ["boolLit",Object ["value",Bool false]]]; Array [String "undef"]]
                  @ List.filter_map (fun (d:Source.declaration) ->
                    if d.parameters=[] then Some (Array []) else None) declarations)
  in
  let active_imports = ref [] in
  (* The row reserved for an application of a declaration whose equation has
     methods: their receiver is that application, so it needs its label
     before its equation is expanded, as Lean reserves it. *)
  let applications = ref [] in
  let intern row =
    let rec find n = function [] -> rows := !rows @ [row]; n
      | r::rs -> if r=row then n else find (n+1) rs in find 0 !rows
  in
  let rec labels = function Rigid _ | Union _ -> unsupported "rigid type nested in a graph type"
    | Atoms atoms -> Array (List.map int (List.sort_uniq compare (List.concat_map atom_labels atoms)))
  and atom_labels = function
    | Nul -> [0] | True -> [1] | False -> [2] | Undef -> [3]
    | Num -> [intern (Array [String "num"])] | Str -> [intern (Array [String "str"])]
    | Bigint -> [intern (Array [String "bigint"])] | Symbol -> [intern (Array [String "symbol"])]
    | NumLit bits -> [intern (Array [Object ["numLit",Object ["bits",String (Printf.sprintf "%Lu" bits)]]])]
    | StrLit value -> [intern (Array [Object ["strLit",Object ["value",String value]]])]
    | Top -> [intern (Array [String "top"])]
    | Named (id,args) -> declaration_labels id args
    | Shape shape ->
      let writes,reads = List.partition (fun (f:Semantic.field) -> f.write <> None) shape.fields in
      let fields writable fs = Array (List.map (fun (f:Semantic.field) ->
        if f.optional then unsupported "optional presence has no SourceClaims encoding yet";
        if writable && f.write <> Some f.read then unsupported "asymmetric read/write capability export";
        Array [key_json f.name;labels f.read]) fs) in
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
          | _,Some _,_ -> unsupported "callable with string index needs a combined clause"
          | _,None,[] -> Object ["refs",Object ["first",fields;"rest",Array [];"views",views]]
          | [],None,_ -> Object ["arrs",Object calls]
          | _,_,_ ->
            if reads <> [] then unsupported "callable with readonly fields";
            Object ["callable",Object (["first",fields;"rest",Array []] @ calls)] in
      [intern (Array [clause])]
  and declaration_labels id args =
    let rec find i = function
      | [] -> unsupported ("unknown declaration " ^ id)
      | (d:Source.declaration)::rest ->
        if d.id=id then
          if d.parameters=[] && args=[] then [i+4]
          else if List.length args <= List.length d.parameters then begin
            match List.assoc_opt (id,args) !applications with
            | Some label -> [label]
            | None ->
            let rec mentions = function
              | Atoms atoms -> List.exists (function
                  | Named (other,_) -> other=id
                  | Shape shape ->
                    List.exists (fun (f:Semantic.field) -> mentions f.read) shape.fields ||
                    List.exists (fun (c:Semantic.signature) -> mentions c.receiver) shape.calls
                  | _ -> false) atoms
              | Union ts -> List.exists mentions ts
              | Rigid _ -> false in
            if mentions d.expression then begin
              let label = List.length !rows in
              rows := !rows @ [Array [String "reserved";String id]];
              applications := ((id,args),label) :: !applications;
              (match Proposal.definition declarations id args with
               | Atoms atoms ->
                 let row = List.concat_map (fun l -> match List.nth_opt !rows l with
                   | Some (Array clauses) -> clauses
                   | _ -> fail "application references a missing graph row")
                   (List.sort_uniq compare (List.concat_map atom_labels atoms)) in
                 rows := List.mapi (fun j r -> if j=label then Array row else r) !rows
               | _ -> unsupported "generic application needs a ground graph type");
              [label]
            end else begin
            if List.mem id !active_imports then
              unsupported "recursive generic application needs memoized rows";
            active_imports := id::!active_imports;
            let result = try (match Proposal.definition declarations id args with
              | Atoms atoms ->
                let labels = List.sort_uniq compare (List.concat_map atom_labels atoms) in
                (match labels with
                | [] -> unsupported "generic application has no inhabited graph clause"
                | [label] -> [label]
                | labels ->
                  let row = List.concat_map (fun label ->
                    match List.nth_opt !rows label with
                    | Some (Array clauses) -> clauses
                    | _ -> fail "application references a missing graph row") labels in
                  [intern (Array row)])
              | _ -> unsupported "generic application needs a ground graph type")
              with e -> active_imports := List.tl !active_imports; raise e in
            active_imports := List.tl !active_imports;
            result
            end
          end else unsupported "type application has wrong arity"
        else find (i + if d.parameters=[] then 1 else 0) rest in
    find 0 declarations
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
  (* A declaration applied to a rigid argument has no graph row of its own:
     its definition, with the argument substituted, is the claim, exactly as
     Lean expands the source equation. Ground applications keep their rows. *)
  let rec expand_rigid = function
    | Atoms atoms when List.exists (function
        | Named (_,args) -> List.exists contains_symbolic args | _ -> false) atoms ->
      List.fold_left (fun acc atom -> union acc (match atom with
        | Named (id,args) when List.exists contains_symbolic args ->
          expand_rigid (Proposal.definition declarations id args)
        | atom -> Atoms [atom])) (Atoms []) atoms
    | t -> t
  in
  let rec claim_type t = match expand_rigid t with
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
  let interior (f : Proposal.function_claim) =
    let expressions row = Array (List.map (fun (e : Proposal.expression) ->
      Object (["pos",e.pos; "type",claim_type e.type_; "current",Null]
        @ instantiate e.instantiation)) row) in
    let entries es = Array (List.map (fun (e : Proposal.entry) ->
      Object ["start",e.start;"bindings",Array (List.map named e.bindings)]) es) in
    let arrows = if f.arrows = [] then [] else
      ["arrows",Array (List.map (fun (pos,rows) ->
        Object ["pos",pos;"rows",Array (List.map (fun (o : Proposal.overlay) ->
          Object ["expressions",expressions o.row_expressions;
                  "entries",entries o.row_entries]) rows)]) f.arrows)] in
    ["entries",entries f.entries; "expressions",expressions f.expressions] @ arrows in
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
  (* The initialization unit's claims, stated only for a module that has
     top-level code. *)
  let init = match proposal.init with
    | None -> []
    | Some f -> ["init",Object (interior f)] in
  Object (["file",proposal.program.file; "sourceSha256",proposal.program.digest;
    "types",Array !rows; "functions",Array functions] @ init)
