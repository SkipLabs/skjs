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
  (* Applications reserved for Lean to fill: row, declaration position and
     argument rows. *)
  let reserved = ref [] in
  (* The row reserved for an application of a declaration whose equation has
     methods: their receiver is that application, so it needs its label
     before its equation is expanded, as Lean reserves it. *)
  let applications = ref [] in
  (* Array types, each an empty row Lean fills with the array shape over the
     store row: the producer states the store's contract, never the shape. *)
  let arrays = ref [] in
  (* Intersections of ground types, each an empty row Lean fills with the meet
     of its operands: the producer names the operands, never the meet. *)
  let meets = ref [] in
  let intern row =
    let rec find n = function [] -> rows := !rows @ [row]; n
      | r::rs -> if r=row then n else find (n+1) rs in find 0 !rows
  in
  let rec labels = function
    | Rigid _ | Union _ -> unsupported "rigid type nested in a graph type"
    | Meet (t,ts) as m ->
      if Semantic.mentions_rigid m then unsupported "rigid type nested in a graph type";
      let parts = Array (List.map labels (t::ts)) in
      (match List.assoc_opt parts !meets with
       | Some label -> Array [int label]
       | None ->
         let label = List.length !rows in
         rows := !rows @ [Array []];
         meets := !meets @ [(parts,label)];
         Array [int label])
    | Atoms atoms -> Array (List.map int (List.sort_uniq compare (List.concat_map atom_labels atoms)))
  and atom_labels = function
    | Nul -> [0] | True -> [1] | False -> [2] | Undef -> [3]
    | Num -> [intern (Array [String "num"])] | Str -> [intern (Array [String "str"])]
    | Bigint -> [intern (Array [String "bigint"])] | Symbol -> [intern (Array [String "symbol"])]
    | NumLit bits -> [intern (Array [Object ["numLit",Object ["bits",String (Printf.sprintf "%Lu" bits)]]])]
    | StrLit value -> [intern (Array [Object ["strLit",Object ["value",String value]]])]
    | BigintLit value -> [intern (Array [Object ["bigintLit",Object ["value",Number value]]])]
    | Top -> [intern (Array [String "top"])]
    | Ctors signatures ->
      List.iter (fun (s:Semantic.signature) ->
        if s.quantified <> [] then unsupported "quantified construct signature claim encoding") signatures;
      (* Variadic construct signatures carry their rest, an argument-list type;
         the list is left out when empty, its one spelling of none. *)
      let fixed = List.filter_map (fun (s:Semantic.signature) -> match s.rest_pack with
        | None -> Some (Array [Array (List.map labels s.params);labels s.result])
        | Some _ -> None) signatures in
      let rests = List.filter_map (fun (s:Semantic.signature) -> Option.map (fun r ->
        Array [Array (List.map labels s.params);Array [pack_labels r;labels s.result]]) s.rest_pack) signatures in
      [intern (Array [Object ["ctors",Object (("signatures",Array fixed) ::
        (if rests = [] then [] else ["variadic",Array rests]))]])]
    | Named (id,args) -> declaration_labels id args
    | Exact fs ->
      (* Invariant fields, and one own-key bound: its own keys are among
         exactly theirs. *)
      [intern (Array [Object ["refs",Object ["first",Array (List.map (fun (f:Semantic.field) ->
          if f.optional || f.write <> Some f.read then unsupported "an exact record's fields are invariant";
          Array [key_json f.name;labels f.read]) fs);"rest",Array [];"views",Array [];
        "bounds",Array [Object ["among",Bool true;
          "keys",Array (List.map (fun (f:Semantic.field) -> key_json f.name) fs)]]]]])]
    | Shape shape ->
      (* An optional field constrains its key only where the object has it:
         a writable one under one invariant contract, a readonly one as a
         view there. *)
      let optional,present = List.partition (fun (f:Semantic.field) -> f.optional) shape.fields in
      let writes,reads = List.partition (fun (f:Semantic.field) -> f.write <> None) present in
      let fields writable fs = Array (List.map (fun (f:Semantic.field) ->
        if writable && f.write <> Some f.read then unsupported "asymmetric read/write capability export";
        Array [key_json f.name;labels f.read]) fs) in
      let optional_list = match optional with
        | [] -> []
        | fs -> ["optional",Array (List.map (fun (f:Semantic.field) ->
            if f.write <> None && f.write <> Some f.read then
              unsupported "asymmetric read/write capability export";
            Object ["key",key_json f.name;"readonly",Bool (f.write = None);"type",labels f.read]) fs)] in

      let fields,views = fields true writes,fields false reads in
      List.iter (fun (a:Semantic.signature) ->
        if a.quantified <> [] then unsupported "quantified callable claim encoding") shape.calls;
      (* Fixed arrows and variadic signatures of one value share its clause; the
         variadic list is left out when empty, its one spelling of none. *)
      let fixed = List.filter (fun (a:Semantic.signature) ->
        a.variadic = None && a.rest_pack = None) shape.calls in
      let arrows = Array (List.map (fun (a:Semantic.signature) ->
        Array [labels a.receiver;Array [Array (List.map labels a.params);labels a.result]]) fixed) in
      let variadic = List.filter_map (fun (a:Semantic.signature) ->
        (* A rest's type is a pack: of any number of actuals at an element, or
           the one a pack parameter's instance states. *)
        let rest = match a.variadic,a.rest_pack with
          | Some element,None -> Some (pack_labels (Pack {
              required=[];optional_elements=[];rest=Some element;readonly=false}))
          | Some _,Some _ -> unsupported "signature has both element and pack rests"
          | None,Some r -> Some (pack_labels r)
          | None,None -> None in
        Option.map (fun rest -> Array [labels a.receiver;Array [Array (List.map labels a.params);
          Array [rest;labels a.result]]]) rest) shape.calls in
      let calls = ("arrows",arrows) :: (if variadic = [] then [] else ["variadic",Array variadic]) in
      match shape.elements with
      | Some sequence ->
        if shape.fields <> [] || shape.calls <> [] || shape.string_index <> None
        then unsupported "array with additional fields, indexes or calls";
        (* The store's contract is the producer's; the array holding it, with
           its prototype, is a row Lean fills with the one array shape. *)
        let store = intern (Array [Object ["list",Object ["first",Object [
          "required",Array (List.map labels sequence.required);
          "optional",Array (List.map labels sequence.optional_elements);
          "rest",(match sequence.rest with None -> Null | Some t -> labels t);
          "readonly",Bool sequence.readonly];"rest",Array []]]]) in
        (match List.assoc_opt (store,sequence.readonly) !arrays with
         | Some label -> [label]
         | None ->
           let label = List.length !rows in
           rows := !rows @ [Array []];
           arrays := !arrays @ [((store,sequence.readonly),label)];
           [label])
      | None ->
        let clause = match shape.fields,shape.string_index,shape.calls with
        | _,Some index,[] ->
          (* A mutable index is also a writable one, at its one contract. *)
          let cells = match index.writable with
            | None -> []
            | Some w when w = index.value -> ["cells",Array [labels index.value]]
            | Some _ -> unsupported "asymmetric string index signature" in
          Object ["dict",Object (["first",fields;"rest",Array [];"views",views;
            "indexes",Array [labels index.value]] @ optional_list @ cells)]
        | _,Some _,_ -> unsupported "callable with string index needs a combined clause"
        | _,None,[] -> Object ["refs",Object (["first",fields;"rest",Array [];"views",views] @ optional_list)]
        | [],None,_ -> Object ["arrs",Object calls]
        | _,_,_ ->
          if optional <> [] then unsupported "callable with optional fields";
          if reads <> [] then unsupported "callable with readonly fields";
          Object ["callable",Object (["first",fields;"rest",Array []] @ calls)] in
        [intern (Array [clause])]

  and pack_labels = function
    | PackParameter _ -> unsupported "rigid pack nested in a graph type"
    | Pack sequence -> Array [int (intern (Array [Object ["pack",Object ["first",Object [
        "required",Array (List.map labels sequence.required);
        "optional",Array (List.map labels sequence.optional_elements);
        "rest",(match sequence.rest with None -> Null | Some t -> labels t);
        "readonly",Bool false];"rest",Array []]]]))]
  and declaration_labels id args =
    let rec find i k = function
      | [] -> unsupported ("unknown declaration " ^ id)
      | (d:Source.declaration)::rest ->
        if d.id=id then
          if d.parameters=[] && args=[] then [i+4]
          else if List.length args <= List.length d.parameters then begin
            match List.assoc_opt (id,args) !applications with
            | Some label -> [label]
            | None ->
              (* One lowering of every declaration: the row is reserved here,
                 after its arguments' rows, and Lean fills it from the
                 declaration's source terms. *)
              let arg_labels = List.map labels args in
              let label = List.length !rows in
              rows := !rows @ [Array []];
              applications := ((id,args),label) :: !applications;
              reserved := !reserved @ [Object ["row",int label;"declaration",int k;
                "args",Array arg_labels]];
              [label]
          end else unsupported "type application has wrong arity"
        else find (i + if d.parameters=[] then 1 else 0) (k + 1) rest in
    find 0 0 declarations
  in
  (* A callable whose signature mentions a rigid parameter has no graph row:
     it is exported in the scheme form, with its own binders (possibly none),
     so a returned closure can retain an outer binder in its result. *)
  let rec contains_symbolic = function
    | Rigid _ -> true
    | Meet (t,ts) -> List.exists contains_symbolic (t::ts)
    | Union ts -> List.exists contains_symbolic ts
    | Atoms atoms -> List.exists (function
        | Named (_,args) -> List.exists contains_symbolic args
        | Shape s ->
          List.exists (fun (f:Semantic.field) -> contains_symbolic f.read
            || Option.fold ~none:false ~some:contains_symbolic f.write) s.fields
          || Option.fold ~none:false ~some:(fun (i:Semantic.index_signature) ->
              contains_symbolic i.value || Option.fold ~none:false ~some:contains_symbolic i.writable) s.string_index
          || List.exists signature_contains_symbolic s.calls
          || Option.fold ~none:false ~some:sequence_contains_symbolic s.elements
        | Exact fs -> List.exists (fun (f:Semantic.field) -> contains_symbolic f.read) fs
        | Ctors signatures -> List.exists signature_contains_symbolic signatures
        | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
        | Bigint | Symbol | BigintLit _ -> false) atoms
  and pack_contains_symbolic = function
    | PackParameter _ -> true
    | Pack s -> sequence_contains_symbolic s
  and sequence_contains_symbolic s = List.exists contains_symbolic
      (s.required @ s.optional_elements @ Option.to_list s.rest)
  and signature_contains_symbolic (s:Semantic.signature) =
    List.exists contains_symbolic (s.receiver :: s.result :: s.params @ Option.to_list s.variadic)
    || Option.fold ~none:false ~some:pack_contains_symbolic s.rest_pack
    || List.exists (fun (q:Semantic.quantifier) ->
        Option.fold ~none:false ~some:argument_contains_symbolic q.bound) s.quantified
  and argument_contains_symbolic = function
    | ValueArgument t -> contains_symbolic t
    | PackArgument p -> pack_contains_symbolic p
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
      if signature.rest_pack <> None then unsupported "a pack parameter in a scheme claim";
      let type_params = Array (List.map (fun (q:Semantic.quantifier) -> Object [
        "name",String q.identity.spelling;
        "bound",(match q.bound with None -> Null | Some (ValueArgument t) -> claim_type t
          | Some (PackArgument _) -> unsupported "a pack bound in a scheme claim")])
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
    | Meet _ as t when not (contains_symbolic t) -> labels t
    | Meet _ -> unsupported "a type parameter's intersection in a claim"
  in
  (* The substitution is exported so Lean re-checks the elimination it names,
     rather than re-inferring one of its own. A site that calls no quantified
     callable omits the field: unlike `current`, its absence asserts nothing. *)
  let instantiate = function
    | None -> []
    | Some subst -> ["instantiate",Array (List.map (fun (name,t) ->
        Object ["name",String name; "type",(match t with ValueArgument t -> claim_type t
          | PackArgument p -> pack_labels p)]) subst)]
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
    "types",Array !rows; "functions",Array functions] @ init @
    (if !reserved = [] then [] else ["applications",Array !reserved]) @
    (if !arrays = [] then [] else ["arrays",Array (List.map (fun ((store,readonly),row) ->
      Object ["row",int row;"store",int store;"readonly",Bool readonly]) !arrays)]) @
    (if !meets = [] then [] else ["meets",Array (List.map (fun (parts,row) ->
      Object ["row",int row;"parts",parts]) !meets)]))
