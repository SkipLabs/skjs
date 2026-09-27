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
(* The graph's sole callable contract shape. Effects become definition
   obligations when a qualified signature is proposed. *)
let effect_json = function
  | Unrestricted -> String "unrestricted"
  | PreservesInputHeap -> String "preservesInputHeap"
let call_contract call_effect receiver arguments result = Object [
  "receiver",receiver; "arguments",arguments; "result",result;
  "effect",effect_json call_effect]

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
  (* A generic body's binder is a value parameter row, one per spelling,
     which names its own label. Lean reads the unit's binders as these rows
     and certifies the body at every assignment of them; a claim over a
     binder, however nested, is then an ordinary graph type. *)
  let parameters = ref [] in
  let parameter_label (r:Semantic.rigid) =
    match List.assoc_opt r.spelling !parameters with
    | Some label -> label
    | None ->
      let label = List.length !rows in
      rows := !rows @ [Object ["param",int label;"name",String r.spelling;"kind",String "value"]];
      parameters := (r.spelling,label) :: !parameters;
      label
  in
  (* A binder's ground bound, from the signature that declares it: such a
     binder is the meet of its row and the bound, which Lean fills. *)
  (* A binder bounded by another binder, `U extends T`, is the meet of the
     two, which Lean fills as `U ⊓ T`. *)
  let bounds = List.concat_map (fun (f : Proposal.function_claim) ->
    List.filter_map (fun (q:Semantic.quantifier) -> match q.bound with
      | Some (ValueArgument b) when not (Semantic.mentions_rigid b) -> Some (q.identity,b)
      | Some (ValueArgument (Rigid t)) when t <> q.identity -> Some (q.identity,Rigid t)
      | _ -> None) f.source.quantified) (Option.to_list proposal.init @ proposal.functions) in
  (* The operand lists an intersection distributes into over its operands'
     union arms, each a choice of one arm per operand (at most 16 are
     written; more stay one meet, as before). *)
  let distributed parts =
    let rec arms = function
      | Union ts -> List.concat_map arms ts
      | Atoms (_::_::_ as atoms) -> List.map (fun a -> Atoms [a]) atoms
      | t -> [t] in
    List.fold_right (fun part acc ->
      List.concat_map (fun arm -> List.map (fun rest -> arm :: rest) acc) (arms part)) parts [[]] in
  let rec labels t = Array (List.map int (label_list t))
  and label_list = function
    | Rigid r -> (match List.assoc_opt r bounds with
      | None -> [parameter_label r]
      | Some b ->
        let parts = Array [Array [int (parameter_label r)]; labels b] in
        (match List.assoc_opt parts !meets with
         | Some label -> [label]
         | None ->
           let label = List.length !rows in
           rows := !rows @ [Array []];
           meets := !meets @ [(parts,label)];
           [label]))
    | Union ts -> List.sort_uniq compare (List.concat_map label_list ts)
    | Meet (t,ts) when (let n = List.length (distributed (t::ts)) in n > 1 && n <= 16) ->
      (* An intersection with a union operand is the union of the
         intersections with each of its arms, `(A | B) & C` is
         `(A & C) | (B & C)`, the same values: the claim states it so, one
         meet row per arm, which a read then splits on. *)
      (* An arm meeting two disjoint primitives, `"hi" & "fixed"` at an
         instance, holds no value, and is left out. *)
      let empty parts = List.exists (fun a -> List.exists (fun b -> match a,b with
        | Atoms [x],Atoms [y] -> Inference.meet_atom x y = Some []
        | _ -> false) parts) parts in
      List.sort_uniq compare (List.concat_map (fun parts -> match parts with
        | _ when empty parts -> []
        | p::ps -> label_list (Meet (p,ps))
        | [] -> []) (distributed (t::ts)))
    (* A meet row, filled by Lean from its operands' rows: a binder's is its
       parameter row, and the meet of a binder with others is a meet row. *)
    | Meet (t,ts) ->
      let parts = Array (List.map labels (t::ts)) in
      (match List.assoc_opt parts !meets with
       | Some label -> [label]
       | None ->
         let label = List.length !rows in
         rows := !rows @ [Array []];
         meets := !meets @ [(parts,label)];
         [label])
    | Atoms atoms -> List.sort_uniq compare (List.concat_map atom_labels atoms)
  and atom_labels = function
    | Nul -> [0] | True -> [1] | False -> [2] | Undef -> [3]
    | Num -> [intern (Array [String "num"])] | Str -> [intern (Array [String "str"])]
    | Bigint -> [intern (Array [String "bigint"])] | Symbol -> [intern (Array [String "symbol"])]
    | NumLit bits -> [intern (Array [Object ["numLit",Object ["bits",String (Printf.sprintf "%Lu" bits)]]])]
    | StrLit value -> [intern (Array [Object ["strLit",Object ["value",String value]]])]
    | BigintLit value -> [intern (Array [Object ["bigintLit",Object ["value",Number value]]])]
    | Top -> [intern (Array [String "top"])]
    | Callable -> [intern (Array [Object ["arrs",Object ["arrows",Array []]]])]
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
    (* A class's generic method, held by its prototype: a scheme row. Its
       binders are the parser's names for the member's rows (`…#k:null^0`),
       which Lean's lowering of the class's instance type binds too, so the
       prototype's closure and the instance's member quantify over the same
       rows. A binder the source spells is scoped, and no row states it. *)
    | Shape {fields=[];indexes=[];elements=None;calls=[s]}
        when s.quantified <> [] && List.for_all (fun (q:Semantic.quantifier) ->
          String.contains q.identity.spelling '#' && q.bound = None) s.quantified ->
      let binders = List.map (fun (q:Semantic.quantifier) -> int (parameter_label q.identity)) s.quantified in
      let signature,variadic = match s.variadic,s.rest_pack with
        | None,None -> [call_contract s.call_effect (labels s.receiver) (Array (List.map labels s.params)) (labels s.result)],[]
        | Some element,None ->
          [],[call_contract s.call_effect (labels s.receiver)
            (Array [Array (List.map labels s.params);
              pack_labels (Pack {required=[];optional_elements=[];rest=Some element;readonly=false;dense=true})])
            (labels s.result)]
        | _,Some _ -> unsupported "a pack parameter in a generic method's scheme" in
      [intern (Object ["scheme",Object (["binders",Array binders;"signatures",Array signature]
        @ (if variadic = [] then [] else ["variadic",Array variadic]))])]
    | Shape shape ->
      (* An optional field constrains its key only where the object has it:
         a writable one under one invariant contract, a readonly one as a
         view there. *)
      let hosted,plain = List.partition (fun (f:Semantic.field) -> f.host) shape.fields in
      let optional,present = List.partition (fun (f:Semantic.field) -> f.optional) plain in
      let writes,reads = List.partition (fun (f:Semantic.field) -> f.write <> None) present in
      (* A method is a host-relative member: its signatures, received by the
         object, as Lean lowers method syntax (`methods`). *)
      let methods = match hosted with
        | [] -> []
        | fs -> ["methods",Array (List.map (fun (f:Semantic.field) ->
            let signatures = match f.read with
              | Atoms [Shape {fields=[];indexes=[];calls=(_::_ as calls);elements=None}] -> calls
              | _ -> unsupported "a method is one or more signatures" in
            List.iter (fun (s:Semantic.signature) ->
              if s.quantified <> [] then unsupported "quantified method claim encoding") signatures;
            let calls = List.filter_map (fun (s:Semantic.signature) ->
              if s.variadic = None && s.rest_pack = None then
                Some (call_contract s.call_effect (Object []) (Array (List.map labels s.params)) (labels s.result)) else None) signatures in
            let rests = List.filter_map (fun (s:Semantic.signature) ->
              let rest = match s.variadic,s.rest_pack with
                | Some element,None -> Some (pack_labels (Pack {
                    required=[];optional_elements=[];rest=Some element;readonly=false;dense=true}))
                | None,Some r -> Some (pack_labels r)
                | Some _,Some _ -> unsupported "signature has both element and pack rests"
                | None,None -> None in
              Option.map (fun rest -> call_contract s.call_effect (Object [])
                (Array [Array (List.map labels s.params);rest]) (labels s.result)) rest) signatures in
            Object ["key",key_json f.name;"calls",Array calls;"rests",Array rests;
                    "schemes",Array []]) fs)] in
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
      (* A record holding its prototype does not own the keys the prototype
         states (the library overlay's hidden members). *)
      let hidden_bound = match List.find_opt (fun (f:Semantic.field) -> f.name = Name "[[proto]]") shape.fields with
        | Some {read=Atoms [Shape p];_} ->
          ["bounds",Array [Object ["among",Bool false;
            "keys",Array (List.map (fun (f:Semantic.field) -> key_json f.name) p.fields)]]]
        | _ -> [] in
      List.iter (fun (a:Semantic.signature) ->
        if a.quantified <> [] then unsupported "quantified callable claim encoding") shape.calls;
      (* Fixed arrows and variadic signatures of one value share its clause; the
         variadic list is left out when empty, its one spelling of none. *)
      let fixed = List.filter (fun (a:Semantic.signature) ->
        a.variadic = None && a.rest_pack = None) shape.calls in
      let arrows = Array (List.map (fun (a:Semantic.signature) ->
        call_contract a.call_effect (labels a.receiver) (Array (List.map labels a.params)) (labels a.result)) fixed) in
      let variadic = List.filter_map (fun (a:Semantic.signature) ->
        (* A rest's type is a pack: of any number of actuals at an element, or
           the one a pack parameter's instance states. *)
        let rest = match a.variadic,a.rest_pack with
          | Some element,None -> Some (pack_labels (Pack {
              required=[];optional_elements=[];rest=Some element;readonly=false;dense=true}))
          | Some _,Some _ -> unsupported "signature has both element and pack rests"
          | None,Some r -> Some (pack_labels r)
          | None,None -> None in
        Option.map (fun rest -> call_contract a.call_effect (labels a.receiver)
          (Array [Array (List.map labels a.params);rest]) (labels a.result)) rest) shape.calls in
      let calls = ("arrows",arrows) :: (if variadic = [] then [] else ["variadic",Array variadic]) in
      match shape.elements with
      | Some sequence ->
        if shape.fields <> [] || shape.calls <> [] || shape.indexes <> []
        then unsupported "array with additional fields, indexes or calls";
        (* The store's contract is the producer's; the array holding it, with
           its prototype, is a row Lean fills with the one array shape. *)
        let store = intern (Array [Object ["list",Object ["first",Object [
          "required",Array (List.map labels sequence.required);
          "optional",Array (List.map labels sequence.optional_elements);
          "rest",(match sequence.rest with None -> Null | Some t -> labels t);
          "readonly",Bool sequence.readonly;"dense",Bool sequence.dense];"rest",Array []]]]) in
        (match List.assoc_opt (store,sequence.readonly) !arrays with
         | Some label -> [label]
         | None ->
           let label = List.length !rows in
           rows := !rows @ [Array []];
           arrays := !arrays @ [((store,sequence.readonly),label)];
           [label])
      | None ->
        let clause = match shape.fields,shape.indexes,shape.calls with
        | _,(_::_ as indexes),[] ->
          (* Each index is over the keys its class admits; a mutable one is
             also a writable one, at its one contract. *)
          let entry (index:Semantic.index_signature) = Array [String (match index.keys with
            | Strings -> "strings" | Numeric -> "numeric" | Symbols -> "symbols");labels index.value] in
          let cells = List.filter_map (fun (index:Semantic.index_signature) -> match index.writable with
            | None -> None
            | Some w when w = index.value -> Some (entry index)
            | Some _ -> unsupported "asymmetric index signature") indexes in
          Object ["dict",Object (["first",fields;"rest",Array [];"views",views;
            "indexes",Array (List.map entry indexes)] @ optional_list @ methods
            @ (if cells = [] then [] else ["cells",Array cells]))]
        | _,_::_,_ -> unsupported "callable with an index signature needs a combined clause"
        | _,[],[] -> Object ["refs",Object (["first",fields;"rest",Array [];"views",views] @ optional_list @ methods @ hidden_bound)]
        | _ when methods <> [] -> unsupported "a callable object with methods needs a combined clause"
        | [],[],_ -> Object ["arrs",Object calls]
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
        "readonly",Bool false;"dense",Bool true];"rest",Array []]]]))]
  and declaration_labels id args =
    let rec find i k = function
      | [] -> unsupported ("unknown declaration " ^ id)
      | (d:Source.declaration)::rest ->
        if d.id=id then
          if d.parameters=[] && args=[] then [i+4]
          else if List.length args <= List.length d.parameters then begin
            (* An argument left to its default is that default, at the earlier
               arguments: `IteratorResult<number>` and `IteratorResult<number,
               unknown>` are one application, and so one row. *)
            let rec complete previous supplied parameters defaults = match parameters,defaults with
              | parameter::more,default::others ->
                (match supplied,default with
                 | value::tail,_ -> complete ((parameter,Semantic.ValueArgument value)::previous) tail more others
                 | [],Some value ->
                   let value = Inference.substitute (List.rev previous) value in
                   complete ((parameter,Semantic.ValueArgument value)::previous) [] more others
                 | [],None -> None)
              | _ -> Some (List.rev_map (fun (_,a) -> match a with
                  | Semantic.ValueArgument t -> t | _ -> assert false) previous) in
            let args = Option.value (complete [] args d.parameters d.defaults) ~default:args in
            (* Keyed by the argument rows: two binders of one spelling, a
               class's and a function's, are one parameter row, so their
               applications are one. *)
            let arg_labels = List.map labels args in
            match List.assoc_opt (id,arg_labels) !applications with
            | Some label -> [label]
            | None ->
              (* One lowering of every declaration: the row is reserved here,
                 after its arguments' rows, and Lean fills it from the
                 declaration's source terms. *)
              let label = List.length !rows in
              rows := !rows @ [Array []];
              applications := ((id,arg_labels),label) :: !applications;
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
          || List.exists (fun (i:Semantic.index_signature) ->
              contains_symbolic i.value || Option.fold ~none:false ~some:contains_symbolic i.writable) s.indexes
          || List.exists signature_contains_symbolic s.calls
          || Option.fold ~none:false ~some:sequence_contains_symbolic s.elements
        | Exact fs -> List.exists (fun (f:Semantic.field) -> contains_symbolic f.read) fs
        | Ctors signatures -> List.exists signature_contains_symbolic signatures
        | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
        | Bigint | Symbol | BigintLit _ | Callable -> false) atoms
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
  (* A declaration that reaches itself, a class's instance type through its
     methods' receiver or a recursive alias, has no finite expansion: applied
     to a binder, it is its application row at the binder's parameter row, as
     Lean reads its source annotation. *)
  let rec named_in = function
    | Atoms atoms -> List.concat_map (function
        | Named (id,args) -> id :: List.concat_map named_in args
        | Shape s -> List.concat_map (fun (f:Semantic.field) -> named_in f.read
            @ Option.fold ~none:[] ~some:named_in f.write) s.fields
          @ List.concat_map (fun (c:Semantic.signature) ->
              List.concat_map named_in (c.receiver :: c.result :: c.params @ Option.to_list c.variadic)) s.calls
          @ List.concat_map (fun (i:Semantic.index_signature) -> named_in i.value) s.indexes
          @ Option.fold ~none:[] ~some:(fun (q:Semantic.sequence) ->
              List.concat_map named_in (q.required @ q.optional_elements @ Option.to_list q.rest)) s.elements
        | Exact fs -> List.concat_map (fun (f:Semantic.field) -> named_in f.read) fs
        | Ctors cs -> List.concat_map (fun (c:Semantic.signature) ->
            List.concat_map named_in (c.receiver :: c.result :: c.params)) cs
        | _ -> []) atoms
    | Union ts -> List.concat_map named_in ts
    | Meet (t,ts) -> List.concat_map named_in (t::ts)
    | Rigid _ -> [] in
  let references id = match List.find_opt (fun (d:Source.declaration) -> d.id=id) declarations with
    | Some d -> List.concat_map named_in (d.expression :: d.bases)
    | None -> [] in
  let self_referential id =
    let rec reach seen = function
      | [] -> false
      | x :: rest -> x = id || (if List.mem x seen then reach seen rest
                                else reach (x::seen) (references x @ rest)) in
    reach [] (references id) in
  let rec expand_rigid = function
    | Atoms atoms when List.exists (function
        | Named (id,args) -> List.exists contains_symbolic args && not (self_referential id)
        | _ -> false) atoms ->
      List.fold_left (fun acc atom -> union acc (match atom with
        | Named (id,args) when List.exists contains_symbolic args && not (self_referential id) ->
          expand_rigid (Proposal.definition declarations id args)
        | atom -> Atoms [atom])) (Atoms []) atoms
    | t -> t
  in
  let rec claim_type t = match expand_rigid t with
    | Rigid n -> Object ["param",String n.spelling]
    | Atoms [Shape {fields=[];indexes=[];calls=[signature];elements=None}]
        when signature.quantified <> [] || List.exists contains_symbolic
          (signature.receiver :: signature.result :: signature.params @ Option.to_list signature.variadic) ->
      if signature.rest_pack <> None then unsupported "a pack parameter in a scheme claim";
      let type_params = Array (List.map (fun (q:Semantic.quantifier) -> Object [
        "name",String q.identity.spelling;
        "bound",(match q.bound with None -> Null | Some (ValueArgument t) -> claim_type t
          | Some (PackArgument _) -> unsupported "a pack bound in a scheme claim")])
        signature.quantified) in
      Object ["scheme",Object ["effect",effect_json signature.call_effect;"typeParams",type_params;
        "this",claim_type signature.receiver;
        "params",Array (List.map claim_type signature.params);
        "rest",(match signature.variadic with None -> Null | Some t -> claim_type t);
        "result",claim_type signature.result]]
    | Atoms [Shape {fields=[];indexes=[];calls=[];elements=Some
        {required=[];optional_elements=[];rest=Some element;readonly=false;dense=true}}]
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
    | Meet _ as t -> labels t
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
  (* A statement entry's bindings; a field's known contents are its object's
     `current` assertion, one `[field, type]` pair per field. *)
  let bindings bs = Array (List.filter_map (fun (n,b) ->
    if Environment.is_field n then None else
    let fields = List.filter_map (fun (m,f) ->
      if Environment.is_field m && Environment.owner m = n then
        Some (Array [String (Environment.field_of m); claim_type (binding_type f)])
      else None) bs in
    Some (Object ["name",String n; "type",claim_type (binding_type b);
                  "current",(if fields = [] then Null else Array fields)])) bs)

  in
  let interior (f : Proposal.function_claim) =
    let expressions row = Array (List.map (fun (e : Proposal.expression) ->
      Object (["pos",e.pos; "type",claim_type e.type_; "current",Null]
        @ instantiate e.instantiation)) row) in
    let entries es = Array (List.map (fun (e : Proposal.entry) ->
      Object ["start",e.start;"bindings",bindings e.bindings]) es) in
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
      Object ["start",e.start;"bindings",bindings e.bindings]) es) in
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
