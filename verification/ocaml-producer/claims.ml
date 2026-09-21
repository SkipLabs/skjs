open Json
open Semantic
open Environment
open Source
open Proposal
let unsupported s = fail ("unsupported: " ^ s)
let encode (proposal : Proposal.t) =
  (* The graph is just the existing SourceClaims wire format, interned structurally. *)
  let rows = ref [Array [String "nul"]; Array [Object ["boolLit",Object ["value",Bool true]]];
                  Array [Object ["boolLit",Object ["value",Bool false]]]; Array [String "undef"]]
  in
  let intern row =
    let rec find n = function [] -> rows := !rows @ [row]; n
      | r::rs -> if r=row then n else find (n+1) rs in find 0 !rows
  in
  let rec labels = function Rigid _ | Union _ -> unsupported "rigid type nested in a graph type"
    | Atoms atoms -> Array (List.map int (List.sort_uniq compare (List.map atom_label atoms)))
  and atom_label = function
    | Nul -> 0 | True -> 1 | False -> 2 | Undef -> 3
    | Num -> intern (Array [String "num"]) | Str -> intern (Array [String "str"])
    | Top -> intern (Array [String "top"])
    | Shape shape ->
      let fields = Array (List.map (fun (f:Semantic.field) ->
        if f.optional || f.write <> Some f.read then unsupported "field capability export";
        Array [String f.name;labels f.read]) shape.fields) in
      let arrows = Array (List.map (fun (a:Semantic.signature) ->
        Array [Array (List.map labels a.params);labels a.result]) shape.calls) in
      let clause = match shape.fields,shape.calls with
        | _,[] -> Object ["refs",Object ["first",fields;"rest",Array [];"views",Array []]]
        | [],_ -> Object ["arrs",Object ["arrows",arrows]]
        | _,_ -> Object ["callable",Object ["first",fields;"rest",Array [];"arrows",arrows]] in
      intern (Array [clause])
  in
  let claim_type = function Rigid n -> Object ["param",String n.spelling] | (Atoms _ | Union _) as t -> labels t
  in
  let point t extra = Object (extra @ ["type",claim_type t; "current",Null])
  in
  let named (n,b) = point (binding_type b) ["name",String n]

  in
  let functions = List.map (fun (f : Proposal.function_claim) ->
    let source = f.source in
    Object ["name",String source.name; "namePos",source.name_pos;
      "params",Array (List.map (fun (n,t) -> named (n,Value t)) source.params);
      "result",claim_type source.result;
      "entries",Array (List.map (fun (e : Proposal.entry) ->
        Object ["start",e.start;"bindings",Array (List.map named e.bindings)]) f.entries);
      "expressions",Array (List.map (fun (e : Proposal.expression) ->
        point e.type_ ["pos",e.pos]) f.expressions)]) proposal.functions in
  Object ["file",proposal.program.file; "sourceSha256",proposal.program.digest;
    "types",Array !rows; "functions",Array functions]
