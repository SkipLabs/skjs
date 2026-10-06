(* statement_analysis.ml types statement actions and supplies their semantic callbacks to the graph solver. *)
(* expression_typing.ml dispatches every expression constructor and associates its type with the execution point. *)
(* binding_analysis.ml interprets parameter and pattern binding schedules with recursive expression inference. *)
(* analysis_state.ml allocates the pass state shared by its mutually recursive expression, binding and body analyses. *)
open Source
open Proposal_types
let infer diagnostics flows offered declarations module_functions bounds assumed f =
  let state = Analysis_state.create diagnostics flows offered declarations module_functions bounds assumed f in
  let module S = struct let state = state end in
  let module E = Expression_typing.Make(S) in
  let module B = Binding_analysis.Make(S) in
  let module T = Statement_analysis.Make(S) in
  let open Analysis_state.View(S) in
  let rec expr ?expected env e = E.infer expr bindings body ?expected env e
  and bindings env plan = B.infer expr env plan
  and body owner_span result returned env ss =
    let saved = (!block_result,!block_returned) in
    block_result := result; block_returned := returned;
    Fun.protect ~finally:(fun () ->
      let r,t = saved in block_result := r; block_returned := t)
      (fun () -> T.statements expr bindings owner_span env ss) in
  let run () =
  let owner_span = if f.name_pos=Json.Null then Json.Array [Json.int 0;Json.int 0] else f.name_pos in
  ignore (T.statements expr bindings owner_span env0 f.body);
  (* An expression the lowering reaches on two paths (the fields the arms of a
     constructor's last `if` share) is claimed once when both claims agree;
     two different claims at one span stay, and Lean refuses them. *)
  let seen = Hashtbl.create 64 in
  let expressions = List.filter (fun x ->
    not (Hashtbl.mem seen x) && (Hashtbl.add seen x (); true)) (List.rev !expressions) in
  let expressions = List.map (fun (x:expression) -> match List.assoc_opt (x.point,x.pos) !instances with
    | Some instance -> {x with type_=instance}
    | None -> x) expressions in
  (* Likewise an entry, the closure body a guard's arm types twice. *)
  let seen = Hashtbl.create 64 in
  let entries = List.filter (fun x ->
    not (Hashtbl.mem seen x) && (Hashtbl.add seen x (); true)) (List.rev !entries) in
  {contracts=List.rev !contracts;source=f;entries;expressions;arrows=List.sort_uniq compare (List.rev !arrows)},List.sort_uniq compare !requests
  in
  let result = try Ok (run ()) with Json.Error m -> Error m in
  result,!(state.Analysis_state.writes)
