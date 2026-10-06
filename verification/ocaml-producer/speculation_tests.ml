(* Source cases cannot inspect rollback or inject an unexpected OCaml exception.
   These checks exercise the state boundary used by speculative inference. *)
open Semantic
open Source
open Analysis_state
open Proposal_types
open Statement_analysis

exception Unexpected

let require message condition = if not condition then failwith message

let fresh () =
  let diagnostics = Proposal_diagnostics.create () in
  let fn : Source.fn = {
    quantified=[]; name="scope-test"; name_pos=Json.Null; params=[];
    rest=false; result=Atoms []; body=[] } in
  Analysis_state.create diagnostics [] [] [] [] [] [] fn

let disturb state name =
  let local = !(state.Analysis_state.local) in
  local.current_point <- name;
  local.grown_locals <- [name];
  local.entries <- [{ Proposal_types.point=name; start=Json.int 0; bindings=[] }];
  state.writes := (Json.String name, Atoms []) :: !(state.writes);
  state.diagnostics.Proposal_diagnostics.explanations :=
    (Json.Null,name) :: !(state.diagnostics.Proposal_diagnostics.explanations)

let check_exit name action expected =
  let state = fresh () in
  let outer = !(state.Analysis_state.local) in
  outer.current_point <- "enclosing";
  outer.grown_locals <- ["enclosing"];
  let before = { outer with current_point=outer.current_point } in
  let result = Analysis_state.speculate state (fun () ->
    require "attempt must be marked speculative" (!(state.local)).speculative_typing;
    require "attempt starts with enclosing contents" ((!(state.local)).current_point = "enclosing");
    disturb state name;
    action ()) in
  require "attempt result" (result = expected);
  require "restore enclosing record" (!(state.local) == outer);
  require "preserve enclosing contents" (outer = before);
  require "retain write proposals" (!(state.writes) = [Json.String name, Atoms []]);
  require "retain diagnostic observations"
    (!(state.diagnostics.Proposal_diagnostics.explanations) = [Json.Null,name])

let () =
  check_exit "successful" (fun () -> 7) (Some 7);
  check_exit "refused" (fun () -> Json.fail "probe refused") None;
  let state = fresh () in
  let outer = !(state.Analysis_state.local) in
  require "nested successful attempt" (Analysis_state.speculate state (fun () ->
    disturb state "parent";
    let parent = !(state.local) in
    require "nested refusal" (Analysis_state.speculate state (fun () ->
      disturb state "child";
      Json.fail "nested refusal") = None);
    require "nested scope restores parent identity" (!(state.local) == parent);
    require "nested scope restores parent contents" (parent.current_point = "parent");
    require "nested scope preserves speculative mode" parent.speculative_typing;
    9) = Some 9);
  require "nested scope restores outer identity" (!(state.local) == outer);
  require "nested scope restores normal mode" (not outer.speculative_typing);
  require "nested writes survive both scopes" (List.map fst !(state.writes) =
    [Json.String "child"; Json.String "parent"]);
  let state = fresh () in
  let outer = !(state.Analysis_state.local) in
  let caught = try
    ignore (Analysis_state.speculate state (fun () ->
      disturb state "unexpected"; raise Unexpected)); false
    with Unexpected -> true in
  require "unexpected exceptions propagate" caught;
  require "unexpected exception restores scope" (!(state.local) == outer &&
    outer.current_point = "" && not outer.speculative_typing);
  require "unexpected exception retains shared effects" (List.length !(state.writes) = 1);
  print_endline "speculative scopes: success, refusal, nesting and exception restoration passed"


(* Source cases cannot inject failure into a node's callback or inspect its
   enclosing publication buffers. Node claims and path metadata have separate
   ownership from the write proposals and diagnostic observations they retain. *)
let () =
  let state = fresh () in
  let module Nodes = Statement_analysis.Make(struct let state = state end) in
  let outer = !(state.local) in
  disturb state "enclosing-node";
  let enclosing_output = Nodes.node_output () in
  let restore_path grown_locals = (!(state.local)).grown_locals <- grown_locals in
  let within_node point action =
    let enclosing_path = (!(state.local)).grown_locals in
    Proposal_flow.with_path restore_path enclosing_path (fun () ->
      Nodes.with_output point action) in
  let check_enclosing () =
    require "node restores enclosing point" (outer.current_point = "enclosing-node");
    require "node restores enclosing output" (Nodes.node_output () = enclosing_output);
    require "node restores enclosing path" (outer.grown_locals = ["enclosing-node"]) in
  let result,output = within_node "parent-node" (fun () ->
    require "node starts with empty output" (Nodes.node_output () = Statement_analysis.empty_output);
    disturb state "parent-node";
    let parent_output = Nodes.node_output () in
    let child_result,child_output = within_node "child-node" (fun () ->
      disturb state "child-node"; 11) in
    require "nested node returns value" (child_result = 11);
    require "nested node returns only its claims"
      (List.map (fun (e:Proposal_types.entry) -> e.point) child_output.entries = ["child-node"]);
    require "nested node restores parent output" (Nodes.node_output () = parent_output);
    require "nested node restores parent point and metadata"
      (outer.current_point = "parent-node" && outer.grown_locals = ["parent-node"]);
    let refused = try ignore (within_node "refused-node" (fun () ->
      disturb state "refused-node"; Json.fail "node refusal")); false
      with Json.Error _ -> true in
    require "node refusal propagates" refused;
    require "refused nested node restores parent output" (Nodes.node_output () = parent_output);
    require "refused nested node restores parent path"
      (outer.current_point = "parent-node" && outer.grown_locals = ["parent-node"]);
    17) in
  require "node result survives scope" (result = 17);
  require "parent owns only its output"
    (List.map (fun (e:Proposal_types.entry) -> e.point) output.entries = ["parent-node"]);
  check_enclosing ();
  let caught = try ignore (within_node "exception-node" (fun () ->
    disturb state "exception-node"; raise Unexpected)); false
    with Unexpected -> true in
  require "node unexpected exceptions propagate" caught;
  check_enclosing ();
  require "node write proposals survive every exit" (List.map fst !(state.writes) =
    List.map (fun name -> Json.String name)
      ["exception-node"; "refused-node"; "child-node"; "parent-node"; "enclosing-node"]);
  require "node diagnostics survive every exit"
    (List.map snd !(state.diagnostics.Proposal_diagnostics.explanations) =
      ["exception-node"; "refused-node"; "child-node"; "parent-node"; "enclosing-node"]);
  print_endline "node scopes: owned output, nested paths and exception restoration passed"

(* A row owns three claim collections; its other proposal effects belong to
   the enclosing inference. Exceptions and nested speculation require direct
   access to this boundary. *)
let () =
  let state = fresh () in
  let module Rows = Expression_closures.Make(struct let state = state end) in
  let claims () =
    let local = !(state.local) in
    local.expressions,local.entries,local.contracts in
  let add_claims name =
    let local = !(state.local) in
    local.expressions <- {Proposal_types.point=name;pos=Json.Null;
      type_=Atoms [];instantiation=None} :: local.expressions;
    local.entries <- {Proposal_types.point=name;start=Json.Null;bindings=[]} :: local.entries;
    local.contracts <- {Proposal_types.pos=Json.Null;name;type_=Atoms []} :: local.contracts in
  add_claims "enclosing";
  let enclosing = claims () in
  let row = Rows.collect_overload_row_claims (fun () ->
    require "row starts with empty claim collections" (claims () = ([],[],[]));
    add_claims "first";
    let parent = claims () in
    let nested = Rows.collect_overload_row_claims (fun () -> add_claims "nested") in
    require "nested row collects its own claims"
      (List.map (fun (c:Proposal_types.contract) -> c.name) nested.row_contracts = ["nested"]);
    require "nested row restores enclosing claims" (claims () = parent);
    require "row nested speculation refuses" (Analysis_state.speculate state (fun () ->
      add_claims "speculative"; Json.fail "row speculation") = None);
    require "row uses active state after speculation" (claims () = parent);
    add_claims "last";
    (!(state.local)).grown_locals <- ["row-effect"];
    state.writes := [Json.Null,Atoms []]) in
  require "row retains claim order"
    (List.map (fun (c:Proposal_types.contract) -> c.name) row.row_contracts = ["first";"last"] &&
     List.map (fun (e:Proposal_types.expression) -> e.point) row.row_expressions = ["first";"last"] &&
     List.map (fun (e:Proposal_types.entry) -> e.point) row.row_entries = ["first";"last"]);
  require "row restores enclosing claims" (claims () = enclosing);
  require "row retains other proposal effects"
    ((!(state.local)).grown_locals = ["row-effect"] && !(state.writes) = [Json.Null,Atoms []]);
  List.iter (fun (name,action) ->
    let caught = try ignore (Rows.collect_overload_row_claims (fun () ->
      add_claims name; (!(state.local)).grown_locals <- [name]; action ())); false
      with Json.Error _ | Unexpected -> true in
    require "row failure propagates" caught;
    require "failed row restores enclosing claims" (claims () = enclosing);
    require "failed row retains other effects" ((!(state.local)).grown_locals = [name]))
    ["refused-row",(fun () -> Json.fail "row refusal");
     "unexpected-row",(fun () -> raise Unexpected)];
  print_endline "overload row scopes: claim ownership, nesting and exception restoration passed"

(* The typing point, bounds, execution roots and block return destination each
   have a lexical lifetime independent of speculative candidate output. *)
let () =
  let state = fresh () in
  let contexts () = ((!(state.local)).current_point,!(state.rigid_bounds),
    !(state.typing_roots),!(state.block_result),!(state.block_returned)) in
  let within name action =
    let rigid = {scope=0;index=0;spelling=name} in
    let bounds = [rigid,Atoms []] in
    let roots = [name,Execution.Atom (Json.Null,{Execution.source=Json.Null;impact=Execution.None_}),[]] in
    let returned = ref [Rigid rigid] in
    Analysis_state.with_current_point state name (fun () ->
      Analysis_state.with_rigid_bounds state bounds (fun () ->
        Analysis_state.with_typing_roots state roots (fun () ->
          Analysis_state.with_block_context state None returned (fun () ->
            require "typing scopes expose requested context"
              (contexts () = (name,bounds,roots,None,returned));
            action ())))) in
  let enclosing = contexts () in
  let result = within "parent-context" (fun () ->
    let parent = contexts () in
    require "nested context returns result" (within "child-context" (fun () -> 23) = 23);
    require "nested context restores parent" (contexts () = parent);
    require "context nested speculation refuses" (Analysis_state.speculate state (fun () ->
      within "refused-context" (fun () -> Json.fail "context refusal")) = None);
    require "refused context restores active parent" (contexts () = parent);
    let caught = try ignore (within "unexpected-context" (fun () -> raise Unexpected)); false
      with Unexpected -> true in
    require "typing context unexpected exceptions propagate" caught;
    require "exception restores parent context" (contexts () = parent);
    29) in
  require "typing scopes return result and restore enclosing context"
    (result = 29 && contexts () = enclosing);
  print_endline "typing contexts: dynamic scope, nested refusal and exception restoration passed"
