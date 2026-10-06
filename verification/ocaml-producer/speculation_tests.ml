(* Source cases cannot inspect rollback or inject an unexpected OCaml exception.
   These checks exercise the state boundary used by speculative inference. *)
open Semantic
open Source
open Analysis_state

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
