open Semantic
open Environment
open Source
open Proposal_types
open Refinement
module Make (S : Analysis_state.Scope) = struct
open Analysis_state.View(S)
  let instance_of ?declared (callee:expr) substitution =
    match callee.node with
    (* A generic method read from its object is claimed at the instance the
       call names: Lean puts the method's scheme below it. *)
    | Read _ | Index _ ->
      (match declared with
       | Some (Atoms [Shape ({calls=[signature];_} as shape)]) ->
         let instance = Inference.substitute substitution
           (Atoms [Shape {shape with calls=[{signature with quantified=[]}]}]) in
         instances := ((!current_point,callee.pos),instance) :: !instances
       | _ -> ())
    | Id n when not (List.mem_assoc n env0) && List.mem_assoc n module_functions ->
      (match Lazy.force (List.assoc n module_functions) with
       | Atoms [Shape ({calls=[signature];_} as shape)] ->
         let instance = Inference.substitute substitution
           (Atoms [Shape {shape with calls=[{signature with quantified=[]}]}]) in
         instances := ((!current_point,callee.pos),instance) :: !instances
       | Atoms [Ctors [signature]] ->
         let instance = Inference.substitute substitution
           (Atoms [Ctors [{signature with quantified=[]}]]) in
         instances := ((!current_point,callee.pos),instance) :: !instances
       | _ -> ())
    | _ -> ()

  let method_read (callee:expr) = match callee.node with
    | Read _ | Index _ -> true | _ -> false

  let quietly f =
    let previous_speculative = !speculative_typing in
    speculative_typing := true;
    let saved = (!closures,!requests,!classes,!entries,!expressions,!instantiations,!instances,!arrows) in
    let metadata = (!evolving,!grown_locals,!exact_locals,!objects,!fresh_constructor,!exact_allocs,
                    !contracts,!current_point) in
    let result = try Some (f ()) with Json.Error _ -> None in
    let (a,b,c,d,e,g,h,i) = saved in
    closures := a; requests := b; classes := c; entries := d; expressions := e;
    instantiations := g; instances := h; arrows := i;
    let (e,g,x,o,f,a,c,p) = metadata in
    evolving := e; grown_locals := g; exact_locals := x; objects := o;
    fresh_constructor := f; exact_allocs := a; contracts := c; current_point := p;
    speculative_typing := previous_speculative;
    result

  let entry env span = match Json.list span with
    | start::_ ->
      (* A field's contents are claimed where its object is still one record. *)
      let bindings = List.filter (fun (n,_) -> not (is_field n) ||
        (match List.assoc_opt (owner n) env with
         | Some (Value t) -> record_field declarations t (field_of n)
         | _ -> false)) env in
      entries := {point = !current_point;start;bindings} :: !entries
    | [] -> Json.fail "empty source span"

end
