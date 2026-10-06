open Semantic
open Source


(* A module function as its callers see it: an ordinary function at exactly its
   annotated parameters and result. A rest parameter contributes its tuple's
   positions or its array's element. Generic ones are not reachable yet. *)
(* A leading `this: T` parameter is the receiver, not a position. *)
let module_type (g:Source.fn) =
  let receiver,params = match g.params with
    | ("this",t) :: rest -> t,rest
    | params -> top,params in
  let tys = List.map snd params in
  match g.rest,List.rev tys with
  | true,last::before ->
    (match Semantic.tuple_positions ~readonly:true last,Semantic.array_element ~readonly:true last with
     | Some positions,_ -> quantified_arrow ~receiver g.quantified (List.rev before @ positions) g.result
     | None,Some element -> variadic_arrow ~quantified:g.quantified ~receiver (List.rev before) element g.result
     | _ -> Proposal_diagnostics.unsupported "rest parameter contract of a module function")
  | _ -> quantified_arrow ~receiver g.quantified tys g.result

