(* This executable emits proposals, never an acceptance decision. With
   `--explain`, it prints instead the known causes of failure it met, each at
   its source span (`Proposal.explain`), for naming a failed search. *)
let () =
  match Array.to_list Sys.argv with
  | [_;"--explain";file] ->
    Proposal.explaining := true;
    (try ignore (file |> Json.read |> Source.decode |> Proposal.infer) with Json.Error _ -> ());
    print_endline (Json.encode (Json.Array (List.rev_map (fun (pos,reason) ->
      Json.Object ["pos",pos;"reason",Json.String reason]) !Proposal.explanations)))
  | _ -> try
    let file = match Array.to_list Sys.argv with
      | [_;file] -> file
      | _ -> Json.fail "usage: producer [--explain] fragment.json" in
    let result = file |> Json.read |> Source.decode |> Proposal.infer |> Claims.encode in
    print_endline (Json.encode result)
  with Json.Error e -> prerr_endline e; exit 2
