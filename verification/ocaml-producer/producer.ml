(* This executable emits proposals, never an acceptance decision. *)
let () = try
  if Array.length Sys.argv <> 2 then Json.fail "usage: producer fragment.json";
  let result = Sys.argv.(1) |> Json.read |> Source.decode |> Proposal.infer |> Claims.encode in
  print_endline (Json.encode result)
with Json.Error e -> prerr_endline e; exit 2
