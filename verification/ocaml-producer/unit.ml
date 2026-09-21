let () =
  let roundtrip text =
    let value = Json.parse text in
    assert (Json.parse (Json.encode value) = value) in
  List.iter roundtrip [
    "{\"escaped\":\"a\\nb\\t\\\"\\\\\",\"number\":-1.25e+3,\"other\":[null,true,false]}";
    "\"\\ud83d\\ude00\""; "\"λ😀\""; "[]"; "{}" ];
  List.iter (fun text ->
    match Json.parse text with
    | _ -> failwith ("malformed JSON accepted: " ^ text)
    | exception Json.Error _ -> ())
    ["{\"a\":0,\"a\":1}"; "[1,]"; "01"; "1."; "1e"; "-";
     "\"\\ud800\""; "\"\\udc00\""; "true false"; "\"unclosed" ];
  let open Semantic in
  let a = Rigid {scope=0;index=0;spelling="T"}
  and b = Rigid {scope=1;index=0;spelling="T"} in
  assert (a <> b);
  assert (union a b <> a);
  let identity={scope=2;index=0;spelling="T"} in
  let signature={quantified=[{identity;bound=None}];params=[Rigid identity];result=Rigid identity} in
  let inferred:Inference.instantiation=Inference.infer signature [bool] in
  assert (inferred.Inference.params=[bool]);
  assert (inferred.Inference.result=bool);
  assert (inferred.Inference.substitution=[identity,bool]);
  print_endline "JSON codec, rigid identity and generic inference: passed"
