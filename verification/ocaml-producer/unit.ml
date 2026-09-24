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
  let signature={quantified=[{identity;bound=None}];receiver=top;params=[Rigid identity];variadic=None;rest_pack=None;result=Rigid identity} in
  let inferred:Inference.instantiation=Inference.infer signature [bool] in
  assert (inferred.Inference.params=[bool]);
  assert (inferred.Inference.result=bool);
  assert (inferred.Inference.substitution=[identity,bool]);
  let infer params actuals = Inference.infer {signature with params} actuals in
  let t=Rigid identity and tru=ground [True] and num=ground [Num] in
  (* Repeated lower constraints join independently of argument order. *)
  assert ((infer [t;t] [tru;bool]).Inference.result=bool);
  assert ((infer [t;t] [bool;tru]).Inference.result=bool);
  (* Contravariant occurrences meet upper bounds, even if the broader one is first. *)
  assert ((infer [arrow [t] bool;arrow [t] bool]
    [arrow [bool] bool;arrow [tru] bool]).Inference.result=tru);
  (* Two parameter reversals recover covariance. *)
  let nested ty=arrow [arrow [ty] bool] bool in
  assert ((infer [nested t;nested t] [nested tru;nested bool]).Inference.result=bool);
  (* A contradiction must still reach independent validation. *)
  assert ((infer [t;arrow [t] num] [bool;arrow [num] num]).Inference.result=bool);
  let u={scope=2;index=1;spelling="U"} and v={scope=2;index=2;spelling="V"} in
  let chain={quantified=[{identity=u;bound=None};{identity;bound=Some (Rigid u)};
    {identity=v;bound=Some t}];receiver=top;params=[Rigid u;t;Rigid v];variadic=None;rest_pack=None;result=Rigid u} in
  let propagated=Inference.infer chain [tru;tru;bool] in
  assert (List.for_all (fun (_,ty) -> ty=bool) propagated.Inference.substitution);
  let boundedUpper={signature with quantified=[{identity=u;bound=None};
    {identity;bound=Some (Rigid u)}];params=[Rigid u;arrow [t] bool]} in
  assert ((Inference.infer boundedUpper [tru;arrow [bool] bool]).Inference.substitution=
    [u,tru;identity,tru]);
  (* Cyclic proposal dependencies terminate; they cannot create semantic types. *)
  let cyclic={signature with quantified=[{identity;bound=Some (Rigid u)};
    {identity=u;bound=Some t}];params=[t;Rigid u]} in
  assert ((Inference.infer cyclic [tru;bool]).Inference.substitution=[identity,bool;u,bool]);
  (* Equal spellings from a different scope are rigid, not solver variables. *)
  assert ((infer [t] [a]).Inference.substitution=[identity,a]);
  print_endline "JSON codec, rigid identity and generic inference: passed"
