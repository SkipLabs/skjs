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
  let signature={call_effect=Unrestricted;quantified=[{identity;bound=None}];receiver=top;params=[Rigid identity];variadic=None;rest_pack=None;result=Rigid identity} in
  let inferred:Inference.instantiation=Inference.infer signature [bool] in
  assert (inferred.Inference.result=bool);
  assert (inferred.Inference.substitution=[identity,ValueArgument bool]);
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
  let chain={call_effect=Unrestricted;quantified=[{identity=u;bound=None};{identity;bound=Some (ValueArgument (Rigid u))};
    {identity=v;bound=Some (ValueArgument t)}];receiver=top;params=[Rigid u;t;Rigid v];variadic=None;rest_pack=None;result=Rigid u} in
  let propagated=Inference.infer chain [tru;tru;bool] in
  assert (List.for_all (fun (_,ty) -> ty=ValueArgument bool) propagated.Inference.substitution);
  let boundedUpper={signature with quantified=[{identity=u;bound=None};
    {identity;bound=Some (ValueArgument (Rigid u))}];params=[Rigid u;arrow [t] bool]} in
  assert ((Inference.infer boundedUpper [tru;arrow [bool] bool]).Inference.substitution=
    [u,ValueArgument tru;identity,ValueArgument tru]);
  (* Cyclic proposal dependencies terminate; they cannot create semantic types. *)
  let cyclic={signature with quantified=[{identity;bound=Some (ValueArgument (Rigid u))};
    {identity=u;bound=Some (ValueArgument t)}];params=[t;Rigid u]} in
  assert ((Inference.infer cyclic [tru;bool]).Inference.substitution=[identity,ValueArgument bool;u,ValueArgument bool]);
  (* Equal spellings from a different scope are rigid, not solver variables. *)
  assert ((infer [t] [a]).Inference.substitution=[identity,ValueArgument a]);
  (* One pack instance must reach both the constructor and the call rest.
     It may contain objects: packs are not a primitive-only inference mode. *)
  let p={scope=3;index=0;spelling="Params"} in
  let object_type=record [{name=Name "value";optional=false;read=num;write=None;host=false}] in
  let pack=Pack {required=[object_type];optional_elements=[];rest=None;readonly=false;dense=true} in
  let constructor={signature with quantified=[];params=[];
    rest_pack=Some (PackParameter p);result=t} in
  let generic={constructor with
    quantified=[{identity=p;bound=Some (PackArgument (Pack {
      required=[];optional_elements=[];rest=Some t;readonly=false;dense=true}))}];
    params=[Atoms [Ctors [constructor]]]} in
  let solution=[p,PackArgument pack;identity,ValueArgument num] in
  let instance=Inference.substitute_signature solution {generic with quantified=[]} in
  let expected_constructor={constructor with rest_pack=Some pack;result=num} in
  assert (instance.params=[Atoms [Ctors [expected_constructor]]]);
  assert (instance.rest_pack=Some pack && instance.result=num);
  (* Re-entering a quantified signature protects its pack binder, while an
     outer value substitution still reaches its bound and nested signatures. *)
  let nested=Inference.substitute_signature solution generic in
  assert (nested.rest_pack=Some (PackParameter p));
  assert (nested.params=[Atoms [Ctors [{constructor with result=num}]]]);
  assert (nested.quantified=[{identity=p;bound=Some (PackArgument (Pack {
    required=[];optional_elements=[];rest=Some num;readonly=false;dense=true}))}]);
  let refuses expected f = match f () with
    | _ -> failwith ("expected substitution refusal: " ^ expected)
    | exception Json.Error message -> assert (message="unsupported: " ^ expected) in
  refuses "pack substitution used as a value type: Params"
    (fun () -> Inference.substitute solution (Rigid p));
  refuses "value substitution used as an argument pack: Params"
    (fun () -> Inference.substitute_pack [p,ValueArgument num] (PackParameter p));
  (* Inner P is a different binder, not a value use of the outer pack P. *)
  let role_terms=Json.parse {|[
    {"k":"pack","of":{"k":"binder","name":"P"}},
    {"k":"scheme","binders":[{"name":"P"}],"signatures":[
      {"k":"binder","name":"P"},{"k":"binder","name":"Outer"}]}]|} in
  assert (Source.binder_use "P" role_terms=(false,true));
  assert (Source.binder_use "Outer" role_terms=(true,false));
  let mixed=Json.Array [role_terms;Json.parse {|{"k":"binder","name":"P"}|}] in
  assert (Source.binder_use "P" mixed=(true,true));
  assert (Source.binder_use "P" (Json.String (Json.encode mixed))=(false,false));
  print_endline "JSON codec, scoped binder roles, sorted substitution and generic inference: passed"
