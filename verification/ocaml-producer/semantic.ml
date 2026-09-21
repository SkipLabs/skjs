(* Semantic types contain no solver state. More precise proposals do not mutate them.
   A rigid parameter remains distinct from any future inference/existential IDs. *)
type ty = Atoms of atom list | Rigid of rigid | Union of ty list
and rigid = { scope: int; index: int; spelling: string }
and atom = Nul | Undef | True | False | Num | Str | Top
         | Shape of shape
and field = { name: string; optional: bool; read: ty; write: ty option }
and signature = { params: ty list; result: ty }
and shape = { fields: field list; calls: signature list }
let record fields = Atoms [Shape {fields;calls=[]}]
let arrow params result = Atoms [Shape {fields=[];calls=[{params;result}]}]
let ground xs = Atoms (List.sort_uniq compare xs)
let bool = ground [True;False]
let union a b = match a,b with
  | Atoms [], t | t, Atoms [] -> t
  | Atoms xs, Atoms ys -> ground (xs @ ys)
  | _ when a=b -> a
  | _ -> let parts = function Union ts -> ts | t -> [t] in
    Union (List.sort_uniq compare (parts a @ parts b))
let widen = function Atoms [True] | Atoms [False] -> bool | t -> t
