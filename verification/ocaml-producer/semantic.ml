(* Semantic types contain no solver state. More precise proposals do not mutate them.
   A rigid parameter remains distinct from any future inference/existential IDs. *)
type ty = Atoms of atom list | Rigid of rigid | Union of ty list
and rigid = { scope: int; index: int; spelling: string }
and atom = Nul | Undef | True | False | Num | Str | NumLit of int64 | StrLit of string | Top
         | Shape of shape
and field = { name: string; optional: bool; read: ty; write: ty option }
and quantifier = { identity: rigid; bound: ty option }
and signature = { quantified: quantifier list; params: ty list; result: ty }
and sequence = { required: ty list; optional_elements: ty list; rest: ty option; readonly: bool }
and shape = { fields: field list; calls: signature list; elements: sequence option }
let record fields = Atoms [Shape {fields;calls=[];elements=None}]
let arrow params result =
  Atoms [Shape {fields=[];calls=[{quantified=[];params;result}];elements=None}]
let quantified_arrow quantified params result =
  Atoms [Shape {fields=[];calls=[{quantified;params;result}];elements=None}]
let ground xs = Atoms (List.sort_uniq compare xs)
let bool = ground [True;False]
let union a b = match a,b with
  | Atoms [], t | t, Atoms [] -> t
  | Atoms xs, Atoms ys -> ground (xs @ ys)
  | _ when a=b -> a
  | _ -> let parts = function Union ts -> ts | t -> [t] in
    Union (List.sort_uniq compare (parts a @ parts b))
let rec widen = function
  | Atoms xs -> ground (List.concat_map (function
      | True | False -> [True;False] | NumLit _ -> [Num] | StrLit _ -> [Str]
      | a -> [a]) xs)
  | Rigid _ as t -> t | Union ts -> List.fold_left union (Atoms []) (List.map widen ts)
let array elements = Atoms [Shape {fields=[];calls=[];elements=Some elements}]
(* A call may omit a trailing position exactly when its contract admits
   `undefined`: that is the value bound there. Optionality is a property of the
   declared type, not a separate arity record. *)
let rec admits_undefined = function
  | Atoms xs -> List.exists (function Undef | Top -> true | _ -> false) xs
  | Rigid _ -> false
  | Union ts -> List.exists admits_undefined ts

let rec without_nullish = function
  | Atoms xs -> ground (List.filter (function Nul | Undef -> false | _ -> true) xs)
  | Rigid _ as t -> t | Union ts -> List.fold_left union (Atoms []) (List.map without_nullish ts)
let number_literal spelling = Atoms [NumLit (Int64.bits_of_float (float_of_string spelling))]
