(* Semantic types contain no solver state. More precise proposals do not mutate them.
   A rigid parameter remains distinct from any future inference/existential IDs. *)
type ty = Atoms of atom list | Rigid of rigid | Union of ty list
and rigid = { scope: int; index: int; spelling: string }
and atom = Nul | Undef | True | False | Num | Str | NumLit of int64 | StrLit of string | Top
         (* Opaque values: every bigint, every symbol. *)
         | Bigint | Symbol
         (* A class value: construct signatures, which `new` meets and no call
            does. A signature's receiver is unused: `new` passes none. *)
         | Ctors of signature list
         | Shape of shape
         (* Declaration identity, with arguments retained for later generic
            instantiation. A recursive reference is never expanded into a
            finite approximation. *)
         | Named of string * ty list
(* A property key: a string, or the symbol the declaration document lists at
   this index. The two spaces never meet. *)
and key = Name of string | Key of int
and field = { name: key; optional: bool; read: ty; write: ty option }
and index_signature = { value: ty; writable: ty option }
and quantifier = { identity: rigid; bound: ty option }
(* `receiver` is the `this` value a call may pass: `Top` for a signature
   indifferent to it. `variadic` is the contract of each actual after `params`,
   for a signature that takes any number of them. *)
and signature = { quantified: quantifier list; receiver: ty; params: ty list;
                  variadic: ty option; result: ty }
and sequence = { required: ty list; optional_elements: ty list; rest: ty option; readonly: bool }
and shape = { fields: field list; string_index: index_signature option; calls: signature list; elements: sequence option }
let record fields = Atoms [Shape {fields;string_index=None;calls=[];elements=None}]
let top = Atoms [Top]
let arrow params result =
  Atoms [Shape {fields=[];string_index=None;calls=[{quantified=[];receiver=top;params;variadic=None;result}];elements=None}]
let quantified_arrow ?(receiver=top) quantified params result =
  Atoms [Shape {fields=[];string_index=None;calls=[{quantified;receiver;params;variadic=None;result}];elements=None}]
let variadic_arrow ?(quantified=[]) ?(receiver=top) params element result =
  Atoms [Shape {fields=[];string_index=None;calls=[{quantified;receiver;params;variadic=Some element;result}];elements=None}]
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
let array elements = Atoms [Shape {fields=[];string_index=None;calls=[];elements=Some elements}]
(* A call may omit a trailing position exactly when its contract admits
   `undefined`: that is the value bound there. Optionality is a property of the
   declared type, not a separate arity record. *)
(* The positions a rest parameter stands for: the required elements of the
   tuple its arguments are collected into. A contract with optional or
   unbounded positions is not a fixed number of further arguments. *)
let tuple_positions = function
  | Atoms [Shape {fields=[];string_index=None;calls=[];elements=Some s}]
    when s.optional_elements=[] && s.rest=None && not s.readonly -> Some s.required
  | _ -> None

(* The contract of each further argument, where a rest parameter's contract is
   a mutable `T[]`: it collects any number of them. *)
let array_element = function
  | Atoms [Shape {fields=[];string_index=None;calls=[];elements=Some s}]
    when s.required=[] && s.optional_elements=[] && not s.readonly -> s.rest
  | _ -> None

let rec admits_undefined = function
  | Atoms xs -> List.exists (function Undef | Top -> true | _ -> false) xs
  | Rigid _ -> false
  | Union ts -> List.exists admits_undefined ts

let rec without_nullish = function
  | Atoms xs -> ground (List.filter (function Nul | Undef -> false | _ -> true) xs)
  | Rigid _ as t -> t | Union ts -> List.fold_left union (Atoms []) (List.map without_nullish ts)
let number_literal spelling = Atoms [NumLit (Int64.bits_of_float (float_of_string spelling))]
