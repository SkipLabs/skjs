(* Semantic types contain no solver state. More precise proposals do not mutate them.
   A rigid parameter remains distinct from any future inference/existential IDs. *)
type ty = Atoms of atom list | Rigid of rigid | Union of ty list
         (* An intersection in a declaration's equation whose operands are
            known only where it is applied: one is a parameter of the
            declaration, `T & { readonly [k: string]: Json }`, or another
            declaration. It is kept, its principal operand first, until the
            application: there it is the one object its operands describe
            where they are records (`Proposal.definition`), and otherwise its
            principal, the parameter's instance, a proposal Lean checks
            against the whole intersection. It never leaves a declaration's
            expansion. *)
         | Meet of ty * ty list
and rigid = { scope: int; index: int; spelling: string }
and atom = Nul | Undef | True | False | Num | Str | NumLit of int64 | StrLit of string | Top
         (* Every bigint; every symbol, an opaque value. *)
         | Bigint | Symbol
         (* One bigint: its canonical decimal integer. *)
         | BigintLit of string
         (* A class value: construct signatures, which `new` meets and no call
            does. A signature's receiver is unused: `new` passes none. *)
         | Ctors of signature list
         | Shape of shape
         (* A record whose own keys are exactly its fields' keys, as a fresh
            object literal's are: no other key, so no prototype. The bound is
            what lets it meet a dictionary, or a record whose optional fields
            it leaves out. *)
         | Exact of field list
         (* Declaration identity, with arguments retained for later generic
            instantiation. A recursive reference is never expanded into a
            finite approximation. *)
         | Named of string * ty list
(* A property key: a string, or the symbol the declaration document lists at
   this index. The two spaces never meet. *)
and key = Name of string | Key of int
and field = { name: key; optional: bool; read: ty; write: ty option }
and index_signature = { value: ty; writable: ty option }
(* Argument lists are not value types. A pack parameter and its instances
   travel through their own substitution projection, never through [ty]. *)
and pack = PackParameter of rigid | Pack of sequence
and type_argument = ValueArgument of ty | PackArgument of pack
and quantifier = { identity: rigid; bound: type_argument option }
(* `receiver` is the `this` value a call may pass: `Top` for a signature
   indifferent to it. `variadic` is the contract of each actual after `params`,
   for a signature that takes any number of them; `rest_pack` the type of all
   of them as one argument list, for a rest typed by a pack parameter or a
   concrete pack instance. At most one is set. *)
and signature = { quantified: quantifier list; receiver: ty; params: ty list;
                  variadic: ty option; rest_pack: pack option; result: ty }
and sequence = { required: ty list; optional_elements: ty list; rest: ty option; readonly: bool }
and shape = { fields: field list; string_index: index_signature option; calls: signature list; elements: sequence option }
let record fields = Atoms [Shape {fields;string_index=None;calls=[];elements=None}]
(* Two object contracts as the one object both describe: their named members,
   which must be disjoint, and the one string index either states. `None`
   where they are not both plain objects so combined: a hint only, as Lean's
   meet gives the intersection its meaning. *)
(* Whether a type mentions a type parameter. *)
let rec mentions_rigid = function
  | Rigid _ -> true
  | Union ts -> List.exists mentions_rigid ts
  | Meet (t,ts) -> List.exists mentions_rigid (t::ts)
  | Atoms atoms -> List.exists (function
      | Named (_,args) -> List.exists mentions_rigid args
      | Shape s ->
        List.exists (fun (f:field) -> mentions_rigid f.read
          || Option.fold ~none:false ~some:mentions_rigid f.write) s.fields
        || Option.fold ~none:false ~some:(fun (i:index_signature) -> mentions_rigid i.value
          || Option.fold ~none:false ~some:mentions_rigid i.writable) s.string_index
        || List.exists signature_mentions_rigid s.calls
        || Option.fold ~none:false ~some:sequence_mentions_rigid s.elements
      | Exact fs -> List.exists (fun (f:field) -> mentions_rigid f.read) fs
      | Ctors signatures -> List.exists signature_mentions_rigid signatures
      | Nul | Undef | True | False | Num | Str | NumLit _ | StrLit _ | Top
      | Bigint | Symbol | BigintLit _ -> false) atoms
and sequence_mentions_rigid s = List.exists mentions_rigid
    (s.required @ s.optional_elements @ Option.to_list s.rest)
and signature_mentions_rigid (s:signature) =
  s.quantified <> [] || s.rest_pack <> None ||
  List.exists mentions_rigid (s.receiver :: s.result :: s.params @ Option.to_list s.variadic)
let meet_objects a b = match a,b with
  | Atoms [Shape x],Atoms [Shape y]
    when x.calls=[] && y.calls=[] && x.elements=None && y.elements=None &&
         (x.string_index=None || y.string_index=None) ->
    let names = List.map (fun (f:field) -> f.name) (x.fields @ y.fields) in
    if List.length names <> List.length (List.sort_uniq compare names) then None
    else Some (Atoms [Shape {x with fields=x.fields @ y.fields;
      string_index=(match x.string_index with None -> y.string_index | own -> own)}])
  | _ -> None
let top = Atoms [Top]
let arrow params result =
  Atoms [Shape {fields=[];string_index=None;calls=[{quantified=[];receiver=top;params;variadic=None;rest_pack=None;result}];elements=None}]
let quantified_arrow ?(receiver=top) quantified params result =
  Atoms [Shape {fields=[];string_index=None;calls=[{quantified;receiver;params;variadic=None;rest_pack=None;result}];elements=None}]
let variadic_arrow ?(quantified=[]) ?(receiver=top) params element result =
  Atoms [Shape {fields=[];string_index=None;calls=[{quantified;receiver;params;variadic=Some element;rest_pack=None;result}];elements=None}]
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
      | BigintLit _ -> [Bigint]
      | a -> [a]) xs)
  | Rigid _ as t -> t | Union ts -> List.fold_left union (Atoms []) (List.map widen ts)
  | Meet (t,ts) -> Meet (widen t,ts)
let array elements = Atoms [Shape {fields=[];string_index=None;calls=[];elements=Some elements}]
(* A call may omit a trailing position exactly when its contract admits
   `undefined`: that is the value bound there. Optionality is a property of the
   declared type, not a separate arity record. *)
(* The positions a rest parameter stands for: the required elements of the
   tuple its arguments are collected into. A contract with optional or
   unbounded positions is not a fixed number of further arguments. *)
let tuple_positions ?(readonly=false) = function
  | Atoms [Shape {fields=[];string_index=None;calls=[];elements=Some s}]
    when s.optional_elements=[] && s.rest=None && (readonly || not s.readonly) -> Some s.required
  | _ -> None

(* The contract of each further argument, where a rest parameter's contract is
   a mutable `T[]` (with [readonly], a `readonly T[]` too: the array a call
   collects is fresh, and a readonly view of it gives up only writes): it
   collects any number of them. *)
let array_element ?(readonly=false) = function
  | Atoms [Shape {fields=[];string_index=None;calls=[];elements=Some s}]
    when s.required=[] && s.optional_elements=[] && (readonly || not s.readonly) -> s.rest
  | _ -> None

let rec admits_undefined = function
  | Atoms xs -> List.exists (function Undef | Top -> true | _ -> false) xs
  | Rigid _ -> false
  | Union ts -> List.exists admits_undefined ts
  | Meet (t,ts) -> List.for_all admits_undefined (t::ts)

let rec without_nullish = function
  | Atoms xs -> ground (List.filter (function Nul | Undef -> false | _ -> true) xs)
  | Rigid _ as t -> t | Union ts -> List.fold_left union (Atoms []) (List.map without_nullish ts)
  | Meet (t,ts) -> Meet (without_nullish t,ts)
(* JavaScript's `ToBoolean` of every value of an atom, where the atom settles
it: null, undefined, `false`, the two zeros, NaN, `""` and `0n` are falsy,
every object, function, class and symbol truthy. *)
let truthiness = function
  | Nul | Undef | False -> Some false
  | True | Symbol | Shape _ | Exact _ | Ctors _ -> Some true
  | NumLit bits -> let x = Int64.float_of_bits bits in Some (not (x = 0. || Float.is_nan x))
  | StrLit s -> Some (s <> "")
  | BigintLit i -> Some (i <> "0")
  | Num | Str | Bigint | Top | Named _ -> None
(* The part of a type a truthiness test answering [truth] leaves: the atoms
   that may answer so. *)
let rec truthy_slice truth = function
  | Atoms xs -> ground (List.filter (fun a -> truthiness a <> Some (not truth)) xs)
  | Rigid _ | Meet _ as t -> t
  | Union ts -> List.fold_left union (Atoms []) (List.map (truthy_slice truth) ts)
let number_literal spelling = Atoms [NumLit (Int64.bits_of_float (float_of_string spelling))]
(* The literal *type* `0` (or `-0`) admits both runtime zeros: TypeScript
   gives `-0` the type `0`, and strict equality equates them. A literal value
   keeps its own bit pattern (`number_literal`); only the type names both, as
   Lean's annotation lowering does (`SourceTypes.numberLabels`). *)
let number_literal_type spelling =
  if float_of_string spelling = 0. then ground [NumLit 0L; NumLit (Int64.bits_of_float (-0.))]
  else number_literal spelling
