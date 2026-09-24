import Verification.Model.Types.CellUnion

/-! # The fragment language

The subset of TypeScript this pipeline accepts, as an abstract syntax tree:
functions, statements, expressions and type parameters. The tree is declared on
the producer side in `tools/fragment.mts` and written by `tools/fragment-parse.mts`;
the decoders here read that JSON, so the two files describe one language.

Raw claims travel alongside the tree. Types remain JSON until consumed, so
unsupported unused claims do not become invented types. Cell annotations and
claims use the same bounded contract decoder. -/
namespace Verification.Model.Fragment
open Lean ProgramTyping PositiveRules

/-- Validate a free required-parameter signature without projecting away object
requirements: the receiver contract, the parameters, the result, and the
contract of each further actual, for a signature that takes any number of
them. Every signature states its receiver; one indifferent to it states
`unknown`. -/
private def callableShape (a : Json) : Except String (Json × List Json × Json × Option Json) := do
  let rest := (a.getObjVal? "rest").toOption
  CellClaims.fieldsExactly a
    (["a","this","params","result","construct","array"] ++ (if rest.isSome then ["rest"] else []))
  if (← jStr (← jField a "a")) != "function" then throw "expected a function atom"
  for key in ["construct","array"] do
    let mode ← jStr (← jField a key)
    if mode != "unknown" && mode != "absent" then throw "unsupported function object mode"
  let args ← jArr a "params"
  return (← jField a "this", args, ← jField a "result", rest)

/-- The positions a rest parameter stands for: the required elements of its
tuple contract. A contract with optional or unbounded positions is not a fixed
number of further arguments, which is what the callable signature has to say,
so it is refused here rather than approximated. -/
def tupleRequired (j : Json) : Except String (List Json) := do
  CellClaims.fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then
    throw "a rest parameter needs a tuple contract of required positions"
  match ← jArr j "atoms" with
  | [atom] =>
    CellClaims.fieldsExactly atom ["a","required","optional","rest","readonly"]
    if (← jStr (← jField atom "a")) != "array" then
      throw "a rest parameter needs a tuple contract of required positions"
    if ← (← jField atom "readonly").getBool? then
      throw "a rest parameter collects into a fresh array, never a readonly view"
    if !(← jArr atom "optional").isEmpty || (← jField atom "rest") != Json.null then
      throw "a rest parameter needs a tuple contract of required positions"
    jArr atom "required"
  | _ => throw "a rest parameter needs a tuple contract of required positions"

/-- The contract of each further argument a rest parameter collects, where its
contract is a mutable `T[]`; none for any other contract. -/
def arrayElement (j : Json) : Option Json := do
  let .ok false := (← (j.getObjVal? "top").toOption).getBool? | none
  let .ok [atom] := (← (j.getObjVal? "atoms").toOption).getArr?.map (·.toList) | none
  let .ok "array" := (← (atom.getObjVal? "a").toOption).getStr? | none
  let .ok false := (← (atom.getObjVal? "readonly").toOption).getBool? | none
  let .ok [] := (← (atom.getObjVal? "required").toOption).getArr?.map (·.toList) | none
  let .ok [] := (← (atom.getObjVal? "optional").toOption).getArr?.map (·.toList) | none
  let rest ← (atom.getObjVal? "rest").toOption
  if rest == .null then none else some rest

/-- Whether a record claim names an optional field. -/
private def hasOptional (atom : Json) : Bool :=
  match atom.getObjVal? "fields" with
  | .ok (.arr fs) => fs.any fun f => (f.getObjVal? "optional").toOption == some (.bool true)
  | _ => false

mutual
/-- Callable operands may recursively contain callables, arrays and primitives.
Every union and overload arm is checked; record operands remain excluded. -/
partial def callableType (j : Json) : SourceTypes.Lowering (Ty Nat) := do
  CellClaims.fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then return [← SourceTypes.use .top]
  let arms ← (← jArr j "atoms").mapM fun atom => do
    if (← jStr (← jField atom "a")) == "graph" then
      CellClaims.fieldsExactly atom ["a", "label"]
      let label ← (← jField atom "label").getNat?
      if label >= (← get).length then throw "graph label is absent"
      return [label]
    else if (← jStr (← jField atom "a")) == "function" then
      let signatures ← (← CellClaims.conjuncts atom).mapM fun a => do
        let (recv, args, result, rest) ← callableShape a
        return (← receiverType recv, ← args.mapM callableType, ← rest.mapM callableType,
          ← callableType result)
      -- Fixed and variadic signatures of one value sit in one clause: each
      -- says which receivers and actual lists a caller may write.
      let fixed := signatures.filterMap fun (Rc, Ds, E, R) =>
        if E.isNone then some (Rc, Ds, R) else none
      let variadic := signatures.filterMap fun (Rc, Ds, E, R) => E.map fun E => (Rc, Ds, E, R)
      return [← SourceTypes.use (.arrs fixed.eraseDups variadic.eraseDups)]
    else if (← jStr (← jField atom "a")) == "constructor" then
      -- A construct signature: what a class meets and no plain function does.
      -- A generic class's instances form one conjunction: each is a signature.
      let signatures ← (← CellClaims.conjuncts atom).mapM fun a => do
        CellClaims.fieldsExactly a ["a", "params", "result"]
        return (← (← jArr a "params").mapM callableType, ← callableType (← jField a "result"))
      return [← SourceTypes.use (.ctors signatures)]
    else if ["array", "store"].contains (← jStr (← jField atom "a")) then
      return [← arrayType atom]
    else if (← jStr (← jField atom "a")) == "record" &&
        (atom.getObjVal? "indexSignature").toOption.isSome then
      CellClaims.fieldsExactly atom
        ["a", "fields", "indexes", "indexSignature", "call", "construct", "array"]
      -- Keep named invariants and readonly views alongside the index view in
      -- one clause. A mutable named field has one lifetime contract; a
      -- readonly named field contributes no write capability.
      let fields ← (← jArr atom "fields").mapM fun field => do
        CellClaims.fieldsExactly field ["name", "optional", "read", "write"]
        let name ← jStr (← jField field "name")
        if name == SourceTypes.storeField then
          throw "the array store is internal, not a source property"
        if ← (← jField field "optional").getBool? then
          throw "optional named fields with a string index signature are not yet in the source fragment"
        let read ← callableType (← jField field "read")
        let write ← jField field "write"
        if write == Json.mkObj [("top", toJson false), ("atoms", toJson ([] : List Json))] then
          return (name, read, false)
        let written ← callableType write
        if read != written then
          throw "a mutable named field needs one fixed read/write contract"
        return (name, read, true)
      if (fields.map fun (name, _, _) => name).eraseDups.length != fields.length then
        throw "duplicate named field in an indexed object"
      let index ← jField atom "indexSignature"
      CellClaims.fieldsExactly index ["read", "write"]
      let write ← jField index "write"
      if write != Json.mkObj [("top", toJson false), ("atoms", toJson ([] : List Json))] then
        throw "only readonly string index signatures are in the source fragment"
      for key in ["call", "construct", "array"] do
        let mode ← jStr (← jField atom key)
        if mode != "unknown" && mode != "absent" then
          throw "unsupported indexed object mode"
      let indexes ← jField atom "indexes"
      CellClaims.fieldsExactly indexes ["string", "number", "symbol"]
      for key in ["string", "number", "symbol"] do
        let mode ← jStr (← jField indexes key)
        if mode != "absent" && mode != "synthetic" then
          throw "unsupported synthetic index marker"
      let element ← callableType (← jField index "read")
      let invariant := fields.filterMap fun (name, A, writable) =>
        if writable then some (name, A) else none
      let views := fields.filterMap fun (name, A, writable) =>
        if writable then none else some (name, A)
      return [← SourceTypes.use (.dict invariant [] views [element])]
    else if (← jStr (← jField atom "a")) == "record" && hasOptional atom then
      return [← optionalRecord atom]
    else
      let single := Json.mkObj [("top",toJson false),("atoms",toJson [atom])]
      -- The callable table grows as this walks it, so a numeric parameter or
      -- result is interned rather than refused for being outside the four
      -- fixed labels.
      SourceTypes.translateArm (← CellClaims.primitive single)
  return arms.flatten.mergeSort (· ≤ ·) |>.eraseDups

/-- A receiver contract: what a callable operand may be, or an object whose
fields hold such contracts, invariantly or, where the read and write sides
differ, as a view. -/
partial def receiverType (j : Json) : SourceTypes.Lowering (Ty Nat) := do
  CellClaims.fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then return [← SourceTypes.use .top]
  let arms ← (← jArr j "atoms").mapM fun atom => do
    if (← jStr (← jField atom "a")) == "record" then
      if (atom.getObjVal? "and").toOption.isSome then
        throw "a receiver contract is one record, not a conjunction"
      let fields ← CellClaims.decodeShapes
        (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
      let lowered ← fields.mapM fun (name, read, write) => do
        return (name, ← callableType read, ← callableType write)
      let invariant := lowered.filterMap fun (n, r, w) => if r == w then some (n, w) else none
      let views := lowered.filterMap fun (n, r, w) => if r == w then none else some (n, r)
      return [← SourceTypes.use (.refs invariant [] views)]
    else
      callableType (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  return arms.flatten.mergeSort (· ≤ ·) |>.eraseDups

/-- An array type: a tuple contract on a store, held by an object in its store
field, invariantly or, for a readonly array, as a view. Element types are
lowered as callable operands are. -/
partial def arrayType (atom : Json) : SourceTypes.Lowering Nat := do
  CellClaims.fieldsExactly atom ["a","required","optional","rest","readonly"]
  let required ← (← jArr atom "required").mapM callableType
  let optional ← (← jArr atom "optional").mapM callableType
  let restJson ← jField atom "rest"
  let rest ← if restJson == .null then pure none else do pure (some (← callableType restJson))
  let readonly ← (← jField atom "readonly").getBool?
  let store ← SourceTypes.use (.list ⟨required, optional, rest, readonly⟩ [])
  if (← jStr (← jField atom "a")) == "store" then pure store
  else if readonly then SourceTypes.use (.refs [] [] [(SourceTypes.storeField, [store])])
  else SourceTypes.use (.refs [(SourceTypes.storeField, [store])] [] [])

/-- A record with optional fields: each field, required or optional, under
the one contract its read and write agree on. An optional field constrains its
key only where the object has it. Absorption does not apply to these records. -/
partial def optionalRecord (atom : Json) : SourceTypes.Lowering Nat := do
  let fields ← CellClaims.decodeFields
    (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  let lowered ← fields.mapM fun (name, read, write, optional) => do
    let r ← callableType read
    let w ← callableType write
    if r != w then
      throw (if optional then "a readonly optional field needs a view presence form"
        else "cell read and write types do not describe the same invariant")
    return (name, r, optional)
  let required := lowered.filterMap fun (n, t, o) => if o then none else some (n, t)
  let optional := lowered.filterMap fun (n, t, o) => if o then some (n, t) else none
  SourceTypes.use (.refs required [] [] optional)
end

/-- Required record fields admit primitives and callables, but not nested
records. Decode both capabilities through the same table before checking
invariance, field by field. -/
private def cellContract (atom : Json) : SourceTypes.Lowering CellUnion.Contract := do
  let fields ← CellClaims.decodeShapes
    (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  fields.mapM fun (name, read, write) => do
    return ⟨name, ← callableType read, ← callableType write⟩

private def cellConjunction (atom : Json) : SourceTypes.Lowering Nat := do
  let types ← (← CellClaims.conjuncts atom).mapM fun part => do
    let c ← cellContract part
    if !CellUnion.invariant c then
      throw "cell read and write types do not describe the same invariant"
    return c.map fun f => (f.name, f.read)
  let first :: rest := (types.mergeSort CellClaims.beforeFields).eraseDups
    | throw "an empty conjunction is not a contract"
  SourceTypes.use (.refs first rest [])

/-- A callable bag is one value satisfying both contracts, never a union. -/
private def callableObject (atom : Json) : SourceTypes.Lowering Nat := do
  CellClaims.fieldsExactly atom ["a","function","bag"]
  let fn ← jField atom "function"
  let (recv,args,result,rest) ← callableShape fn
  let Rc ← receiverType recv
  let Ds ← args.mapM callableType
  let E ← rest.mapM callableType
  let R ← callableType result
  let c ← cellContract (← jField atom "bag")
  if !CellUnion.invariant c then
    throw "callable field requires an invariant read/write contract"
  match E with
  | none => SourceTypes.use (.callable (c.map fun f => (f.name, f.write)) [] [(Rc,Ds,R)] [])
  | some E => SourceTypes.use (.callable (c.map fun f => (f.name, f.write)) [] [] [(Rc,Ds,E,R)])

/-- Validate every union arm. Record alternatives may absorb a redundant
read/write contract into an existing invariant alternative (CellUnion.normalize_exact).
Other unsupported arms reject the whole type; no projection is allowed.
Record fields admit bounded primitive/callable contracts.
Arrow operands additionally admit callable contracts. -/
def translate (j : Json) : SourceTypes.Lowering (Ty Nat) := do
  if j == Json.mkObj [("unsupported", toJson true)] then
    throw "type claim unavailable from producer"
  CellClaims.fieldsExactly j ["top","atoms"]
  -- `unknown` is semantic top: every value, and no operation through it.
  if ← (← jField j "top").getBool? then return [← SourceTypes.use .top]
  let atoms ← jArr j "atoms"
  let tagged ← atoms.mapM fun atom => do return (← jStr (← jField atom "a"),atom)
  -- A conjunction is one arm of the union, not a union of its own, so each
  -- contributes a single label. Absorption applies to the plain arms, which is
  -- where two contracts can subsume one another.
  let (conjoined, plain) :=
    ((tagged.filter (fun p => p.1 == "record")).map (·.2)).partition
      (fun a => (a.getObjVal? "and").toOption.isSome)
  let (indexed, plain) := plain.partition
    (fun a => (a.getObjVal? "indexSignature").toOption.isSome)
  let (withOptional, plain) := plain.partition hasOptional
  let optionals ← withOptional.mapM fun a => do return [← optionalRecord a]
  let records ← CellUnion.lower (← plain.mapM cellContract)
  let dictionaries ← indexed.mapM fun atom =>
    callableType (Json.mkObj [("top", toJson false), ("atoms", toJson [atom])])
  let conjunctions ← conjoined.mapM fun a => do return [← cellConjunction a]
  let arms ← (tagged.filter (fun p => p.1 != "record")).mapM fun (_,atom) => do
    let single := Json.mkObj [("top",toJson false),("atoms",toJson [atom])]
    match ← jStr (← jField atom "a") with
    | "graph" =>
      CellClaims.fieldsExactly atom ["a", "label"]
      let label ← (← jField atom "label").getNat?
      if label >= (← get).length then throw "graph label is absent"
      return [label]
    | "callable" => return [← callableObject atom]
    | "constructor" => callableType single
    | "array" | "store" => return [← arrayType atom]
    | "function" => callableType single
    -- A number or string arm is interned, so `1` and `number` are separate
    -- labels and the singleton is below the family by the ordinary clause rules.
    | "number" | "numberlit" | "string" | "stringlit" | "void" | "bigint" | "symbol" =>
      SourceTypes.numberLabels (← CellClaims.primitive single)
    | _ => SourceTypes.translate (← CellClaims.primitive single)
  return (records ++ optionals ++ dictionaries ++ conjunctions ++ arms).flatten.mergeSort (· ≤ ·) |>.eraseDups

/-- A point assertion separates the persistent reference type from a current
contents predicate. It is never accepted by erasing `current`. Ordinary function
signatures and nested function operands continue to use `translate`. -/
structure PointType where
  type : Ty Nat
  /-- What the point's record currently holds, field by field, for the fields
  whose read and write contracts differ. A point naming no record has none. -/
  current : Option (List (PropKey × Ty Nat)) := none

def translatePoint (j : Json) : SourceTypes.Lowering PointType := do
  -- Preserve the existing exact union translation when it succeeds.
  match ← SourceTypes.attempt (translate j) with
  | .ok A => return ⟨A,none⟩
  | .error original =>
    -- The persistent contract is what a field may be written; what it holds
    -- now is the read side, stated separately and field by field. Numbers are
    -- interned on both sides, so a numeric field can carry an assertion.
    let .ok fs := CellClaims.decode j | throw original
    let write ← fs.mapM fun f => do return (f.name, ← SourceTypes.translateArm f.write)
    let read ← fs.mapM fun f => do return (f.name, ← SourceTypes.translateArm f.read)
    let current := (read.zip write).filterMap fun (r,w) => if r.2 == w.2 then none else some r
    if current.isEmpty then throw original
    return ⟨[← CellClaims.reference write],some current⟩

/-- The test a logical assignment makes on the target's current value. -/
inductive LogicalOp where
  | nullish | orElse | andAlso
  deriving Repr, DecidableEq

/-- One element of an array pattern: position `index` binds `name`, with a
default when the read is undefined. -/
structure ArrayElem (Expr : Type) where
  index : Nat
  name : String
  namePos : Span
  default_ : Option Expr

/-- A lexically scoped rigid binder. Bounds may mention outer or preceding
binders; the source decoder that consumes the expression checks that scope. -/
structure TypeParam where
  name : String
  bound : Option Json

def decodeTypeParam (j : Json) : Except String TypeParam := do
  CellClaims.fieldsExactly j ["name", "bound"]
  let name ← jStr (← jField j "name")
  if name.isEmpty then throw "empty type-parameter name"
  let b ← jField j "bound"
  return ⟨name, if b == Json.null then none else some b⟩

inductive Expr where
  | var (pos : Span) (name : String)
  | lit (pos : Span) (v : Claim.Val)
  | logical (pos : Span) (andOp : Bool) (left right : Expr)
  | coalesce (pos : Span) (left right : Expr)
  | shapeTest (pos : Span) (tag : Tag) (equal : Bool) (e : Expr)
  /-- Strict equality awaiting a checked singleton operand from source claims. -/
  | equality (pos : Span) (equal : Bool) (left right : Expr)
  | singletonTest (pos : Span) (tag : Tag) (equal testLeft : Bool) (left right : Expr)
  | not (pos : Span) (e : Expr)
  /-- `e as T`, `e satisfies T` or `e!`: the operand's value. An annotation is
  an obligation the operand must meet, never a fact about it. -/
  | cast (pos : Span) (annot : Option Json) (e : Expr)
  /-- An object literal: one named field per initializer, in source order. -/
  | alloc (pos : Span) (names : List String) (es : List Expr)
  | read (pos : Span) (field : String) (e : Expr)
  | write (pos : Span) (field : String) (receiver rhs : Expr)
  /-- `e[key]`: the receiver, then the key, then the read of the field the
  key's claimed type names. The decoder leaves the field unresolved; the
  extractor fills it from the key's claim, a string singleton, and the key's
  expression obligation must establish it. -/
  | index (pos : Span) (field : Option String) (e key : Expr)
  | indexWrite (pos : Span) (field : Option String) (receiver key rhs : Expr)
  /-- An array literal: one element per initializer, in source order. -/
  | arrayLit (pos : Span) (elems : List Expr)
  /-- `[a, b = d] = rhs`: the right side once, then each mutable local takes
  its position of the store, or its default when that read is undefined; the
  value is the right side. -/
  | arrayAssign (pos : Span) (targets : List (ArrayElem Expr)) (rhs : Expr)
  /-- `e[key]` with a numeric key: an element read of the array's store, and
  its assignment; resolved from `index` and `indexWrite` by the key's claim. -/
  | elemAt (pos : Span) (e key : Expr)
  | elemWrite (pos : Span) (receiver key rhs : Expr)
  /-- Arithmetic on two numbers, left operand first. -/
  | arith (pos : Span) (op : Arith) (l r : Expr)
  /-- `target op= rhs`, or an increment when `rhs` is absent: the target's
  parts once, its value read, the right side, the operation, the write back.
  `post` makes the old value the expression's value. -/
  | update (pos : Span) (op : Arith) (target : Expr) (rhs : Option Expr) (post : Bool)
  /-- `target ??= rhs`, `||=` or `&&=`: the target's parts once, its value
  read, the test on it, and the right side written only on the writing arm.
  The Boolean forms need a Boolean target: truthiness is only that. -/
  | logicalAssign (pos : Span) (op : LogicalOp) (target rhs : Expr)
  /-- Read a local once; assign and return the RHS only when nullish. -/
  | nullishAssign (pos : Span) (name : String) (namePos : Span) (rhs : Expr)
  /-- Assignment to a mutable local, which is an expression: it yields the
  value written, where the calculus's write yields null. -/
  | assign (pos : Span) (name : String) (namePos : Span) (rhs : Expr)
  | withValue (pos : Span) (fn initial : Expr) (functionType bagType : Json)
  /-- `params` are what the body reads. `defaults` names the positions a call
  may omit and the expression that replaces the `undefined` bound there; the
  advertised domain at such a position is the parameter's type with
  `undefined`. `receiver` is none for an arrow, whose `this` is a capture; an
  ordinary (strict) function binds the receiver of each call as `this`, at the
  annotation given here. -/
  | lambda (pos : Span) (receiver : Option Json) (typeParams : List TypeParam)
      (params : List (String × Json)) (defaults : List (Nat × Expr)) (rest : Bool)
      (result : Json) (body : Expr)
  /-- A class value: its constructor `lambda` as construct-only code. -/
  | ctor (pos : Span) (lam : Expr)
  /-- `new callee(args)`: the callee, then the actuals, then its construct code. -/
  | construct (pos : Span) (callee : Expr) (args : List Expr)
  | bindWithReceiver (pos : Span) (callee receiver : Expr) (args : List Expr)
  | callWithReceiver (pos : Span) (callee receiver : Expr) (args : List Expr)
  /-- `f.apply(r, list)`: the target, the receiver and the list are saved,
  then the list's length and each index are read in order, before the call. No
  list, or a null or undefined one, gives no actuals. -/
  | applyWithReceiver (pos : Span) (callee receiver : Expr) (list : Option Expr)
  /-- `spreads` are the positions of the arguments written with `...`, in
  increasing order: each stands for the elements of its operand, read where it
  is written. -/
  | call (pos : Span) (callee : Expr) (args : List Expr) (spreads : List Nat)
  /-- A call through a property reference, `o.m(a)`: `callee` is the `read`
  (or `index`) of the method; its object is the receiver. The object is saved,
  the method read and saved, the actuals evaluated, then the saved method is
  invoked with the saved object. -/
  | invoke (pos : Span) (callee : Expr) (args : List Expr) (spreads : List Nat)
  /-- The return statement's entry environment; the expression retains its own span. -/
  | atEnv (pos : Span) (body : Expr)
  /-- Administrative completion and sequencing; neither invents a source expression claim. -/
  | done (pos : Span)
  | seqBody (pos : Span) (init body : Expr)
  /-- Some result denotes a lowered statement conditional with an entry claim;
  none denotes a source ternary whose own expression claim supplies its result. -/
  | ifBody (pos : Span) (result : Option Json) (cond thn els : Expr)
  | letBody (pos : Span) (name : String) (annot : Option Json) (init body : Expr)

/-- Lexical dependencies, including deferred bodies. Exhaustive so a new
executable source form cannot bypass parameter-initialization checks. -/
partial def Expr.freeNames : Expr → List String
  | .var _ n => [n]
  | .lit .. | .done .. => []
  | .lambda _ receiver _ ps ds _ _ b =>
    -- An ordinary function binds its own `this`; an arrow captures it.
    ((ds.flatMap fun d => d.2.freeNames) ++ b.freeNames).filter
      (fun n => !(ps.map Prod.fst).contains n && (receiver.isNone || n != "this"))
  | .shapeTest _ _ _ e | .not _ e | .cast _ _ e | .read _ _ e | .atEnv _ e | .ctor _ e => e.freeNames
  | .construct _ f args => f.freeNames ++ args.flatMap Expr.freeNames
  | .alloc _ _ es | .arrayLit _ es => es.flatMap Expr.freeNames
  | .logical _ _ a b | .coalesce _ a b | .equality _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .index _ _ a b
  | .elemAt _ a b | .arith _ _ a b | .logicalAssign _ _ a b
  | .withValue _ a b _ _ | .seqBody _ a b => a.freeNames ++ b.freeNames
  | .indexWrite _ _ a b c | .elemWrite _ a b c | .ifBody _ _ a b c =>
    a.freeNames ++ b.freeNames ++ c.freeNames
  | .update _ _ a b _ => a.freeNames ++ (b.map Expr.freeNames).getD []
  | .assign _ n _ e | .nullishAssign _ n _ e => n :: e.freeNames
  | .arrayAssign _ targets rhs => rhs.freeNames ++ targets.flatMap
      (fun q => q.name :: (q.default_.map Expr.freeNames).getD [])
  | .bindWithReceiver _ f r args | .callWithReceiver _ f r args =>
    f.freeNames ++ r.freeNames ++ args.flatMap Expr.freeNames
  | .applyWithReceiver _ f r list => f.freeNames ++ r.freeNames ++ (list.map Expr.freeNames).getD []
  | .call _ f args _ | .invoke _ f args _ => f.freeNames ++ args.flatMap Expr.freeNames
  | .letBody _ n _ a b => a.freeNames ++ b.freeNames.filter (· != n)

/-- Every direct call of a named function: the call's span, the callee read's
span, and the name, as `freeNames` binds names. -/
partial def Expr.callees : Expr → List (Span × Span × String)
  | .var .. | .lit .. | .done .. => []
  | .lambda _ _ _ ps ds _ _ b =>
    ((ds.flatMap fun d => d.2.callees) ++ b.callees).filter
      (fun c => !(ps.map Prod.fst).contains c.2.2)
  | .shapeTest _ _ _ e | .not _ e | .cast _ _ e | .read _ _ e | .atEnv _ e | .ctor _ e => e.callees
  | .construct p f args =>
    (match f with | .var q n => [(p, q, n)] | _ => []) ++ f.callees ++ args.flatMap Expr.callees
  | .alloc _ _ es | .arrayLit _ es => es.flatMap Expr.callees
  | .logical _ _ a b | .coalesce _ a b | .equality _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .index _ _ a b
  | .elemAt _ a b | .arith _ _ a b | .logicalAssign _ _ a b
  | .withValue _ a b _ _ | .seqBody _ a b => a.callees ++ b.callees
  | .indexWrite _ _ a b c | .elemWrite _ a b c | .ifBody _ _ a b c =>
    a.callees ++ b.callees ++ c.callees
  | .update _ _ a b _ => a.callees ++ (b.map Expr.callees).getD []
  | .assign _ _ _ e | .nullishAssign _ _ _ e => e.callees
  | .arrayAssign _ targets rhs => rhs.callees ++ targets.flatMap
      (fun q => (q.default_.map Expr.callees).getD [])
  | .bindWithReceiver _ f r args | .callWithReceiver _ f r args =>
    f.callees ++ r.callees ++ args.flatMap Expr.callees
  | .applyWithReceiver _ f r list => f.callees ++ r.callees ++ (list.map Expr.callees).getD []
  | .call p f args _ =>
    (match f with | .var q n => [(p, q, n)] | _ => []) ++ f.callees ++ args.flatMap Expr.callees
  | .invoke _ f args _ => f.callees ++ args.flatMap Expr.callees
  | .letBody _ n _ a b => a.callees ++ b.callees.filter (·.2.2 != n)

/-- Closure conversion for acyclic forward captures. Only a literal closure's
allocation can move; every potentially effectful initializer keeps source order.
No pending binding may be read or exposed by another executing initializer.
A deferred closure is allocated exactly once, after its captures exist. Source
parameters are immutable in this fragment, and mutable outer captures retain
cell identity. Thus delaying this unobservable allocation preserves captures,
aliasing and effects (up to fresh-location renaming). Cyclic/escaping pending
closures require an explicit initialization frame and are refused here. -/
def parameterOrder (ps : List (String × Json)) (defaults : List (Nat × Expr)) :
    Except String (List Nat) := do
  let names := ps.map Prod.fst
  let dependencies (i : Nat) := ((defaults.lookup i).map Expr.freeNames).getD []
    |>.filter names.contains
  let ready (done : List Nat) (i : Nat) :=
    (dependencies i).all fun n => done.any fun j => names[j]? == some n
  let mut done := []
  let mut pending := []
  for i in List.range ps.length do
    if ready done i then done := done ++ [i]
    else
      match defaults.lookup i with
      | some (.lambda ..) => pending := pending ++ [i]
      | _ => throw "parameter default may only read initialized earlier parameters and captures; a pending closure cannot be invoked or exposed"
    -- At most one new dependency is discharged per iteration; the bounded
    -- fixpoint also handles chains of literal closures capturing one another.
    for _ in List.range ps.length do
      if let some j := pending.find? (ready done) then
        done := done ++ [j]
        pending := pending.filter (· != j)
  if !pending.isEmpty then throw "cyclic parameter-default captures require an initialization frame"
  return done

/-- Singleton notation for small source-adapter fixtures. -/
abbrev Expr.lam (p : Span) (name : String) (arg result : Json) (body : Expr) : Expr :=
  .lambda p none [] [(name,arg)] [] false result body
abbrev Expr.app (p : Span) (callee arg : Expr) : Expr := .call p callee [arg] []

def Expr.span : Expr → Span
  | .atEnv _ body | .letBody _ _ _ _ body | .seqBody _ _ body => body.span
  | .ifBody p _ _ _ _ | .done p | .equality p _ _ _ | .singletonTest p _ _ _ _ _ | .coalesce p _ _ | .logical p _ _ _ => p
  | .index p _ _ _ | .indexWrite p _ _ _ _ | .arith p _ _ _ | .update p _ _ _ _ | .logicalAssign p _ _ _ => p
  | .arrayLit p _ | .elemAt p _ _ | .elemWrite p _ _ _ | .arrayAssign p _ _ => p
  | .var p _ | .lit p _ | .shapeTest p _ _ _ | .not p _ | .cast p _ _ | .alloc p _ _ | .read p _ _ | .write p _ _ _ | .assign p _ _ _ | .nullishAssign p _ _ _ | .withValue p _ _ _ _ | .lambda p _ _ _ _ _ _ _ | .call p _ _ _ | .invoke p _ _ _ | .callWithReceiver p _ _ _ | .bindWithReceiver p _ _ _ | .applyWithReceiver p _ _ _ | .ctor p _ | .construct p _ _ => p

/-- One declarator of a `const` or `let`. -/
structure Binding where
  name : String
  namePos : Span
  annot : Option Json
  init : Expr

/-- One property of an object pattern: `field: name = default_`. -/
structure PatternProp where
  field : String
  name : String
  namePos : Span
  default_ : Option Expr

inductive Stmt where
  | ret (pos : Span) (e : Expr)
  /-- Immutable bindings, left to right, each initializer seeing the earlier
  ones. The statement is the entry; no cut separates its declarators. -/
  | constants (pos : Span) (bindings : List Binding)
  /-- Mutable locals, one private cell each. A binding's annotation is the
  storage contract every assignment is checked against; absent, the producer
  supplies one. What the initializer happens to produce is not what the
  binding may later hold. -/
  | mutables (pos : Span) (bindings : List Binding)
  /-- An object pattern on a `const`: the initializer once, then each property
  read in order, a default evaluated only when its read is undefined. -/
  | pattern (pos : Span) (props : List PatternProp) (init : Expr)
  /-- An array pattern: each element reads its position of the initializer's
  store, with a default when the read is undefined. -/
  | arrayPattern (pos : Span) (elems : List (ArrayElem Expr)) (init : Expr)
  | ite (pos : Span) (cond : Expr) (thn : List Stmt) (els : Option (List Stmt))
  | brk (pos : Span)
  | cont (pos : Span)
  | loop (pos : Span) (cond : Expr) (body : List Stmt)
  | effect (pos : Span) (e : Expr)

/-- One element of an array pattern, decoded with the given expression
decoder, since the structure is shared by statements and expressions. -/
def decodeArrayElem (decodeExpr : Json → Except String Expr) (q : Json) :
    Except String (ArrayElem Expr) := do
  CellClaims.fieldsExactly q ["index","name","namePos","default_"]
  let d ← jField q "default_"
  let dflt ← if d == .null then pure none else some <$> decodeExpr d
  return ⟨← (← jField q "index").getNat?, ← jStr (← jField q "name"), ← jSpan q "namePos", dflt⟩

/-- A statement's own span. -/
def Stmt.pos : Stmt → Span
  | .ret p _ | .constants p _ | .mutables p _ | .pattern p _ _ | .arrayPattern p _ _
  | .ite p _ _ _ | .loop p _ _ | .brk p | .cont p | .effect p _ => p

/-- Every direct call of a named function in a statement. -/
partial def Stmt.callees : Stmt → List (Span × Span × String)
  | .ret _ e | .effect _ e => e.callees
  | .constants _ bs | .mutables _ bs => bs.flatMap fun b => b.init.callees
  | .pattern _ props init => init.callees ++
    props.flatMap fun q => (q.default_.map Expr.callees).getD []
  | .arrayPattern _ elems init => init.callees ++
    elems.flatMap fun q => (q.default_.map Expr.callees).getD []
  | .ite _ c t e => c.callees ++ t.flatMap Stmt.callees ++ (e.getD []).flatMap Stmt.callees
  | .loop _ c b => c.callees ++ b.flatMap Stmt.callees
  | .brk .. | .cont .. => []

/-- Singleton notation for small source-adapter fixtures. -/
abbrev Stmt.cst (p : Span) (name : String) (annot : Option Json) (init : Expr) : Stmt :=
  .constants p [⟨name, p, annot, init⟩]
abbrev Stmt.mut (p : Span) (name : String) (namePos : Span) (annot : Option Json) (init : Expr) : Stmt :=
  .mutables p [⟨name, namePos, annot, init⟩]

structure Param where
  name : String
  ty : Json
  /-- A rest parameter stands for the required positions of its tuple
  contract, and binds the array its arguments are collected into. -/
  rest : Bool := false
structure Fn where
  name : String
  namePos : Span
  params : List Param
  ret : Json
  body : List Stmt
structure Claims where
  name : String
  namePos : Span
  params : List (String × Json)
  ret : Json
  envs : List (Nat × List (String × Json))
  exprs : List (Span × Json)

private def decodeArith (j : Json) : Except String Arith := do
  match ← jStr j with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | "div" => pure .div
  | op => throw s!"unknown arithmetic operator '{op}'"

partial def decodeExpr (j : Json) : Except String Expr := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "id" => return .var p (← jStr (← jField j "name"))
  -- No declaration can bind the name `this`, so it names the receiver slot.
  | "this" =>
    CellClaims.fieldsExactly j ["k","pos"]
    return .var p "this"
  | "lit" => return .lit p (← decodeVal (← jField j "lit"))
  | "bin" =>
    let op ← jStr (← jField j "op")
    if op == "&&" || op == "||" then
      return .logical p (op == "&&") (← decodeExpr (← jField j "l")) (← decodeExpr (← jField j "r"))
    if op != "===" && op != "!==" then
      throw s!"unsupported source expression at [{p.1},{p.2}): only strict equality with a null or undefined literal or Boolean &&/|| is supported"
    let left ← decodeExpr (← jField j "l")
    let right ← decodeExpr (← jField j "r")
    match left, right with
    | _, .lit _ .vnull => return .singletonTest p .isNul (op == "===") true left right
    | .lit _ .vnull, _ => return .singletonTest p .isNul (op == "===") false left right
    | _, .lit _ .vundef => return .singletonTest p .isUndef (op == "===") true left right
    | .lit _ .vundef, _ => return .singletonTest p .isUndef (op == "===") false left right
    | _, _ => return .equality p (op == "===") left right
  | "typeofTest" => do
    CellClaims.fieldsExactly j ["k","pos","shape","equal","e"]
    -- Each `typeof` result names one value shape.
    let tag ← match ← jStr (← jField j "shape") with
      | "number" => pure Tag.isNum | "string" => pure .isStr | "boolean" => pure .isBool
      | "undefined" => pure .isUndef | "function" => pure .isFun
      | "bigint" => pure .isBigint | "symbol" => pure .isSymbol
      | other => throw s!"unsupported typeof test '{other}'"
    return .shapeTest p tag (← (← jField j "equal").getBool?) (← decodeExpr (← jField j "e"))
  | "coalesce" => return .coalesce p (← decodeExpr (← jField j "left")) (← decodeExpr (← jField j "right"))
  | "not" => return .not p (← decodeExpr (← jField j "e"))
  | "cast" =>
    CellClaims.fieldsExactly j ["k","pos","cast","annot","e"]
    let kind ← jStr (← jField j "cast")
    if kind != "as" && kind != "satisfies" && kind != "nonNull" then throw "unknown cast kind"
    let a ← jField j "annot"
    if (kind == "nonNull") != (a == .null) then throw "a cast's annotation does not match its kind"
    return .cast p (if a == .null then none else some a) (← decodeExpr (← jField j "e"))
  | "alloc" =>
    let fields ← jArr j "fields"
    let parts ← fields.mapM fun f => do
      return (← jStr (← jField f "name"), ← decodeExpr (← jField f "e"))
    return .alloc p (parts.map Prod.fst) (parts.map Prod.snd)
  | "read" => return .read p (← jStr (← jField j "field")) (← decodeExpr (← jField j "e"))
  | "arith" => do
    CellClaims.fieldsExactly j ["k","pos","op","l","r"]
    return .arith p (← decodeArith (← jField j "op")) (← decodeExpr (← jField j "l")) (← decodeExpr (← jField j "r"))
  | "update" => do
    CellClaims.fieldsExactly j ["k","pos","op","target","rhs","post"]
    let rhs ← jField j "rhs"
    let rhs ← if rhs == .null then pure none else do pure (some (← decodeExpr rhs))
    return .update p (← decodeArith (← jField j "op")) (← decodeExpr (← jField j "target"))
      rhs (← (← jField j "post").getBool?)
  | "arrayLit" => do
    CellClaims.fieldsExactly j ["k","pos","elems"]
    return .arrayLit p (← (← jArr j "elems").mapM decodeExpr)
  | "arrayAssign" => do
    CellClaims.fieldsExactly j ["k","pos","targets","rhs"]
    let targets ← (← jArr j "targets").mapM (decodeArrayElem decodeExpr)
    if targets.isEmpty then throw "an empty pattern binds nothing"
    return .arrayAssign p targets (← decodeExpr (← jField j "rhs"))
  | "index" => do
    CellClaims.fieldsExactly j ["k","pos","e","key"]
    return .index p none (← decodeExpr (← jField j "e")) (← decodeExpr (← jField j "key"))
  | "indexWrite" => do
    CellClaims.fieldsExactly j ["k","pos","receiver","key","rhs"]
    return .indexWrite p none (← decodeExpr (← jField j "receiver")) (← decodeExpr (← jField j "key"))
      (← decodeExpr (← jField j "rhs"))
  | "bindWithReceiver" => do
    CellClaims.fieldsExactly j ["k","pos","callee","receiver","args"]
    return .bindWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) (← (← jArr j "args").mapM decodeExpr)
  | "callWithReceiver" => do
    CellClaims.fieldsExactly j ["k","pos","callee","receiver","args"]
    return .callWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) (← (← jArr j "args").mapM decodeExpr)
  | "applyWithReceiver" => do
    CellClaims.fieldsExactly j ["k","pos","callee","receiver","list"]
    let list ← match ← jField j "list" with
      | .null => pure none
      | l => some <$> decodeExpr l
    return .applyWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) list
  | "withValue" => do
    CellClaims.fieldsExactly j ["k","pos","fn","initial","functionType","bagType"]
    return .withValue p (← decodeExpr (← jField j "fn")) (← decodeExpr (← jField j "initial"))
      (← jField j "functionType") (← jField j "bagType")
  | "ctor" => do
    CellClaims.fieldsExactly j ["k","pos","lambda"]
    let lam ← decodeExpr (← jField j "lambda")
    let .lambda _ none [] _ [] false _ _ := lam
      | throw "a class value is a constructor lambda with plain parameters"
    return .ctor p lam
  | "new" => do
    CellClaims.fieldsExactly j ["k","pos","callee","args"]
    return .construct p (← decodeExpr (← jField j "callee")) (← (← jArr j "args").mapM decodeExpr)
  | "lambda" => do
    -- Two proof fixtures embed parser snapshots from before quantified lambdas.
    -- Live producers always write `typeParams`; absence in those snapshots is
    -- the unique encoding of the former, necessarily empty list.
    let (typeParams, receiver) ← match (j.getObjVal? "typeParams").toOption with
      | some raw => do
        CellClaims.fieldsExactly j ["k","pos","typeParams","receiver","params","result","body"]
        -- An ordinary function records its receiver annotation and whether
        -- its code is strict. Its receiver rule is the strict one: sloppy code
        -- substitutes the global object and boxes primitives, which nothing
        -- here models, so a sloppy function that reads `this` is refused.
        let receiver ← match ← jField j "receiver" with
          | .null => pure none
          | r => do
            CellClaims.fieldsExactly r ["type","strict"]
            pure (some (← jField r "type", ← (← jField r "strict").getBool?))
        pure ((← (← raw.getArr?).toList.mapM decodeTypeParam), receiver)
      | none => do
        CellClaims.fieldsExactly j ["k","pos","params","result","body"]
        pure ([], none)
    let raw ← jArr j "params"
    let restAt := raw.zipIdx.filterMap fun (param,i) =>
      if (param.getObjVal? "rest").toOption.isSome then some i else none
    if restAt.any (· != raw.length - 1) then
      throw "a rest parameter must be the last one"
    let params ← raw.mapM fun param => do
      let fields := ["name","type"] ++
        (if (param.getObjVal? "default").toOption.isSome then ["default"] else []) ++
        (if (param.getObjVal? "rest").toOption.isSome then ["rest"] else [])
      CellClaims.fieldsExactly param fields
      match (param.getObjVal? "rest").toOption with
      | none => pure ()
      | some marked =>
        if !(← marked.getBool?) then throw "a rest parameter is marked by `true`"
        if (param.getObjVal? "default").toOption.isSome then
          throw "a rest parameter cannot have a default"
      return (← jStr (← jField param "name"), ← jField param "type")
    let defaults ← raw.zipIdx.filterMapM fun (param,i) => do
      match (param.getObjVal? "default").toOption with
      | none => return none
      | some d => return some (i, ← decodeExpr d)
    let body ← decodeExpr (← jField j "body")
    if let some (_, false) := receiver then
      if (body :: defaults.map Prod.snd).any (·.freeNames.contains "this") then
        throw s!"unsupported source expression at [{p.1},{p.2}): a function that reads `this` must be strict code"
    return .lambda p (receiver.map Prod.fst) typeParams params defaults (!restAt.isEmpty)
      (← jField j "result") body
  | "doneBody" => return .done p
  | "seqBody" => return .seqBody p (← decodeExpr (← jField j "init")) (← decodeExpr (← jField j "body"))
  | "ifBody" =>
    return .ifBody p (some (← jField j "result")) (← decodeExpr (← jField j "cond"))
      (← decodeExpr (← jField j "then")) (← decodeExpr (← jField j "else_"))
  | "conditional" =>
    return .ifBody p none (← decodeExpr (← jField j "cond"))
      (← decodeExpr (← jField j "then")) (← decodeExpr (← jField j "else_"))
  | "letBody" =>
    let annot ← jField j "annot"
    return .letBody p (← jStr (← jField j "name"))
      (if annot == .null then none else some annot)
      (← decodeExpr (← jField j "init")) (← decodeExpr (← jField j "body"))
  | "returnBody" => return .atEnv p (← decodeExpr (← jField j "e"))
  | "apply" => do
    let args ← (← jArr j "args").mapM decodeExpr
    let spreads ← match (j.getObjVal? "spreads").toOption with
      | none => do
        CellClaims.fieldsExactly j ["k","pos","callee","args"]
        pure []
      | some marked => do
        CellClaims.fieldsExactly j ["k","pos","callee","args","spreads"]
        let spreads ← (← marked.getArr?).toList.mapM fun i => do
          let i ← i.getNat?
          if i ≥ args.length then throw "a spread position names no argument"
          pure i
        if spreads.isEmpty then throw "an empty spread list is written by omitting it"
        if !(spreads.zip spreads.tail).all (fun (a,b) => a < b) then
          throw "spread positions are listed once each, in order"
        pure spreads
    return .call p (← decodeExpr (← jField j "callee")) args spreads
  | "invoke" => do
    let args ← (← jArr j "args").mapM decodeExpr
    let spreads ← match (j.getObjVal? "spreads").toOption with
      | none => do
        CellClaims.fieldsExactly j ["k","pos","callee","args"]
        pure []
      | some marked => do
        CellClaims.fieldsExactly j ["k","pos","callee","args","spreads"]
        let spreads ← (← marked.getArr?).toList.mapM fun i => do
          let i ← i.getNat?
          if i ≥ args.length then throw "a spread position names no argument"
          pure i
        if spreads.isEmpty then throw "an empty spread list is written by omitting it"
        if !(spreads.zip spreads.tail).all (fun (a,b) => a < b) then
          throw "spread positions are listed once each, in order"
        pure spreads
    let callee ← decodeExpr (← jField j "callee")
    match callee with
    | .read .. | .index .. => pure ()
    | _ => throw "a method call's target is a property reference"
    return .invoke p callee args spreads
  | "write" =>
    return .write p (← jStr (← jField j "field")) (← decodeExpr (← jField j "receiver"))
      (← decodeExpr (← jField j "rhs"))
  | "logicalAssign" => do
    CellClaims.fieldsExactly j ["k","pos","op","target","rhs"]
    let op ← match ← jStr (← jField j "op") with
      | "nullish" => pure LogicalOp.nullish
      | "or" => pure .orElse
      | "and" => pure .andAlso
      | op => throw s!"unknown logical assignment '{op}'"
    return .logicalAssign p op (← decodeExpr (← jField j "target")) (← decodeExpr (← jField j "rhs"))
  | "nullishAssign" => do
    CellClaims.fieldsExactly j ["k","pos","name","namePos","rhs"]
    return .nullishAssign p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← decodeExpr (← jField j "rhs"))
  | "assign" => do
    CellClaims.fieldsExactly j ["k","pos","name","namePos","rhs"]
    return .assign p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← decodeExpr (← jField j "rhs"))
  | _ => throw s!"unsupported source expression at [{p.1},{p.2}): expression outside the stateful fragment"

/-- The declarators of a `const` or `let`: at least one, in source order. -/
partial def decodeBindings (j : Json) : Except String (List Binding) := do
  CellClaims.fieldsExactly j ["k","pos","bindings"]
  let bindings ← (← jArr j "bindings").mapM fun b => do
    CellClaims.fieldsExactly b ["name","namePos","annot","init"]
    let a ← jField b "annot"
    return (⟨← jStr (← jField b "name"), ← jSpan b "namePos",
      if a == .null then none else some a, ← decodeExpr (← jField b "init")⟩ : Binding)
  if bindings.isEmpty then throw "a declaration needs a binding"
  return bindings

partial def decodeStmt (j : Json) : Except String Stmt := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "return" => return .ret p (← decodeExpr (← jField j "e"))
  | "effect" => return .effect p (← decodeExpr (← jField j "e"))
  | "const" => return .constants p (← decodeBindings j)
  | "let" => return .mutables p (← decodeBindings j)
  | "arrayPattern" =>
    CellClaims.fieldsExactly j ["k","pos","elems","init"]
    let elems ← (← jArr j "elems").mapM (decodeArrayElem decodeExpr)
    if elems.isEmpty then throw "an empty pattern binds nothing"
    return .arrayPattern p elems (← decodeExpr (← jField j "init"))
  | "pattern" =>
    CellClaims.fieldsExactly j ["k","pos","props","init"]
    let props ← (← jArr j "props").mapM fun q => do
      CellClaims.fieldsExactly q ["field","name","namePos","default_"]
      let d ← jField q "default_"
      let dflt ← if d == .null then pure none else some <$> decodeExpr d
      return (⟨← jStr (← jField q "field"), ← jStr (← jField q "name"), ← jSpan q "namePos", dflt⟩ : PatternProp)
    if props.isEmpty then throw "an empty pattern binds nothing"
    return .pattern p props (← decodeExpr (← jField j "init"))
  | "break" => return .brk p
  | "continue" => return .cont p
  | "while" => return .loop p (← decodeExpr (← jField j "cond")) (← (← jArr j "body").mapM decodeStmt)
  | "if" =>
    let thn ← (← jArr j "then").mapM decodeStmt
    let els ← match ← jField j "else_" with
      | .null => pure none
      | .arr a => pure (some (← a.toList.mapM decodeStmt))
      | _ => throw "malformed else branch"
    return .ite p (← decodeExpr (← jField j "cond")) thn els
  | _ => throw "statement outside the stateful fragment"

def decodeFn (j : Json) : Except String (Fn × List TypeParam) := do
  let typeParams ← (← jArr j "typeParams").mapM decodeTypeParam
  return (⟨← jStr (← jField j "name"), ← jSpan j "namePos",
    ← (← jArr j "params").mapM (fun p => do
      let rest ← match (p.getObjVal? "rest").toOption with
        | none => pure false
        | some b => do
          if !(← b.getBool?) then throw "a rest parameter is marked by `true`"
          pure true
      return ⟨← jStr (← jField p "name"), ← jField p "type", rest⟩),
    ← jField j "retType", ← (← jArr j "body").mapM decodeStmt⟩, typeParams)

def decodeAstWithParams (j : Json) : Except String (List (Fn × List TypeParam)) := do
  CellClaims.fieldsExactly j ["file", "sourceSha256", "declarations", "init", "functions"]
  let document ← jField j "declarations"
  CellClaims.fieldsExactly document ["roots", "definitions", "values", "symbols"]
  if !(← jArr document "roots").isEmpty || !(← jArr document "definitions").isEmpty ||
      !(← jArr document "values").isEmpty || !(← jArr document "symbols").isEmpty then
    throw "type declarations have no certified graph interpretation"
  (← jArr j "functions").mapM decodeFn

/-- The module's top-level code, in source order. -/
def decodeInit (j : Json) : Except String (List Stmt) := do
  (← jArr j "init").mapM decodeStmt

def decodeAst (j : Json) : Except String (List Fn) := do
  (← decodeAstWithParams j).mapM fun (f, tps) => do
    if !tps.isEmpty then throw "generic functions are checked through source extraction"
    return f

def decodeClaims (j : Json) : Except String Claims := do
  let vars := fun j => do
    (← jArr j "vars").mapM fun v => do return (← jStr (← jField v "name"), ← jField v "type")
  return ⟨← jStr (← jField j "name"), ← jSpan j "namePos",
    ← (← jArr j "params").mapM (fun p => do return (← jStr (← jField p "name"), ← jField p "type")),
    ← jField j "retType",
    ← (← jArr j "envs").mapM (fun e => do return ((← jSpan e "pos").1, ← vars e)),
    ← (← jArr j "exprs").mapM (fun e => do return (← jSpan e "pos", ← jField e "type"))⟩

def decodeTypeClaims (j : Json) (fileKey : String) : Except String (List Claims) := do
  for f in (← j.getArr?).toList do
    if (← jStr (← jField f "file")) == fileKey then
      return ← (← jArr f "functions").mapM decodeClaims
  throw "missing claim file"

end Verification.Model.Fragment
