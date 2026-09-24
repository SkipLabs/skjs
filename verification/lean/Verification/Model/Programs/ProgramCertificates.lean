import Verification.Model.Programs.ProgramTyping

/-! Finite program evidence checked against the declarative rules. Each node
states its sequent explicitly. The external entry point also checks that the
root is the requested closed program and type; evidence cannot change the task.
No proof search or semantic observation budget is involved. -/
namespace Verification.Model.ProgramCertificates
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules

structure Sequent (ι : Type) where
  context : List (Ty ι)
  term : Tm
  type : Ty ι
  deriving DecidableEq

/-- What a literal index names in a tuple contract, as the checker reads it: a
required position's type; an optional or rest position's type with `undefined`;
any named position's type. -/
def requiredAt (T : Tuple (Ty ι)) (b : UInt64) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => T.required[k]?

def optionalAt (T : Tuple (Ty ι)) (b : UInt64) (U : Ty ι) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => match T.required[k]? with
    | some _ => none
    | none => (positionTy T k).map (· ++ U)

def namedAt (T : Tuple (Ty ι)) (b : UInt64) : Option (Ty ι) :=
  (indexOfBits b).bind fun k => positionTy T k

inductive Rule (ι : Type) where
  | var | nul | undef | tru | fls | truLit | flsLit | numLit | num | strLit | str
  | funE | app | letE | alloc | allocDict | read | readView | write | arith | test
  | readDict (element undef : Ty ι)
  | indexDict (element undef : Ty ι)
  | readOptional (element undef : Ty ι)
  | arrLit | elem | setElem | len
  | elemOpt (undef : Ty ι)
  | elemAny (undef : Ty ι)
  | ifBool | ifTrue | ifFalse
  | ifKnown (answer : Bool)
  | ifBoolVar (trueType falseType : Ty ι)
  | unionVar (slot : Nat)
  | makeCallable | callCallable | readCallable | writeCallable
  /-- The rest-array type of each signature, in the signatures' order. -/
  | funRest (arrays : List (Ty ι))
  /-- A callable object with variadic code: the rest-array type of each signature. -/
  | makeCallableRest (arrays : List (Ty ι))
  /-- A copy of a spread, at the element type its store holds. -/
  | arrCopy (elem : Ty ι)
  /-- How many actuals are fixed, which later ones are spreads, and the rest
  type the further ones fit. -/
  | callRest (fixed omitted : Nat) (spreads : List Bool) (rest : Ty ι)
  /-- A bound function: its saved slots are read from the context. -/
  | bindE
  /-- A bound variadic function, likewise. -/
  | bindRestE
  /-- A class value: the `undefined` type its bodies' receiver has. -/
  | ctorE (undef : Ty ι)
  /-- `new`: the constructor, then the actuals in order. -/
  | construct
  | sub (proof : PositiveCertificates.Proof ι)

inductive Evidence (ι : Type) where
  | node (claim : Sequent ι) (rule : Rule ι) (premises : List (Evidence ι))

def claim : Evidence ι → Sequent ι
  | .node j _ _ => j

/-- The premises a function-creation node owes: one checked body per declared
signature, in the order the checker expects. -/
abbrev funEPremises [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (A : Ty ι)
    (arity : Nat) (b : Tm) (ps : List (Sequent ι)) : Prop :=
  match expand G A with
  | [.arrs L []] => (∀ p ∈ L, p.2.1.length = arity) ∧
      ps = L.map (fun p => ⟨p.1 :: p.2.1 ++ Γ, b, p.2.2⟩)
  | _ => False

/-- The premises a class-value node owes: one checked body per construct
signature, whose receiver is `undefined`. -/
abbrev ctorEPremises [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (A U : Ty ι)
    (arity : Nat) (b : Tm) (ps : List (Sequent ι)) : Prop :=
  match expand G A with
  | [.ctors L] => (∀ p ∈ L, p.1.length = arity) ∧ ps = L.map (fun p => ⟨U :: p.1 ++ Γ, b, p.2⟩)
  | _ => False

/-- The slots a prefix of saved variables names, when every entry is one. -/
def varSlots : List Tm → Option (List Nat)
  | [] => some []
  | .var i :: ts => (varSlots ts).map (i :: ·)
  | _ :: _ => none

theorem varSlots_map (saved : List Nat) : varSlots (saved.map .var) = some saved := by
  induction saved <;> simp_all [varSlots]

theorem varSlots_eq : ∀ {ts : List Tm} {saved : List Nat}, varSlots ts = some saved →
    ts = saved.map .var
  | [], _, h => by simp [varSlots] at h; subst h; rfl
  | .var i :: ts, saved, h => by
    simp only [varSlots, Option.map_eq_some_iff] at h
    obtain ⟨rest, hr, rfl⟩ := h
    simp [varSlots_eq hr]
  | .invoke .. :: _, _, h | .letE .. :: _, _, h | .nul :: _, _, h | .undef :: _, _, h
  | .tru :: _, _, h | .fls :: _, _, h | .num _ :: _, _, h | .str _ :: _, _, h
  | .objAt .. :: _, _, h | .makeAt .. :: _, _, h | .readAt .. :: _, _, h
  | .writeAt .. :: _, _, h | .test .. :: _, _, h | .ite .. :: _, _, h | .arith .. :: _, _, h
  | .arr _ :: _, _, h | .arrLit _ :: _, _, h | .elemAt .. :: _, _, h | .setElem .. :: _, _, h
  | .lenOf _ :: _, _, h | .spread _ :: _, _, h => by simp [varSlots] at h

theorem filterMap_of_map {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.map f = ys.map some → xs.filterMap f = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [List.filterMap_cons, h.1, filterMap_of_map h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Only finite, syntactic premises of one rule. -/
def Local [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι)) : Prop :=
  match r, j.term, ps with
  | .var, .var i, [] => j.context[i]? = some j.type
  | .nul, .nul, [] => Represents G j.type .nul
  | .undef, .undef, [] => Represents G j.type .undef
  | .tru, .tru, [] | .fls, .fls, [] => Represents G j.type .bool
  | .truLit, .tru, [] => Represents G j.type (.boolLit true)
  | .flsLit, .fls, [] => Represents G j.type (.boolLit false)
  | .numLit, .num b, [] => Represents G j.type (.numLit b)
  | .num, .num _, [] => Represents G j.type .num
  | .strLit, .str s, [] => Represents G j.type (.strLit s)
  | .str, .str _, [] => Represents G j.type .str
  -- A source function has no properties of its own; the model still gives it a
  -- bag, so the shape of that allocation is fixed here rather than claimed.
  | .funE, .makeAt (.closure arity b) ns inits, ps =>
    ns = [valueField] ∧ inits = [Tm.nul] ∧ funEPremises G j.context j.type arity b ps
  -- The callee, then the receiver at the selected signature's receiver, then
  -- the actual premises in order, then one premise per position the signature
  -- declares and this call omits. Each of those proves `undefined` at its
  -- declared type: the value the machine binds there.
  | .app, .invoke f r args, jf :: jr :: jas =>
    jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
    (jas.take args.length).map Sequent.term = args ∧
    (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
    (∀ ja ∈ jas, ja.context = j.context) ∧
    match expand G jf.type with
    | [.arrs L _] => (jr.type, jas.map Sequent.type, j.type) ∈ L
    | _ => False
  | .letE, .letE a b, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb = ⟨ja.type :: j.context, b, j.type⟩
  | .alloc, .makeAt .absent ns inits, ps =>
    match expand G j.type with
    | [.refs fs [] []] =>
      ns.Nodup ∧ ns.length = ps.length ∧ ps.map Sequent.term = inits ∧
      (∀ p ∈ ps, p.context = j.context) ∧ fs = ns.zip (ps.map Sequent.type)
    | _ => False
  | .allocDict, .makeAt .absent ns inits, ps =>
    match expand G j.type with
    | [.dict [] [] [] [E]] =>
      ns.Nodup ∧ ns.length = ps.length ∧ ps.map Sequent.term = inits ∧
      (∀ p ∈ ps, p.context = j.context ∧ p.type = E)
    | _ => False
  | .read, .readAt f a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧
    (match expand G ja.type with
     | [.refs fs [] _ _] => (f, j.type) ∈ fs
     | _ => False)
  | .readView, .readAt f a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧
    (match expand G ja.type with
     | [.refs _ [] vs _] => (f, j.type) ∈ vs
     | _ => False)
  | .readOptional A U, .readAt f a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧ Represents G U .undef ∧ j.type = A ++ U ∧
    (match expand G ja.type with
     | [.refs _ [] _ os] => (f, A) ∈ os
     | _ => False)
  | .readDict A U, .readAt (.str _) a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧ Represents G U .undef ∧ j.type = A ++ U ∧
    (match expand G ja.type with
     | [.dict _ [] _ ix _] => A ∈ ix
     | _ => False)
  | .indexDict A U, .indexAt a key, [ja, jk] =>
    ja.context = j.context ∧ ja.term = a ∧
    jk.context = j.context ∧ jk.term = key ∧
    Represents G jk.type .str ∧ Represents G U .undef ∧ j.type = A ++ U ∧
    (match expand G ja.type with
     | [.dict _ [] _ ix _] => A ∈ ix
     | _ => False)
  | .write, .writeAt f a b, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
    Represents G j.type .nul ∧
    (match expand G ja.type with
     | [.refs fs [] _ _] => (f, jb.type) ∈ fs
     | _ => False)
  | .arith, .arith _ a b, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
    Answers G ja.type .isNum true ∧ Answers G jb.type .isNum true ∧ Represents G j.type .num
  | .test, .test _ a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧
    (.boolLit true) ∈ expand G j.type ∧ (.boolLit false) ∈ expand G j.type
  | .arrLit, .arrLit inits, ps =>
    match expand G j.type with
    | [.list T []] =>
      ps.map Sequent.term = inits ∧ (∀ p ∈ ps, p.context = j.context) ∧
      T.required.length ≤ ps.length ∧
      (T.rest = none → ps.length ≤ T.required.length + T.optional.length) ∧
      ∀ q ∈ ps.zipIdx, positionTy T q.2 = some q.1.type
    | _ => False
  | .elem, .elemAt a i, [ja, ji] =>
    ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
    (match expand G ja.type, expand G ji.type with
     | [.list T []], [.numLit b] => requiredAt T b = some j.type
     | _, _ => False)
  | .elemOpt U, .elemAt a i, [ja, ji] =>
    ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
    Represents G U .undef ∧
    (match expand G ja.type, expand G ji.type with
     | [.list T []], [.numLit b] => optionalAt T b U = some j.type
     | _, _ => False)
  | .elemAny U, .elemAt a i, [ja, ji] =>
    ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
    Represents G U .undef ∧ Answers G ji.type .isNum true ∧
    (match expand G ja.type with
     | [.list ⟨[], [], some E, false⟩ []] => j.type = E ++ U
     | _ => False)
  | .setElem, .setElem a i v, [ja, ji, jv] =>
    ja.context = j.context ∧ ja.term = a ∧ ji.context = j.context ∧ ji.term = i ∧
    jv.context = j.context ∧ jv.term = v ∧ j.type = ja.type ∧
    (match expand G ja.type, expand G ji.type with
     | [.list T []], [.numLit b] => namedAt T b = some jv.type ∧ T.readonly = false
     | _, _ => False)
  | .len, .lenOf a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧ Represents G j.type .num ∧
    (match expand G ja.type with
     | [.list _ []] => True
     | _ => False)
  | .ifBool, .ite c t e, [jc,jt,je] =>
    jc.context = j.context ∧ jc.term = c ∧ Answers G jc.type .isBool true ∧
    jt = ⟨j.context,t,j.type⟩ ∧ je = ⟨j.context,e,j.type⟩
  | .ifKnown q, .ite c t e, [jc,jb] =>
    jc.context = j.context ∧ jc.term = c ∧ Represents G jc.type (.boolLit q) ∧
    jb = ⟨j.context, (if q then t else e), j.type⟩
  | .ifBoolVar T F, .ite (.var i) t e, [jt,je] =>
    (match j.context[i]? with | some C => Answers G C .isBool true | none => False) ∧
    Represents G T (.boolLit true) ∧ Represents G F (.boolLit false) ∧
    jt = ⟨j.context.set i T,t,j.type⟩ ∧ je = ⟨j.context.set i F,e,j.type⟩
  | .ifTrue, .ite (.test tag (.var i)) u _, [ju] =>
    ju = ⟨j.context, u, j.type⟩ ∧
    match j.context[i]? with
    | some A => Answers G A tag true
    | none => False
  | .ifFalse, .ite (.test tag (.var i)) _ e, [je] =>
    je = ⟨j.context, e, j.type⟩ ∧
    match j.context[i]? with
    | some A => Answers G A tag false
    | none => False
  | .unionVar i, _, ps =>
    match j.context[i]? with
    | some C => ps = C.map (fun a => ⟨j.context.set i [a], j.term, j.type⟩)
    | none => False
  -- The bag's premises come first, one per named field, then the body's.
  | .makeCallable, .makeAt (.closure arity b) ns inits, ps =>
    match expand G j.type with
    | [.callable P [] L []] =>
      ns.Nodup ∧ ns.length = inits.length ∧
      (ps.take ns.length).map Sequent.term = inits ∧
      (∀ p ∈ ps.take ns.length, p.context = j.context) ∧
      P = ns.zip ((ps.take ns.length).map Sequent.type) ∧
      (∀ p ∈ L, p.2.1.length = arity) ∧
      ps.drop ns.length = L.map (fun p => ⟨p.1 :: p.2.1 ++ j.context,b,p.2.2⟩)
    | _ => False
  | .callCallable, .invoke f r args, jf :: jr :: jas =>
    jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
    (jas.take args.length).map Sequent.term = args ∧
    (∀ ja ∈ jas.drop args.length, ja.term = .undef) ∧
    (∀ ja ∈ jas, ja.context = j.context) ∧
    match expand G jf.type with
    | [.callable _ _ L _] => (jr.type, jas.map Sequent.type,j.type) ∈ L
    | _ => False
  | .readCallable, .readAt f a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧
    match expand G ja.type with
    | [.callable P _ _ _] => (f, j.type) ∈ P
    | _ => False
  | .writeCallable, .writeAt f a b, [ja,jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
    Represents G j.type .nul ∧
    match expand G ja.type with
    | [.callable P _ _ _] => (f, jb.type) ∈ P
    | _ => False
  -- One body premise per signature, with the rest array in slot 0, then the
  -- fixed parameters and the receiver.
  | .funRest As, .makeAt (.variadic n b) ns inits, ps =>
    ns = [valueField] ∧ inits = [Tm.nul] ∧
    match expand G j.type with
    | [.arrs [] L] => L.length = As.length ∧
      (∀ p ∈ L.zip As, p.1.2.1.length = n ∧ RestArray G p.2 p.1.2.2.1) ∧
      ps = (L.zip As).map (fun p => ⟨p.2 :: p.1.1 :: p.1.2.1 ++ j.context, b, p.1.2.2.2⟩)
    | _ => False
  -- The bag's premises come first, one per named field, then one body premise
  -- per signature with its rest array in slot 0.
  | .makeCallableRest As, .makeAt (.variadic n b) ns inits, ps =>
    match expand G j.type with
    | [.callable P [] [] L] =>
      ns.Nodup ∧ ns.length = inits.length ∧
      (ps.take ns.length).map Sequent.term = inits ∧
      (∀ p ∈ ps.take ns.length, p.context = j.context) ∧
      P = ns.zip ((ps.take ns.length).map Sequent.type) ∧
      L.length = As.length ∧
      (∀ p ∈ L.zip As, p.1.2.1.length = n ∧ RestArray G p.2 p.1.2.2.1) ∧
      ps.drop ns.length =
        (L.zip As).map (fun p => ⟨p.2 :: p.1.1 :: p.1.2.1 ++ j.context, b, p.1.2.2.2⟩)
    | _ => False
  -- The one premise is the store the spread reads.
  | .arrCopy E, .arrLit [.spread s], [js] =>
    js.context = j.context ∧ js.term = s ∧ SpreadsInto G js.type E ∧
    Represents G j.type (.list ⟨[], [], some E, false⟩ [])
  -- The callee, the receiver, the fixed actuals, one `undefined` premise per
  -- fixed position the call omits, then one premise per further part: the
  -- actual itself, or the store a spread reads. A call that omits a position
  -- writes no part.
  | .callRest k u flags P, .invoke f r args, jf :: jr :: jas =>
    jf.context = j.context ∧ jf.term = f ∧ jr.context = j.context ∧ jr.term = r ∧
    (∀ ja ∈ jas, ja.context = j.context) ∧
    jas.length = k + u + flags.length ∧ (u = 0 ∨ flags = []) ∧
    args = (jas.take k).map Sequent.term ++
      (flags.zip (jas.drop (k + u))).map (fun q => spreadTerm (q.1, q.2.term)) ∧
    (∀ ja ∈ (jas.drop k).take u, ja.term = .undef) ∧
    RestParts G P ((flags.zip (jas.drop (k + u))).map fun q => (q.1, q.2.type)) ∧
    (jr.type, (jas.take (k + u)).map Sequent.type, P, j.type) ∈ restSigs G jf.type
  -- `.bind`'s saved slots, with no premises: the target's selected signature
  -- starts with the prefix slots' contracts, and the result takes the rest at
  -- the one receiver it states, whatever that is.
  | .bindE, .makeAt (.bound (.var t) (.var r) pre) ns inits, [] =>
    ns = [] ∧ inits = [] ∧
    match varSlots pre, j.context[t]?, j.context[r]?, expand G j.type with
    | some saved, some T, some Rt, [.arrs [(_, Ds, R)] []] =>
      saved.map (j.context[·]?) = (saved.filterMap (j.context[·]?)).map some ∧
      (Rt, saved.filterMap (j.context[·]?) ++ Ds, R) ∈ callSigs G T
    | _, _, _, _ => False
  -- As `bindE`, for a variadic signature of the target with an element rest:
  -- the prefix takes its first fixed positions, and past them the element.
  | .bindRestE, .makeAt (.bound (.var t) (.var r) pre) ns inits, [] =>
    ns = [] ∧ inits = [] ∧
    match varSlots pre, j.context[t]?, j.context[r]?, expand G j.type with
    | some saved, some T, some Rt, [.arrs [] [(_, Ds, E', R)]] =>
      saved.map (j.context[·]?) = (saved.filterMap (j.context[·]?)).map some ∧
      ∃ s ∈ restSigs G T, s.1 = Rt ∧ s.2.2.1 = E' ∧ s.2.2.2 = R ∧
        Ds = s.2.1.drop saved.length ∧ ∃ El ∈ (restElem G E').toList,
        saved.filterMap (j.context[·]?) =
          s.2.1.take saved.length ++ List.replicate (saved.length - s.2.1.length) El
    | _, _, _, _ => False
  -- A class value: a function's allocation with construct-only code.
  | .ctorE U, .makeAt (.closure arity b .construct) ns inits, ps =>
    ns = [valueField] ∧ inits = [Tm.nul] ∧ Represents G U .undef ∧
      ctorEPremises G j.context j.type U arity b ps
  | .construct, .construct f args, jf :: jas =>
    jf.context = j.context ∧ jf.term = f ∧ jas.map Sequent.term = args ∧
    (∀ ja ∈ jas, ja.context = j.context) ∧
    match expand G jf.type with
    | [.ctors L] => (jas.map Sequent.type, j.type) ∈ L
    | _ => False
  | .sub proof, _, [jt] =>
    jt.context = j.context ∧ jt.term = j.term ∧
    PositiveCertificates.check G jt.type j.type proof = true
  | _, _, _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (r : Rule ι) (ps) :
    Decidable (Local G j r ps) := by
  unfold Local
  split <;> try infer_instance
  all_goals try dsimp [Represents, Answers, funEPremises, ctorEPremises]
  all_goals first | infer_instance | (split <;> infer_instance)

def checkTree [DecidableEq ι] (G : NormalGraph ι) : Evidence ι → Bool
  | .node j r ps => decide (Local G j r (ps.map claim)) && ps.attach.all (fun e => checkTree G e.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem e.property
  simp only [Evidence.node.sizeOf_spec]
  omega

mutual
def checkScope (d : Nat) : Tm → Bool
  | .var i => decide (i < d)
  | .objAt _ .absent => true
  | .objAt _ (.closure n b _) => checkScope (d+n+1) b
  | .makeAt (.closure n b _) _ args => checkScope (d+n+1) b && checkScopes d args
  | .objAt _ (.variadic n b) => checkScope (d+n+2) b
  | .makeAt (.variadic n b) _ args => checkScope (d+n+2) b && checkScopes d args
  | .objAt _ (.bound t r pre) => checkScope d t && checkScope d r && checkScopes d pre
  | .makeAt (.bound t r pre) _ args =>
      checkScope d t && checkScope d r && checkScopes d pre && checkScopes d args
  | .makeAt .absent _ args => checkScopes d args
  | .letE a b => checkScope d a && checkScope (d+1) b
  | .invoke f r args => checkScope d f && checkScope d r && checkScopes d args
  | .construct f args => checkScope d f && checkScopes d args
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b =>
      checkScope d a && checkScope d b
  | .readAt _ a | .test _ a | .lenOf a | .spread a => checkScope d a
  | .setElem a b c => checkScope d a && checkScope d b && checkScope d c
  | .arrLit args => checkScopes d args
  | .args vs => checkScopes d vs
  | .ite c a b => checkScope d c && checkScope d a && checkScope d b
  | _ => true

def checkScopes (d : Nat) : List Tm → Bool
  | [] => true
  | a :: args => checkScope d a && checkScopes d args
end

@[simp] theorem checkScopes_iff (d : Nat) (args : List Tm) :
    checkScopes d args = true ↔ ∀ a ∈ args, checkScope d a = true := by
  induction args <;> simp_all [checkScopes]

theorem checkScope_iff (d : Nat) (t : Tm) : checkScope d t = true ↔ Scoped d t := by
  induction t using Tm.induct generalizing d <;> simp_all [checkScope, Scoped, and_assoc]

/-- Bind evidence to the actual requested program, type and empty context.
Scope includes unselected branches and bodies of empty overloads. -/
def check [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) (e : Evidence ι) : Bool :=
  decide (claim e = ⟨[], t, A⟩) && checkScope 0 t && checkTree G e

theorem local_sound [DecidableEq ι] {G : NormalGraph ι} {j r ps}
    (hl : Local G j r ps)
    (hp : ∀ p ∈ ps, HasTy G p.context p.term p.type) : HasTy G j.context j.term j.type := by
  rcases j with ⟨Γ, t, A⟩
  unfold Local at hl
  split at hl <;> (try dsimp only at *) <;> (try subst t)
  · exact .var hl
  · exact .nul hl
  · exact .undef hl
  · exact .tru hl
  · exact .fls hl
  · exact .truLit hl
  · exact .flsLit hl
  · exact .numLit hl
  · exact .num hl
  · exact .strLit hl
  · exact .str hl
  · rename_i ps arity b ns inits
    obtain ⟨rfl, rfl, hl⟩ := hl
    unfold funEPremises at hl
    split at hl
    · rename_i L hL
      apply HasTy.funE hL hl.1
      intro p hmem
      apply hp ⟨p.1 :: p.2.1 ++ Γ, b, p.2.2⟩
      rw [hl.2]
      exact List.mem_map.mpr ⟨p, hmem, rfl⟩
    · contradiction
  · rename_i f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    split at hL
    · rename_i L he
      -- The actual premises and the omitted-position premises are the same list,
      -- split at the number of actuals the call writes.
      have ha : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type,ja.term)),
          HasTy G Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hcontexts ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTy G Γ .undef A := by
        intro A hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja)))
        rw [hcontexts ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type,ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      have h := HasTy.app hf he (xs := (jas.take args.length).map (fun ja => (ja.type,ja.term)))
        (Us := (jas.drop args.length).map Sequent.type)
        (by rw [hsplit]; exact hL) hrt ha hu
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓ, ht, rfl⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    exact .letE ha (hp ⟨ja.type :: Γ, b, A⟩ (by simp))
  · rename_i ps _ _ _ ns inits
    split at hl
    · rename_i fs he
      obtain ⟨hnd, hlen, hterms, hctx, rfl⟩ := hl
      have hzl : (ns.zip ps).length = ns.length := by simp [hlen]
      have hfst : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map (fun p => p.2.2)
          = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip ps).map (fun r => r.2.term)
            = ((ns.zip ps).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = ps.map Sequent.term := by rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip (ps.map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTy.alloc (G := G) (Γ := Γ) (Ref := A)
        (parts := (ns.zip ps).map fun r => (r.1, r.2.type, r.2.term))
        (by rw [hfst]; exact hnd)
        (by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := (List.of_mem_zip (by simpa using hr)).2
          have h := hp r.2 hmem
          rw [hctx r.2 hmem] at h
          exact h)
        (by rw [htyp]; exact he)
      rw [hfst, hsnd] at this
      exact this
    · contradiction
  · rename_i ps _ _ _ ns inits
    split at hl
    · rename_i E he
      obtain ⟨hnd, hlen, hterms, hctx⟩ := hl
      have hfst : ((ns.zip ps).map fun r => (r.1, r.2.term)).map Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip ps).map fun r => (r.1, r.2.term)).map Prod.snd = inits := by
        rw [← hterms]
        calc
          ((ns.zip ps).map fun r => (r.1, r.2.term)).map Prod.snd
              = ((ns.zip ps).map Prod.snd).map Sequent.term := by
                simp [List.map_map, Function.comp_def]
          _ = ps.map Sequent.term := by rw [List.map_snd_zip (by omega)]
      have ht := HasTy.allocDict (G := G) (Γ := Γ) (Dict := A) (Elem := E)
        (parts := (ns.zip ps).map fun r => (r.1, r.2.term))
        (by rw [hfst]; exact hnd)
        (by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := (List.of_mem_zip (by simpa using hr)).2
          have h := hp r.2 hmem
          obtain ⟨hc, heq⟩ := hctx r.2 hmem
          rw [hc, heq] at h
          exact h)
        he
      rw [hfst, hsnd] at ht
      exact ht
    · contradiction
  · rename_i f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs os he
      exact .read ha he hr
    · contradiction
  · rename_i f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs os he
      exact .readView ha he hr
    · contradiction
  · rename_i A U f a ja
    rcases hl with ⟨hΓ, ht, hUnd, eq, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs os he
      subst eq
      exact .readOptional ha he hr hUnd
    · contradiction
  · rename_i A U f a ja
    rcases hl with ⟨hΓ, ht, hUnd, eq, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs vs ix os he
      subst eq
      exact .readDict ha he hr hUnd
    · contradiction
  · rename_i E U a key ja jk
    rcases hl with ⟨hΓa, hta, hΓk, htk, hStr, hUnd, eq, hr⟩
    have ha := hp ja (by simp)
    have hk := hp jk (by simp)
    rw [hΓa, hta] at ha
    rw [hΓk, htk] at hk
    split at hr
    · rename_i fs vs ix os he
      subst eq
      exact .indexDict ha he hk hStr hr hUnd
    · contradiction
  · rename_i f a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hn, hr⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    split at hr
    · rename_i fs vs os he
      exact .write ha he hr hb hn
    · contradiction
  · rename_i op a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hqa, hqb, hn⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    exact .arith ha hqa hb hqb hn
  · rename_i k a ja
    rcases hl with ⟨hΓ, hta, ht, hf⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .test ha ht hf
  · rename_i psl r x ps' inits
    split at hl
    · rename_i T hT
      obtain ⟨hterms, hctx, hreq, hbound, hpos⟩ := hl
      subst hterms
      have hmap : psl.map Sequent.term = (psl.map fun p => (p.type, p.term)).map Prod.snd := by
        simp [List.map_map, Function.comp_def]
      rw [hmap]
      refine HasTy.arrLit (xs := psl.map fun p => (p.type, p.term)) hT
        (by simpa using hreq) (by simpa using hbound) ?_ ?_
      · intro q hq
        rw [List.zipIdx_map] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact hpos p hp
      · intro p hmem
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        have := hp q hq
        rw [hctx q hq] at this
        exact this
    · contradiction
  · rename_i a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i T b hT hI
      simp only [requiredAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hA⟩ := hr
      exact .elem ha hT hi hI hk hA
    · contradiction
  · rename_i U a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hU, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i T b hT hI
      simp only [optionalAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hr⟩ := hr
      split at hr
      · cases hr
      · rename_i hnone
        simp only [Option.map_eq_some_iff] at hr
        obtain ⟨A, hA, rfl⟩ := hr
        exact .elemOpt ha hT hi hI hk hnone hA hU
    · contradiction
  · rename_i U a i ja ji
    rcases hl with ⟨hΓa, hta, hΓi, hti, hU, hq, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    split at hr
    · rename_i E hT
      rw [hr]
      exact .elemAny ha hT hi hq hU
    · contradiction
  · rename_i a i v ja ji jv
    rcases hl with ⟨hΓa, hta, hΓi, hti, hΓv, htv, hty, hr⟩
    have ha := hp ja (by simp)
    have hi := hp ji (by simp)
    have hv := hp jv (by simp)
    rw [hΓa, hta] at ha
    rw [hΓi, hti] at hi
    rw [hΓv, htv] at hv
    rw [hty]
    split at hr
    · rename_i T b hT hI
      obtain ⟨hr, hro⟩ := hr
      simp only [namedAt, Option.bind_eq_some_iff] at hr
      obtain ⟨k, hk, hA⟩ := hr
      exact .setElem ha hT hi hI hk hA hro hv
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ, hta, hn, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    split at hr
    · rename_i T hT
      exact .len ha hT hn
    · contradiction
  · rename_i c t e jc jt je
    rcases hl with ⟨hΓ, hc, hb, rfl, rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ, hc] at hcond
    exact .ifBool hcond hb (hp ⟨Γ,t,A⟩ (by simp)) (hp ⟨Γ,e,A⟩ (by simp))
  · rename_i q c t e jc jb
    rcases hl with ⟨hΓ,hc,hq,rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ,hc] at hcond
    exact .ifKnown hcond hq (hp ⟨Γ,(if q then t else e),A⟩ (by simp))
  · rename_i T F i t e jt je
    rcases hl with ⟨hb,hT,hF,rfl,rfl⟩
    split at hb
    · rename_i C hc
      exact .ifBoolVar hc hb hT hF (hp ⟨Γ.set i T,t,A⟩ (by simp)) (hp ⟨Γ.set i F,e,A⟩ (by simp))
    · contradiction
  · rename_i tag i u e ju
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (fun _ => hp ⟨Γ, u, A⟩ (by simp)) (by intro h; cases h)
    · contradiction
  · rename_i tag i u e je
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (by intro h; cases h) (fun _ => hp ⟨Γ, e, A⟩ (by simp))
    · contradiction
  · rename_i t ps i
    split at hl
    · rename_i C hi
      apply HasTy.unionVar hi
      intro a ha
      apply hp ⟨Γ.set i [a], _, A⟩
      rw [hl]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩
    · contradiction
  · rename_i ps _ _ _ arity b ns inits
    split at hl
    · rename_i P L hr
      obtain ⟨hnd,hlen,hterms,hctx,rfl,harity,hbodies⟩ := hl
      have hplen : (ps.take ns.length).length = ns.length := by
        have : ns.length ≤ ps.length := by
          have := congrArg List.length hterms
          simp only [List.length_map, List.length_take] at this
          omega
        simp only [List.length_take]
        omega
      have hfst : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => p.2.2) = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip (ps.take ns.length)).map (fun r => r.2.term)
            = ((ns.zip (ps.take ns.length)).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = (ps.take ns.length).map Sequent.term := by
              rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip ((ps.take ns.length).map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTy.makeCallable (G := G) (Γ := Γ) (F := A) (arity := arity) (b := b) (L := L)
        (parts := (ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term))
        (by rw [htyp]; exact hr)
        (by rw [hfst]; exact hnd)
        (by
          intro q hq
          obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := List.mem_of_mem_take (List.of_mem_zip (by simpa using hr')).2
          have h := hp r.2 hmem
          rw [hctx r.2 (List.of_mem_zip (by simpa using hr')).2] at h
          exact h)
        harity
        (by
          intro q hq
          apply hp ⟨q.1 :: q.2.1 ++ Γ, b, q.2.2⟩
          have : (⟨q.1 :: q.2.1 ++ Γ, b, q.2.2⟩ : Sequent ι) ∈ ps.drop ns.length := by
            rw [hbodies]
            exact List.mem_map.mpr ⟨q, hq, rfl⟩
          exact List.mem_of_mem_drop this)
      rw [hfst, hsnd] at this
      exact this
    · contradiction
  · rename_i f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    split at hL
    · rename_i P Ps L he
      -- The actual premises and the omitted-position premises are the same list,
      -- split at the number of actuals the call writes.
      have ha : ∀ p ∈ (jas.take args.length).map (fun ja => (ja.type,ja.term)),
          HasTy G Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hcontexts ja (List.mem_of_mem_take hja)] at h
        exact h
      have hu : ∀ A ∈ (jas.drop args.length).map Sequent.type, HasTy G Γ .undef A := by
        intro A hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop hja)))
        rw [hcontexts ja (List.mem_of_mem_drop hja), hundef ja hja] at h
        exact h
      have hsplit : ((jas.take args.length).map (fun ja => (ja.type,ja.term))).map Prod.fst
          ++ (jas.drop args.length).map Sequent.type = jas.map Sequent.type := by
        simp only [List.map_map, Function.comp_def]
        rw [← List.map_append, List.take_append_drop]
      have h := HasTy.callCallable hf he (xs := (jas.take args.length).map (fun ja => (ja.type,ja.term)))
        (Us := (jas.drop args.length).map Sequent.type)
        (by rw [hsplit]; exact hL) hrt ha hu
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ,ht,hL⟩
    have ha := hp ja (by simp)
    rw [hΓ,ht] at ha
    split at hL
    · rename_i P Ps L he
      exact .readCallable ha he hL
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓa,hta,hΓb,htb,hn,hL⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa,hta] at ha
    rw [hΓb,htb] at hb
    split at hL
    · rename_i P Ps L he
      exact .writeCallable ha he hL hb hn
    · contradiction
  · rename_i ps As n b ns inits
    obtain ⟨rfl, rfl, hl⟩ := hl
    split at hl
    · rename_i L hL
      obtain ⟨hlen, hsig, rfl⟩ := hl
      exact HasTy.funRest hL hlen hsig (fun p hm => hp _ (List.mem_map.mpr ⟨p, hm, rfl⟩))
    · contradiction
  · rename_i ps _ _ _ As n b ns inits
    split at hl
    · rename_i P L hr
      obtain ⟨hnd,hlen,hterms,hctx,rfl,hlenA,hsig,hbodies⟩ := hl
      have hplen : (ps.take ns.length).length = ns.length := by
        have : ns.length ≤ ps.length := by
          have := congrArg List.length hterms
          simp only [List.length_map, List.length_take] at this
          omega
        simp only [List.length_take]
        omega
      have hfst : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => p.2.2) = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip (ps.take ns.length)).map (fun r => r.2.term)
            = ((ns.zip (ps.take ns.length)).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = (ps.take ns.length).map Sequent.term := by
              rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip ((ps.take ns.length).map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTy.makeCallableRest (G := G) (Γ := Γ) (F := A) (n := n) (b := b) (L := L)
        (As := As) (parts := (ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term))
        (by rw [htyp]; exact hr)
        (by rw [hfst]; exact hnd)
        (by
          intro q hq
          obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := List.mem_of_mem_take (List.of_mem_zip (by simpa using hr')).2
          have h := hp r.2 hmem
          rw [hctx r.2 (List.of_mem_zip (by simpa using hr')).2] at h
          exact h)
        hlenA hsig
        (by
          intro q hq
          apply hp ⟨q.2 :: q.1.1 :: q.1.2.1 ++ Γ, b, q.1.2.2.2⟩
          have : (⟨q.2 :: q.1.1 :: q.1.2.1 ++ Γ, b, q.1.2.2.2⟩ : Sequent ι) ∈ ps.drop ns.length := by
            rw [hbodies]
            exact List.mem_map.mpr ⟨q, hq, rfl⟩
          exact List.mem_of_mem_drop this)
      rw [hfst, hsnd] at this
      exact this
    · contradiction
  · rename_i E s js
    rcases hl with ⟨hΓ, ht, hsp, hr⟩
    have h := hp js (by simp)
    rw [hΓ, ht] at h
    exact .arrCopy h hsp hr
  · rename_i k u flags P f r args jf jr jas
    rcases hl with ⟨hΓf, htf, hΓr, htr, hctx, hlen, hshort, rfl, hundef, hparts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    have hrt := hp jr (by simp)
    rw [hΓr, htr] at hrt
    have htake : jas.take (k + u) = jas.take k ++ (jas.drop k).take u := List.take_add ..
    have := HasTy.callRest (xs := (jas.take k).map fun ja => (ja.type, ja.term))
      (Us := ((jas.drop k).take u).map Sequent.type) (P := P)
      (parts := (flags.zip (jas.drop (k + u))).map fun q => (q.1, q.2.type, q.2.term)) hf
      (by rw [htake] at hL; simpa [List.map_append, List.map_map, Function.comp_def] using hL) hrt
      (by
        intro p hm
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hja)))
        rw [hctx ja (List.mem_of_mem_take hja)] at h
        exact h)
      (by
        intro A hA
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hA
        have hmem : ja ∈ jas := List.mem_of_mem_drop (List.mem_of_mem_take hja)
        have h := hp ja (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem))
        rw [hctx ja hmem, hundef ja hja] at h
        exact h)
      (by rcases hshort with h | h <;> simp [h])
      (by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        have hja := List.mem_of_mem_drop (List.of_mem_zip hq).2
        have h := hp q.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hja))
        rw [hctx q.2 hja] at h
        exact h)
      (by simpa [List.map_map, Function.comp_def] using hparts)
    simpa [List.map_map, Function.comp_def] using this
  · obtain ⟨rfl, rfl, hl⟩ := hl
    split at hl
    · rename_i hsaved hT hRt hF
      obtain ⟨hmap, hsig⟩ := hl
      rw [varSlots_eq hsaved]
      exact HasTy.bindE hT hsig hRt hmap hF
    · contradiction
  · obtain ⟨rfl, rfl, hl⟩ := hl
    split at hl
    · rename_i hsaved hT hRt hF
      obtain ⟨hmap, ⟨Rt', Ps, E', R'⟩, hmem, h1, h2, h3, h4, El, hEl, h5⟩ := hl
      simp only at h1 h2 h3 h4 h5
      subst h1 h2 h3 h4
      rw [varSlots_eq hsaved]
      exact HasTy.bindRestE hT hmem (by simpa using hEl) hRt hmap h5 hF
    · contradiction
  · rename_i ps U arity b ns inits
    obtain ⟨rfl, rfl, hU, hl⟩ := hl
    unfold ctorEPremises at hl
    split at hl
    · rename_i L hL
      apply HasTy.ctorE hL hU hl.1
      intro p hmem
      apply hp ⟨U :: p.1 ++ Γ, b, p.2⟩
      rw [hl.2]
      exact List.mem_map.mpr ⟨p, hmem, rfl⟩
    · contradiction
  · rename_i f args jf jas
    rcases hl with ⟨hΓf, htf, hterms, hctx, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    split at hL
    · rename_i L he
      have hxs : ∀ p ∈ jas.map (fun ja => (ja.type, ja.term)), HasTy G Γ p.2 p.1 := by
        intro p hp'
        obtain ⟨ja, hja, rfl⟩ := List.mem_map.mp hp'
        have h := hp ja (by simp [hja])
        rw [hctx ja hja] at h
        exact h
      have hc := HasTy.construct (xs := jas.map fun ja => (ja.type, ja.term)) hf he
        (by simpa [List.map_map, Function.comp_def] using hL) hxs
      rw [← hterms]
      simpa [List.map_map, Function.comp_def] using hc
    · contradiction
  · rename_i proof t jt
    rcases hl with ⟨hΓ, ht, hc⟩
    have hj := hp jt (by simp)
    rw [hΓ, ht] at hj
    exact .sub hj hc

theorem checkTree_sound [DecidableEq ι] {G : NormalGraph ι} (e : Evidence ι)
    (he : checkTree G e = true) : HasTy G (claim e).context (claim e).term (claim e).type := by
  cases e with
  | node j r ps =>
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
    apply local_sound he.1
    intro p hp
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hp
    exact checkTree_sound e (he.2 ⟨e, he'⟩ (by simp))
termination_by sizeOf e

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {t A e}
    (he : check G t A e = true) : Scoped 0 t ∧ HasTy G [] t A := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
  refine ⟨(checkScope_iff 0 t).mp he.1.2, ?_⟩
  have ht := checkTree_sound e he.2
  simpa only [he.1.1] using ht

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {t A e}
    (he : check G t A e = true) (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G A) n W h t :=
  (check_sound he).2.closed_safe (check_sound he).1 n W h hw hh

def Representable [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) : Prop :=
  ∃ e, claim e = j ∧ checkTree G e = true

private theorem gather [DecidableEq ι] {G : NormalGraph ι} (js : List (Sequent ι))
    (h : ∀ j ∈ js, Representable G j) :
    ∃ es : List (Evidence ι), es.map claim = js ∧ ∀ e ∈ es, checkTree G e = true := by
  induction js with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons j js ih =>
    obtain ⟨e, he, hc⟩ := h j (by simp)
    obtain ⟨es, hes, hcs⟩ := ih (fun k hk => h k (by simp [hk]))
    refine ⟨e :: es, by simp [he, hes], ?_⟩
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | hm
    · exact hc
    · exact hcs e' hm

private theorem node_complete [DecidableEq ι] {G : NormalGraph ι} {j r js}
    (hl : Local G j r js) (h : ∀ p ∈ js, Representable G p) : Representable G j := by
  obtain ⟨es, hes, hcs⟩ := gather js h
  refine ⟨.node j r es, rfl, ?_⟩
  simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨by simpa only [hes] using hl, fun e _ => hcs e.val e.property⟩

/-- Every declarative derivation has finite accepted evidence. This is coverage
of the rules, not semantic completeness and not a proof-search algorithm. -/
theorem checkTree_complete [DecidableEq ι] {G : NormalGraph ι} {Γ t A}
    (ht : HasTy G Γ t A) : Representable G ⟨Γ, t, A⟩ := by
  induction ht with
  | var hi => exact node_complete (r := .var) (js := []) hi (by simp)
  | nul hr => exact node_complete (r := .nul) (js := []) hr (by simp)
  | undef hr => exact node_complete (r := .undef) (js := []) hr (by simp)
  | tru hr => exact node_complete (r := .tru) (js := []) hr (by simp)
  | fls hr => exact node_complete (r := .fls) (js := []) hr (by simp)
  | truLit hr => exact node_complete (r := .truLit) (js := []) hr (by simp)
  | flsLit hr => exact node_complete (r := .flsLit) (js := []) hr (by simp)
  | numLit hr => exact node_complete (r := .numLit) (js := []) hr (by simp)
  | num hr => exact node_complete (r := .num) (js := []) hr (by simp)
  | strLit hr => exact node_complete (r := .strLit) (js := []) hr (by simp)
  | str hr => exact node_complete (r := .str) (js := []) hr (by simp)
  | @funE Γ F L arity b hr hlen hb ih =>
    apply node_complete (r := .funE) (js := L.map (fun p => ⟨p.1 :: p.2.1 ++ Γ, b, p.2.2⟩))
    · refine ⟨rfl, rfl, ?_⟩
      show funEPremises G Γ F arity b _
      simpa only [funEPremises, show expand G F = [.arrs L []] from hr, and_true] using hlen
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @makeCallable Γ F L arity b parts hr hnd hpart hlen hb ih ihb =>
    apply node_complete (r := .makeCallable)
      (j := ⟨Γ, .makeAt (.closure arity b) (parts.map Prod.fst) (parts.map fun p => p.2.2), F⟩)
      (js := (parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩) ++
        L.map (fun p => ⟨p.1 :: p.2.1 ++ Γ,b,p.2.2⟩))
    · simp only [Local,
        show expand G F = [.callable (parts.map fun p => (p.1, p.2.1)) [] L []] from hr]
      have hlenp : (parts.map fun p => (⟨Γ, p.2.2, p.2.1⟩ : Sequent ι)).length
          = (parts.map Prod.fst).length := by simp
      refine ⟨hnd, by simp, ?_, ?_, ?_, hlen, ?_⟩
      · rw [List.take_left' hlenp]
        simp [List.map_map, Function.comp_def]
      · rw [List.take_left' hlenp]
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        rfl
      · rw [List.take_left' hlenp]
        simp only [List.map_map, Function.comp_def]
        rw [List.zip_map']
      · rw [List.drop_left' hlenp]
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact ih p hp
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact ihb p hp
  | @makeCallableRest Γ F parts L As n b hr hnd hpart hlen hsig hb ih ihb =>
    apply node_complete (r := .makeCallableRest As)
      (j := ⟨Γ, .makeAt (.variadic n b) (parts.map Prod.fst) (parts.map fun p => p.2.2), F⟩)
      (js := (parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩) ++
        (L.zip As).map (fun p => ⟨p.2 :: p.1.1 :: p.1.2.1 ++ Γ,b,p.1.2.2.2⟩))
    · simp only [Local,
        show expand G F = [.callable (parts.map fun p => (p.1, p.2.1)) [] [] L] from hr]
      have hlenp : (parts.map fun p => (⟨Γ, p.2.2, p.2.1⟩ : Sequent ι)).length
          = (parts.map Prod.fst).length := by simp
      refine ⟨hnd, by simp, ?_, ?_, ?_, hlen, hsig, ?_⟩
      · rw [List.take_left' hlenp]
        simp [List.map_map, Function.comp_def]
      · rw [List.take_left' hlenp]
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        rfl
      · rw [List.take_left' hlenp]
        simp only [List.map_map, Function.comp_def]
        rw [List.zip_map']
      · rw [List.drop_left' hlenp]
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact ih p hp
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact ihb p hp
  | @callCallable Γ f r F Rt B P Ps L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    apply node_complete (r := .callCallable)
      (js := ⟨Γ,f,F⟩ :: ⟨Γ,r,Rt⟩ :: (xs.map (fun p => ⟨Γ,p.2,p.1⟩) ++ Us.map (fun A => ⟨Γ,.undef,A⟩)))
    · have hlenx : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))).length
          = (xs.map Prod.snd).length := by simp
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
      · rw [List.take_left' hlenx]
        simp only [List.map_map,Function.comp_def]
      · rw [List.drop_left' hlenx]
        intro ja hj
        obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
        rfl
      · intro ja hj
        rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          rfl
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          rfl
      · have heq : ((xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))
            ++ Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).map Sequent.type)
            = xs.map Prod.fst ++ Us := by
          rw [List.map_append, List.map_map, List.map_map]
          simp [Function.comp_def]
        rw [show expand G F = [.callable P Ps L S] from hr, heq]
        exact hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihrt
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          exact iha p hp
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          exact ihu A hA
  | @readCallable Γ a F P Ps L S f A ha hr hm ih =>
    apply node_complete (G := G) (j := ⟨Γ,.readAt f a,A⟩) (r := .readCallable) (js := [⟨Γ,a,F⟩])
    · simpa [Local,show expand G F = [.callable P Ps L S] from hr] using hm
    · simpa using ih
  | @writeCallable Γ a F P Ps L S f A b N ha hr hm hb hn iha ihb =>
    apply node_complete (G := G) (j := ⟨Γ,.writeAt f a b,N⟩) (r := .writeCallable)
      (js := [⟨Γ,a,F⟩,⟨Γ,b,A⟩])
    · exact ⟨rfl,rfl,rfl,rfl,hn,by
        simp only [show expand G F = [.callable P Ps L S] from hr]
        exact hm⟩
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl
      · exact iha
      · exact ihb
  | @ctorE Γ F U L arity b hr hu hlen hb ih =>
    apply node_complete (r := .ctorE U) (js := L.map (fun p => ⟨U :: p.1 ++ Γ, b, p.2⟩))
    · refine ⟨rfl, rfl, hu, ?_⟩
      show ctorEPremises G Γ F U arity b _
      simpa only [ctorEPremises, show expand G F = [.ctors L] from hr, and_true] using hlen
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @construct Γ f F B L xs hf hr hp hx ihf ihx =>
    apply node_complete (r := .construct)
      (js := ⟨Γ,f,F⟩ :: xs.map (fun p => ⟨Γ,p.2,p.1⟩))
    · refine ⟨rfl, rfl, by simp [List.map_map, Function.comp_def], ?_, ?_⟩
      · intro ja hj
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
        rfl
      · simp only [show expand G F = [.ctors L] from hr]
        simpa [List.map_map, Function.comp_def] using hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
        exact ihx p hp
  | @app Γ f r F Rt B L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    apply node_complete (r := .app)
      (js := ⟨Γ,f,F⟩ :: ⟨Γ,r,Rt⟩ :: (xs.map (fun p => ⟨Γ,p.2,p.1⟩) ++ Us.map (fun A => ⟨Γ,.undef,A⟩)))
    · have hlenx : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))).length
          = (xs.map Prod.snd).length := by simp
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
      · rw [List.take_left' hlenx]
        simp only [List.map_map,Function.comp_def]
      · rw [List.drop_left' hlenx]
        intro ja hj
        obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
        rfl
      · intro ja hj
        rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          rfl
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          rfl
      · have heq : ((xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))
            ++ Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).map Sequent.type)
            = xs.map Prod.fst ++ Us := by
          rw [List.map_append, List.map_map, List.map_map]
          simp [Function.comp_def]
        rw [show expand G F = [.arrs L S] from hr, heq]
        exact hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihrt
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
          exact iha p hp
        · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hj
          exact ihu A hA
  | @letE Γ a A b B ha hb iha ihb =>
    apply node_complete (r := .letE) (js := [⟨Γ,a,A⟩, ⟨A::Γ,b,B⟩])
    · exact ⟨rfl, rfl, rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact iha
      · exact ihb
  | @alloc Γ Ref parts hnd hpart hr ih =>
    apply node_complete (G := G)
      (j := ⟨Γ, .makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2), Ref⟩)
      (r := .alloc) (js := parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩)
    · simp only [Local, show expand G Ref = [.refs (parts.map fun p => (p.1, p.2.1)) [] []] from hr]
      refine ⟨hnd, by simp, by simp [List.map_map, Function.comp_def], by
        intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; rfl, ?_⟩
      simp only [List.map_map, Function.comp_def]
      rw [List.zip_map']
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @allocDict Γ Elem Dict parts hnd hpart hr ih =>
    apply node_complete (G := G)
      (j := ⟨Γ, .makeAt .absent (parts.map Prod.fst) (parts.map Prod.snd), Dict⟩)
      (r := .allocDict) (js := parts.map fun p => ⟨Γ, p.2, Elem⟩)
    · simp only [Local, show expand G Dict = [.dict [] [] [] [Elem]] from hr]
      refine ⟨hnd, by simp, by simp [List.map_map, Function.comp_def], ?_⟩
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact ⟨rfl, rfl⟩
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @read Γ a Ref fs vs os f A ha hr hm ih =>
    apply node_complete (G := G) (j := ⟨Γ, .readAt f a, A⟩) (r := .read) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,by simp only [show expand G Ref = [.refs fs [] vs os] from hr]; exact hm⟩
    simpa using ih
  | @readView Γ a Ref fs vs os f A ha hr hm ih =>
    apply node_complete (G := G) (j := ⟨Γ, .readAt f a, A⟩) (r := .readView) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,by simp only [show expand G Ref = [.refs fs [] vs os] from hr]; exact hm⟩
    simpa using ih
  | @readOptional Γ a Ref fs vs os f A U ha hr hm hUnd ih =>
    apply node_complete (G := G) (j := ⟨Γ, .readAt f a, A ++ U⟩)
      (r := .readOptional A U) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,hUnd,rfl,by simp only [show expand G Ref = [.refs fs [] vs os] from hr]; exact hm⟩
    simpa using ih
  | @readDict Γ a Ref fs vs ix os A U f ha hr hm hUnd ih =>
    apply node_complete (G := G) (j := ⟨Γ, .readAt f a, A ++ U⟩)
      (r := .readDict A U) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,hUnd,rfl,by simp only [show expand G Ref = [.dict fs [] vs ix os] from hr]; exact hm⟩
    simpa using ih
  | @indexDict Γ a Ref fs vs ix os key K A U ha hr hk hStr hm hUnd iha ihk =>
    apply node_complete (G := G) (j := ⟨Γ, .indexAt a key, A ++ U⟩)
      (r := .indexDict A U) (js := [⟨Γ,a,Ref⟩, ⟨Γ,key,K⟩])
      ⟨rfl,rfl,rfl,rfl,hStr,hUnd,rfl,
        by simp only [show expand G Ref = [.dict fs [] vs ix os] from hr]; exact hm⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact iha
    · exact ihk
  | @arrLit Γ L T xs hr hreq hbound hpos hx ih =>
    apply node_complete (G := G) (j := ⟨Γ, .arrLit (xs.map Prod.snd), L⟩) (r := .arrLit)
      (js := xs.map fun p => ⟨Γ, p.2, p.1⟩)
    · simp only [Local, show expand G L = [.list T []] from hr]
      refine ⟨by simp [List.map_map, Function.comp_def],
        by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; rfl,
        by simpa using hreq, by simpa using hbound, ?_⟩
      intro q hq
      rw [List.zipIdx_map] at hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact hpos p hp
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @elem Γ a i L I A T b k ha hr hi hI hk hA iha ihi =>
    apply node_complete (G := G) (j := ⟨Γ, .elemAt a i, A⟩) (r := .elem) (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩])
      ⟨rfl,rfl,rfl,rfl,by simp only [show expand G L = [.list T []] from hr,
        show expand G I = [.numLit b] from hI]; simp [requiredAt, hk, hA]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihi
  | @elemOpt Γ a i L I A U T b k ha hr hi hI hk hnone hA hU iha ihi =>
    apply node_complete (G := G) (j := ⟨Γ, .elemAt a i, A ++ U⟩) (r := .elemOpt U)
      (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩])
      ⟨rfl,rfl,rfl,rfl,hU,by simp only [show expand G L = [.list T []] from hr,
        show expand G I = [.numLit b] from hI]; simp [optionalAt, hk, hnone, hA]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihi
  | @elemAny Γ a i L I E U ha hr hi hq hU iha ihi =>
    apply node_complete (G := G) (j := ⟨Γ, .elemAt a i, E ++ U⟩) (r := .elemAny U)
      (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩])
      ⟨rfl,rfl,rfl,rfl,hU,hq,by simp only [show expand G L = [.list ⟨[], [], some E, false⟩ []] from hr]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihi
  | @setElem Γ a i v L I A T b k ha hr hi hI hk hA hro hv iha ihi ihv =>
    apply node_complete (G := G) (j := ⟨Γ, .setElem a i v, L⟩) (r := .setElem)
      (js := [⟨Γ,a,L⟩, ⟨Γ,i,I⟩, ⟨Γ,v,A⟩])
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,by simp only [show expand G L = [.list T []] from hr,
        show expand G I = [.numLit b] from hI]; simp [namedAt, hk, hA, hro]⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact iha
    · exact ihi
    · exact ihv
  | @len Γ a L N T ha hr hn ih =>
    apply node_complete (G := G) (j := ⟨Γ, .lenOf a, N⟩) (r := .len) (js := [⟨Γ,a,L⟩])
      ⟨rfl,rfl,hn,by simp only [show expand G L = [.list T []] from hr]⟩
    simpa using ih
  | @test Γ a A B k ha ht hf ih =>
    apply node_complete (G := G) (j := ⟨Γ, .test k a, B⟩) (r := .test) (js := [⟨Γ,a,A⟩])
      ⟨rfl,rfl,ht,hf⟩
    simpa using ih
  | @arith Γ a A b B N op ha hqa hb hqb hn iha ihb =>
    apply node_complete (G := G) (j := ⟨Γ, .arith op a b, N⟩) (r := .arith)
      (js := [⟨Γ,a,A⟩, ⟨Γ,b,B⟩]) ⟨rfl,rfl,rfl,rfl,hqa,hqb,hn⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb
  | @write Γ a Ref fs vs os f A b N ha hr hm hb hn iha ihb =>
    apply node_complete (G := G) (j := ⟨Γ, .writeAt f a b, N⟩) (r := .write)
      (js := [⟨Γ,a,Ref⟩, ⟨Γ,b,A⟩])
      ⟨rfl,rfl,rfl,rfl,hn,by simp only [show expand G Ref = [.refs fs [] vs os] from hr]; exact hm⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb
  | @ifBool Γ c C t A e hc hb ht he ihc iht ihe =>
    apply node_complete (r := .ifBool) (js := [⟨Γ,c,C⟩,⟨Γ,t,A⟩,⟨Γ,e,A⟩])
    · exact ⟨rfl,rfl,hb,rfl,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact ihc
      · exact iht
      · exact ihe
  | @ifKnown Γ c C q t e A hc hq ht ihc iht =>
    apply node_complete (r := .ifKnown q) (js := [⟨Γ,c,C⟩,⟨Γ,(if q then t else e),A⟩])
    · exact ⟨rfl,rfl,hq,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact ihc
      · exact iht
  | @ifBoolVar Γ i C T F t A e hi hb hT hF ht he iht ihe =>
    apply node_complete (r := .ifBoolVar T F) (js := [⟨Γ.set i T,t,A⟩,⟨Γ.set i F,e,A⟩])
    · exact ⟨by simpa only [Local, hi] using hb,hT,hF,rfl,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact iht
      · exact ihe
  | @ifTag Γ i A tag q u B e hi hq ht he iht ihe =>
    cases q with
    | true =>
      apply node_complete (r := .ifTrue) (js := [⟨Γ,u,B⟩])
      · simpa only [Local, hi, true_and] using hq
      · simpa using iht rfl
    | false =>
      apply node_complete (r := .ifFalse) (js := [⟨Γ,e,B⟩])
      · simpa only [Local, hi, true_and] using hq
      · simpa using ihe rfl
  | @unionVar Γ i C t A hi ht ih =>
    apply node_complete (r := .unionVar i)
      (js := C.map (fun a => ⟨Γ.set i [a], t, A⟩))
    · simp [Local,hi]
    · intro j hj
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hj
      exact ih a ha
  | @funRest Γ F L As k b hr hlen hsig hb ih =>
    apply node_complete (r := .funRest As)
      (js := (L.zip As).map fun p => ⟨p.2 :: p.1.1 :: p.1.2.1 ++ Γ, b, p.1.2.2.2⟩)
    · refine ⟨rfl, rfl, ?_⟩
      simp only [show expand G F = [.arrs [] L] from hr]
      exact ⟨hlen, hsig, trivial⟩
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @arrCopy Γ s S T E hs hsp hr ih =>
    apply node_complete (G := G) (j := ⟨Γ, .arrLit [.spread s], T⟩) (r := .arrCopy E)
      (js := [⟨Γ, s, S⟩]) ⟨rfl, rfl, hsp, hr⟩
    simpa using ih
  | @callRest Γ f r F Rt xs Us P B parts hf hmem hrt hx hu hshort hp hparts
      ihf ihrt ihx ihu ihp =>
    apply node_complete (r := .callRest xs.length Us.length (parts.map Prod.fst) P)
      (js := ⟨Γ,f,F⟩ :: ⟨Γ,r,Rt⟩ :: (xs.map (fun p => ⟨Γ,p.2,p.1⟩) ++ Us.map (fun A => ⟨Γ,.undef,A⟩) ++
        parts.map (fun p => ⟨Γ,p.2.2,p.2.1⟩)))
    · have hlenx : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι))).length = xs.length := by simp
      have hlenu : (Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).length = Us.length := by simp
      have hlenxu : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι))).length = xs.length + Us.length := by simp
      have hzip : (parts.map Prod.fst).zip (parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι)))
          = parts.map (fun p => (p.1, (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))) := List.zip_map'
      have htk : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).take xs.length =
          xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) := by
        rw [List.append_assoc, List.take_left' hlenx]
      have hdk : ((xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).drop xs.length).take Us.length =
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) := by
        rw [List.append_assoc, List.drop_left' hlenx, List.take_left' hlenu]
      have hdku : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).drop (xs.length + Us.length) =
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι)) := List.drop_left' hlenxu
      have htku : (xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
          Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) ++
          parts.map (fun p => (⟨Γ,p.2.2,p.2.1⟩ : Sequent ι))).take (xs.length + Us.length) =
          xs.map (fun p => (⟨Γ,p.2,p.1⟩ : Sequent ι)) ++
            Us.map (fun A => (⟨Γ,.undef,A⟩ : Sequent ι)) := List.take_left' hlenxu
      refine ⟨rfl, rfl, rfl, rfl, ?_, by simp; omega, by rcases hshort with h | h <;> simp [h],
        ?_, ?_, ?_, ?_⟩
      · intro ja hj
        simp only [List.mem_append, List.mem_map] at hj
        rcases hj with (⟨p,_,rfl⟩ | ⟨A,_,rfl⟩) | ⟨p,_,rfl⟩ <;> rfl
      · rw [htk, hdku, hzip]
        simp [List.map_map, Function.comp_def]
      · rw [hdk]
        intro ja hj
        obtain ⟨A,_,rfl⟩ := List.mem_map.mp hj; rfl
      · rw [hdku, hzip]
        simpa [List.map_map, Function.comp_def] using hparts
      · rw [htku]
        simpa [List.map_map, List.map_append, Function.comp_def] using hmem
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihrt
      · simp only [List.mem_append, List.mem_map] at hj
        rcases hj with (⟨p,hp',rfl⟩ | ⟨A,hA,rfl⟩) | ⟨p,hp',rfl⟩
        · exact ihx p hp'
        · exact ihu A hA
        · exact ihp p hp'
  | @bindE Γ F T Rt R Rc t r saved Ps Ds ht hsig hr hmap hF =>
    apply node_complete (r := .bindE) (js := [])
    · refine ⟨rfl, rfl, ?_⟩
      show (match varSlots (saved.map Tm.var), Γ[t]?, Γ[r]?, expand G F with
        | some saved, some T, some Rt, [.arrs [(_, Ds, R)] []] =>
          saved.map (Γ[·]?) = (saved.filterMap (Γ[·]?)).map some ∧
          (Rt, saved.filterMap (Γ[·]?) ++ Ds, R) ∈ callSigs G T
        | _, _, _, _ => False)
      rw [varSlots_map, ht, hr, show expand G F = [.arrs [(Rc, Ds, R)] []] from hF]
      simp only
      rw [filterMap_of_map hmap]
      exact ⟨hmap, hsig⟩
    · simp
  | @bindRestE Γ F T Rt E El R Rc t r saved Ps Qs ht hsig hel hr hmap hQs hF =>
    apply node_complete (r := .bindRestE) (js := [])
    · refine ⟨rfl, rfl, ?_⟩
      show (match varSlots (saved.map Tm.var), Γ[t]?, Γ[r]?, expand G F with
        | some saved, some T, some Rt, [.arrs [] [(_, Ds, E', R)]] =>
          saved.map (Γ[·]?) = (saved.filterMap (Γ[·]?)).map some ∧
          ∃ s ∈ restSigs G T, s.1 = Rt ∧ s.2.2.1 = E' ∧ s.2.2.2 = R ∧
            Ds = s.2.1.drop saved.length ∧ ∃ El ∈ (restElem G E').toList,
            saved.filterMap (Γ[·]?) =
              s.2.1.take saved.length ++ List.replicate (saved.length - s.2.1.length) El
        | _, _, _, _ => False)
      rw [varSlots_map, ht, hr, show expand G F = [.arrs [] [(Rc, Ps.drop saved.length, E, R)]] from hF]
      simp only
      rw [filterMap_of_map hmap]
      exact ⟨hmap, ⟨Rt, Ps, E, R⟩, hsig, rfl, rfl, rfl, rfl, El, by simp [hel], hQs⟩
    · simp
  | @sub Γ t A B cert ht hc ih =>
    apply node_complete (G := G) (j := ⟨Γ, t, B⟩) (r := .sub cert) (js := [⟨Γ,t,A⟩]) ⟨rfl,rfl,hc⟩
    simpa using ih

theorem derivable_iff_checked [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) :
    (Scoped 0 t ∧ HasTy G [] t A) ↔ ∃ e, check G t A e = true := by
  constructor
  · rintro ⟨hs, ht⟩
    obtain ⟨e, he, hc⟩ := checkTree_complete ht
    exact ⟨e, by simp [check, he, (checkScope_iff 0 t).mpr hs, hc]⟩
  · rintro ⟨e, he⟩; exact check_sound he

#print axioms checkTree_sound
#print axioms derivable_iff_checked
#print axioms accepted_safe
end Verification.Model.ProgramCertificates
