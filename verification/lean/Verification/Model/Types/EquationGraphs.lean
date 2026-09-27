import Verification.Model.Types.GraphRows

/-! A finite presentation of an application-indexed graph. An application
retains its arguments, and a local parameter is identified by its owning
application and slot. Unfolding a row does not unfold the rows it references.
This module supplies graphs to the existing semantics, not another semantics.
-/
namespace Verification.Model.EquationGraphs
open PositiveGraphs PositiveNormalization CallEffects

structure Binder where
  name : String
  kind : ParameterKind
  deriving Repr, DecidableEq

/-- The finite signature fixes both application arity and local binder kinds.
Binder names are only diagnostic metadata. -/
structure Header where
  parameters : Nat
  binders : List Binder
  deriving Repr, DecidableEq

abbrev Signature := List Header

-- Explicit mutually recursive spines let Lean derive executable equality.
-- They represent ordinary lists, not additional type-language constructs.
mutual
inductive Tree where
  | app (head : Nat) (args : Args)
  | bound (head : Nat) (args : Args) (slot : Nat)
  | argument (slot : Nat)
  | local (slot : Nat)
  deriving Repr, DecidableEq
inductive Types where
  | nil
  | cons (head : Tree) (tail : Types)
  deriving Repr, DecidableEq
inductive Args where
  | nil
  | cons (head : Types) (tail : Args)
  deriving Repr, DecidableEq
end

def Types.toList : Types → List Tree
  | .nil => []
  | .cons t ts => t :: ts.toList

def Args.toList : Args → List Types
  | .nil => []
  | .cons t ts => t :: ts.toList

def Types.ofList : List Tree → Types
  | [] => .nil
  | t :: ts => .cons t (ofList ts)

def Args.ofList : List Types → Args
  | [] => .nil
  | t :: ts => .cons t (ofList ts)

@[simp] theorem Types.toList_ofList (ts : List Tree) : (ofList ts).toList = ts := by
  induction ts <;> simp_all [ofList, toList]

@[simp] theorem Args.toList_ofList (ts : List Types) : (ofList ts).toList = ts := by
  induction ts <;> simp_all [ofList, toList]

private def arityOk (sig : Signature) (head : Nat) (args : Args) : Bool :=
  sig[head]?.any fun h => args.toList.length == h.parameters

private def binderOk (sig : Signature) (head slot : Nat) : Bool :=
  sig[head]?.any fun h => slot < h.binders.length

/- Scope checks apply at every nested application. Closed labels have no
argument or local placeholders: only a well-scoped equation may contain them. -/
mutual
def Tree.scoped (sig : Signature) (parameters locals : Nat) : Tree → Bool
  | .app h args => arityOk sig h args && args.scoped sig parameters locals
  | .bound h args i => arityOk sig h args && binderOk sig h i && args.scoped sig parameters locals
  | .argument i => i < parameters
  | .local i => i < locals
def Types.scoped (sig : Signature) (parameters locals : Nat) : Types → Bool
  | .nil => true
  | .cons t ts => t.scoped sig parameters locals && ts.scoped sig parameters locals
def Args.scoped (sig : Signature) (parameters locals : Nat) : Args → Bool
  | .nil => true
  | .cons t ts => t.scoped sig parameters locals && ts.scoped sig parameters locals
end

/- Templates capture parameter references through their argument environment.
They cannot manufacture a parameter belonging to some other application. -/
mutual
def Tree.lexical (locals : Bool) : Tree → Bool
  | .app _ args => args.lexical locals
  | .bound .. => false
  | .argument _ => true
  | .local _ => locals
def Types.lexical (locals : Bool) : Types → Bool
  | .nil => true
  | .cons t ts => t.lexical locals && ts.lexical locals
def Args.lexical (locals : Bool) : Args → Bool
  | .nil => true
  | .cons t ts => t.lexical locals && ts.lexical locals
end

abbrev Label (sig : Signature) := { t : Tree // t.scoped sig 0 0 = true }
abbrev Expression (sig : Signature) (h : Header) :=
  { t : Tree // t.scoped sig h.parameters h.binders.length = true ∧ t.lexical true = true }

/-- Unlike a type operand, a binding position cannot name a parameter's union. -/
def Tree.single : Tree → Bool
  | .argument _ => false
  | .app .. | .bound .. | .local .. => true

abbrev Reference (sig : Signature) (h : Header) :=
  { e : Expression sig h // e.1.single = true }

/-- Arguments are already closed labels, and arity is a construction premise.
The same scope creates both its application label and its bound parameters. -/
structure Scope (sig : Signature) where
  head : Fin sig.length
  arguments : List (List (Label sig))
  arity : arguments.length = sig[head].parameters

def Scope.rawArgs (scope : Scope sig) : Args :=
  Args.ofList (scope.arguments.map fun ts => Types.ofList (ts.map Subtype.val))

private theorem Types.scoped_of_labels (ts : List (Label sig)) :
    (Types.ofList (ts.map Subtype.val)).scoped sig 0 0 = true := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, Types.ofList, Types.scoped, t.2, ih, Bool.and_self]

private theorem Scope.args_closed (scope : Scope sig) :
    scope.rawArgs.scoped sig 0 0 = true := by
  unfold rawArgs
  induction scope.arguments with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, Args.ofList, Args.scoped, Types.scoped_of_labels, ih, Bool.and_self]

private theorem Scope.arity_ok (scope : Scope sig) :
    arityOk sig scope.head.val scope.rawArgs = true := by
  simp [arityOk, rawArgs, scope.arity]

def Scope.label (scope : Scope sig) : Label sig :=
  ⟨.app scope.head.val scope.rawArgs, by
    simp [Tree.scoped, scope.arity_ok, scope.args_closed]⟩

def Scope.bound (scope : Scope sig) (slot : Fin sig[scope.head].binders.length) : Label sig :=
  ⟨.bound scope.head.val scope.rawArgs slot.val, by
    simp [Tree.scoped, scope.arity_ok, scope.args_closed, binderOk]⟩

/-- A scope's local parameters in their declared order. -/
def Scope.binders (scope : Scope sig) : List (Label sig) :=
  (List.finRange sig[scope.head].binders.length).map scope.bound

@[simp] theorem Scope.binders_length (scope : Scope sig) :
    scope.binders.length = sig[scope.head].binders.length := by simp [binders]

@[simp] theorem Scope.mem_binders {scope : Scope sig} {p : Label sig} :
    p ∈ scope.binders ↔ ∃ slot, p = scope.bound slot := by
  simp [binders, eq_comm]

theorem Scope.bound_injective (scope : Scope sig) : Function.Injective scope.bound := by
  intro a b h
  have he := congrArg Subtype.val h
  simp only [bound, Tree.bound.injEq] at he
  exact Fin.ext he.2.2

theorem Scope.binders_nodup (scope : Scope sig) : scope.binders.Nodup :=
  (List.nodup_finRange _).map scope.bound (fun _ _ h he => h (scope.bound_injective he))

/-- Concatenating unions does not inspect or unfold their labels. -/
def Types.append : Types → Types → Types
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (xs.append ys)

theorem Types.scoped_append (xs ys : Types)
    (hx : xs.scoped sig p l = true) (hy : ys.scoped sig p l = true) :
    (xs.append ys).scoped sig p l = true := by
  cases xs with
  | nil => exact hy
  | cons x xs =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hx
    exact Bool.and_eq_true_iff.mpr ⟨h1, scoped_append xs ys h2 hy⟩

abbrev ClosedTypes (sig : Signature) := { ts : Types // ts.scoped sig 0 0 = true }

/- Instantiation traverses the finite expression, never its referenced
rows. The result is closed by construction; missing arguments are impossible
under the expression's scope proof and the application's arity proof. -/
mutual
def Tree.instantiate (scope : Scope sig) (t : Tree)
    (valid : t.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true) :
    ClosedTypes sig :=
  match t with
  | .app h args =>
    let a := Args.instantiate scope args (Bool.and_eq_true_iff.mp valid).2
    ⟨.cons (.app h a.1) .nil, by
      have ha := (Bool.and_eq_true_iff.mp valid).1
      have : arityOk sig h a.1 = true := by simpa [arityOk, a.2.2] using ha
      simp [Types.scoped, Tree.scoped, this, a.2.1]⟩
  | .bound h args i =>
    let a := Args.instantiate scope args (Bool.and_eq_true_iff.mp valid).2
    ⟨.cons (.bound h a.1 i) .nil, by
      have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
      have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).2
      have : arityOk sig h a.1 = true := by simpa [arityOk, a.2.2] using ha
      simp [Types.scoped, Tree.scoped, this, hb, a.2.1]⟩
  | .argument i =>
    have hi : i < scope.arguments.length := by
      have : i < sig[scope.head].parameters := of_decide_eq_true valid
      simpa only [scope.arity] using this
    ⟨Types.ofList (scope.arguments[i].map Subtype.val), Types.scoped_of_labels _⟩
  | .local i =>
    let b := scope.bound ⟨i, of_decide_eq_true valid⟩
    ⟨.cons b.1 .nil, by simp [Types.scoped, b.2]⟩
def Types.instantiate (scope : Scope sig) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true) :
    ClosedTypes sig :=
  match ts with
  | .nil => ⟨.nil, rfl⟩
  | .cons t ts =>
    let a := Tree.instantiate scope t (Bool.and_eq_true_iff.mp valid).1
    let b := Types.instantiate scope ts (Bool.and_eq_true_iff.mp valid).2
    ⟨a.1.append b.1, Types.scoped_append _ _ a.2 b.2⟩
def Args.instantiate (scope : Scope sig) (args : Args)
    (valid : args.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true) :
    { out : Args // out.scoped sig 0 0 = true ∧ out.toList.length = args.toList.length } :=
  match args with
  | .nil => ⟨.nil, by simp [Args.scoped, Args.toList]⟩
  | .cons ts args =>
    let a := Types.instantiate scope ts (Bool.and_eq_true_iff.mp valid).1
    let b := Args.instantiate scope args (Bool.and_eq_true_iff.mp valid).2
    ⟨.cons a.1 b.1, by
      simp [Args.scoped, Args.toList, a.2, b.2.1, b.2.2]⟩
end

/-- Recover the closed labels of a union, retaining each scope proof. -/
def Types.labels (ts : Types) (valid : ts.scoped sig 0 0 = true) : List (Label sig) :=
  match ts with
  | .nil => []
  | .cons t ts => ⟨t, (Bool.and_eq_true_iff.mp valid).1⟩ :: ts.labels (Bool.and_eq_true_iff.mp valid).2

theorem Types.labels_append (xs ys : Types) (hx : xs.scoped sig 0 0 = true)
    (hy : ys.scoped sig 0 0 = true) (hxy : (xs.append ys).scoped sig 0 0 = true) :
    (xs.append ys).labels hxy = xs.labels hx ++ ys.labels hy := by
  cases xs with
  | nil => rfl
  | cons t ts =>
    simp only [append, labels, List.cons_append,
      labels_append ts ys (Bool.and_eq_true_iff.mp hx).2 hy]

@[simp] theorem Types.labels_length (ts : Types) (valid : ts.scoped sig 0 0 = true) :
    (ts.labels valid).length = ts.toList.length := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [labels, toList, List.length_cons,
      labels_length ts (Bool.and_eq_true_iff.mp valid).2]

def Expression.instantiate (scope : Scope sig) (e : Expression sig sig[scope.head]) : List (Label sig) :=
  let out := Tree.instantiate scope e.1 e.2.1
  out.1.labels out.2

private theorem Tree.instantiate_single (scope : Scope sig) (t : Tree)
    (valid : t.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (single : t.single = true) :
    (Tree.instantiate scope t valid).1.toList.length = 1 := by
  cases t <;> simp_all [Tree.single, Tree.instantiate, Types.toList]

/-- A binding reference denotes exactly one closed label, never the first
member of a union or a fallback for a missing argument. -/
def Reference.instantiate (scope : Scope sig) (r : Reference sig sig[scope.head]) : Label sig :=
  let out := r.1.instantiate scope
  have hlen : out.length = 1 := by
    simp only [out, Expression.instantiate, Types.labels_length]
    exact Tree.instantiate_single scope r.1.1 r.1.2.1 r.2
  out[0]'(by omega)

/-- A constructor-headed equation row, before checking its binder interface.
Type operands may expand a parameter's union; binding positions remain single
references. Non-constructor source aliases must be normalized by the compiler. -/
abbrev RowTemplate (sig : Signature) (head : Fin sig.length) :=
  GraphRow (Reference sig sig[head]) (List (Expression sig sig[head]))

/-- Only a scheme introduces local parameters, exactly those in its header.
Its bounds are read outside those parameters. Parameter and dependent-meet
rows are not declaration heads: parameters come from a scope; intersections
require normalization rather than pretending an arbitrary argument is rigid. -/
def RowTemplate.wellBound (head : Fin sig.length) : RowTemplate sig head → Bool
  | .clauses _ => sig[head].binders.isEmpty
  | .scheme bs _ bounds _ =>
    decide (bs.map (fun b => b.1.1) = (List.range sig[head].binders.length).map Tree.local) &&
      bounds.all (fun (b, T) => (bs.any fun p => decide (p = b)) &&
        T.all (fun t => t.1.lexical false))
  | .param .. | .meet .. => false

abbrev Template (sig : Signature) (head : Fin sig.length) :=
  { body : RowTemplate sig head // body.wellBound head = true }

def Template.instantiate (scope : Scope sig) (body : Template sig scope.head) : GraphRow (Label sig) :=
  body.1.map (Reference.instantiate scope) (fun ts => ts.flatMap (Expression.instantiate scope))

def Args.labels (args : Args) (valid : args.scoped sig 0 0 = true) : List (List (Label sig)) :=
  match args with
  | .nil => []
  | .cons ts args => ts.labels (Bool.and_eq_true_iff.mp valid).1 ::
      args.labels (Bool.and_eq_true_iff.mp valid).2

@[simp] theorem Args.labels_length (args : Args) (valid : args.scoped sig 0 0 = true) :
    (args.labels valid).length = args.toList.length := by
  cases args with
  | nil => rfl
  | cons ts args => simp only [labels, toList, List.length_cons,
      labels_length args (Bool.and_eq_true_iff.mp valid).2]

theorem Types.labels_ofList (ts : List (Label sig))
    (valid : (ofList (ts.map Subtype.val)).scoped sig 0 0 = true) :
    (ofList (ts.map Subtype.val)).labels valid = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, ofList, labels, ih]

private theorem Args.labels_ofList (args : List (List (Label sig)))
    (valid : (ofList (args.map fun ts => Types.ofList (ts.map Subtype.val))).scoped sig 0 0 = true) :
    (ofList (args.map fun ts => Types.ofList (ts.map Subtype.val))).labels valid = args := by
  induction args with
  | nil => rfl
  | cons ts args ih => simp only [List.map_cons, ofList, labels, Types.labels_ofList, ih]

private theorem Scope.labels_rawArgs (scope : Scope sig)
    (valid : scope.rawArgs.scoped sig 0 0 = true) :
    scope.rawArgs.labels valid = scope.arguments := Args.labels_ofList scope.arguments valid

private theorem arityOk_exists (valid : arityOk sig head args = true) : head < sig.length := by
  by_cases h : head < sig.length
  · exact h
  · have : sig[head]? = none := List.getElem?_eq_none (by omega)
    simp [arityOk, this] at valid

/-- Reading a closed application recovers the very same scope that built it;
no argument is inferred again or replaced by a default. -/
def Scope.ofRaw (head : Nat) (args : Args) (arity : arityOk sig head args = true)
    (closed : args.scoped sig 0 0 = true) : Scope sig :=
  { head := ⟨head, arityOk_exists arity⟩
    arguments := args.labels closed
    arity := by simpa [arityOk, arityOk_exists arity] using arity }

@[ext] theorem Scope.ext {a b : Scope sig} (hhead : a.head = b.head)
    (hargs : a.arguments = b.arguments) : a = b := by
  cases a
  cases b
  cases hhead
  cases hargs
  rfl

@[simp] theorem Scope.ofRaw_rawArgs (scope : Scope sig)
    (ha : arityOk sig scope.head.val scope.rawArgs = true)
    (hc : scope.rawArgs.scoped sig 0 0 = true) :
    Scope.ofRaw scope.head.val scope.rawArgs ha hc = scope := by
  apply Scope.ext
  · apply Fin.ext; rfl
  · exact scope.labels_rawArgs hc

inductive View (sig : Signature) where
  | application (scope : Scope sig)
  | parameter (scope : Scope sig) (slot : Fin sig[scope.head].binders.length)

def Label.view (label : Label sig) : View sig :=
  match label with
  | ⟨.app h args, valid⟩ =>
    .application (Scope.ofRaw h args (Bool.and_eq_true_iff.mp valid).1 (Bool.and_eq_true_iff.mp valid).2)
  | ⟨.bound h args i, valid⟩ =>
    let ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
    let hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).2
    let scope := Scope.ofRaw h args ha (Bool.and_eq_true_iff.mp valid).2
    .parameter scope ⟨i, by simpa [binderOk, scope, Scope.ofRaw, arityOk_exists ha] using hb⟩
  | ⟨.argument _, valid⟩ => False.elim (by simp [Tree.scoped] at valid)
  | ⟨.local _, valid⟩ => False.elim (by simp [Tree.scoped] at valid)

@[simp] theorem Scope.view_label (scope : Scope sig) : scope.label.view = .application scope := by
  simp [label, Label.view]

@[simp] theorem Scope.view_bound (scope : Scope sig) (slot : Fin sig[scope.head].binders.length) :
    (scope.bound slot).view = .parameter scope slot := by
  simp [bound, Label.view, Scope.ofRaw, Scope.labels_rawArgs]
  apply Fin.ext
  rfl

theorem Types.labels_val (ts : Types) (valid : ts.scoped sig 0 0 = true) :
    Types.ofList ((ts.labels valid).map Subtype.val) = ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [labels, List.map_cons, ofList,
      labels_val ts (Bool.and_eq_true_iff.mp valid).2]

private theorem Args.labels_val (args : Args) (valid : args.scoped sig 0 0 = true) :
    Args.ofList ((args.labels valid).map fun ts => Types.ofList (ts.map Subtype.val)) = args := by
  cases args with
  | nil => rfl
  | cons ts args => simp only [labels, List.map_cons, ofList, Types.labels_val,
      labels_val args (Bool.and_eq_true_iff.mp valid).2]

theorem Scope.ofRaw_args (head : Nat) (args : Args) (ha hc) :
    (Scope.ofRaw (sig := sig) head args ha hc).rawArgs = args := by
  exact Args.labels_val args hc

/-- Every closed label is an application or one of its owned parameters. -/
theorem Label.cases {P : Label sig → Prop} (label : Label sig)
    (app : ∀ scope : Scope sig, P scope.label)
    (bound : ∀ (scope : Scope sig) slot, P (scope.bound slot)) : P label := by
  rcases label with ⟨t, valid⟩
  cases t with
  | app h args =>
    let scope := Scope.ofRaw h args (Bool.and_eq_true_iff.mp valid).1 (Bool.and_eq_true_iff.mp valid).2
    have he : scope.label = (⟨.app h args, valid⟩ : Label sig) := by
      apply Subtype.ext
      simp only [scope, Scope.label, Scope.ofRaw_args]
      rfl
    exact he ▸ app scope
  | bound h args i =>
    let scope := Scope.ofRaw h args (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
      (Bool.and_eq_true_iff.mp valid).2
    have slot : i < sig[scope.head].binders.length := by
      have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).2
      have hh := arityOk_exists (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
      simpa [binderOk, scope, Scope.ofRaw, hh] using hb
    have he : scope.bound ⟨i, slot⟩ = (⟨.bound h args i, valid⟩ : Label sig) := by
      apply Subtype.ext
      simp only [scope, Scope.bound, Scope.ofRaw_args]
      rfl
    exact he ▸ bound scope ⟨i, slot⟩
  | argument i => simp [Tree.scoped] at valid
  | «local» i => simp [Tree.scoped] at valid

/-- A finite list of templates presents every application at its arguments.
There is no depth, colour or unfolding budget in the graph definition. -/
structure Equations where
  signature : Signature
  body : (head : Fin signature.length) → Template signature head
  realm : Option (ArrayRealm (Label signature)) := none

def Equations.row (equations : Equations) (label : Label equations.signature) :
    GraphRow (Label equations.signature) :=
  match label.view with
  | .application scope => (equations.body scope.head).instantiate scope
  | .parameter scope slot =>
    let b := equations.signature[scope.head].binders[slot]
    .param label b.name b.kind

def Equations.graph (equations : Equations) : NormalGraph (Label equations.signature) :=
  NormalGraph.ofRowMap equations.row equations.realm

/-- Unfolding an application substitutes into its one finite template. -/
@[simp] theorem Equations.row_application (equations : Equations) (scope : Scope equations.signature) :
    equations.row scope.label = (equations.body scope.head).instantiate scope := by
  simp [row]

/-- A bound parameter has the kind declared at its own lexical owner. -/
@[simp] theorem Equations.kind_bound (equations : Equations) (scope : Scope equations.signature)
    (slot : Fin equations.signature[scope.head].binders.length) :
    equations.graph.parameterKinds (scope.bound slot) =
      some equations.signature[scope.head].binders[slot].kind := by
  simp [graph, NormalGraph.ofRowMap, row]

/- An application's free parameter names are those carried by its arguments.
A parameter name is atomic: its owner identifies it, but changing an assignment
at a name occurring inside that owner does not change the parameter's value. -/
mutual
def Tree.free : Tree → List Tree
  | .app _ args => args.free
  | t@(.bound ..) => [t]
  | .argument _ | .local _ => []
def Types.free : Types → List Tree
  | .nil => []
  | .cons t ts => t.free ++ ts.free
def Args.free : Args → List Tree
  | .nil => []
  | .cons ts args => ts.free ++ args.free
end

mutual
private theorem Tree.free_size (t p : Tree) (h : p ∈ t.free) : sizeOf p ≤ sizeOf t := by
  cases t with
  | app head args =>
    have hs := Args.free_size args p h
    have he : sizeOf (Tree.app head args) = 1 + sizeOf head + sizeOf args := rfl
    omega
  | bound head args slot =>
    have : p = Tree.bound head args slot := List.mem_singleton.mp h
    subst this
    exact Nat.le_refl _
  | argument _ => simp [Tree.free] at h
  | «local» _ => simp [Tree.free] at h
private theorem Types.free_size (ts : Types) (p : Tree) (h : p ∈ ts.free) :
    sizeOf p < sizeOf ts := by
  cases ts with
  | nil => simp [Types.free] at h
  | cons t ts =>
    have he : sizeOf (Types.cons t ts) = 1 + sizeOf t + sizeOf ts := rfl
    rcases List.mem_append.mp h with h | h
    · have hs := Tree.free_size t p h; omega
    · have hs := Types.free_size ts p h; omega
private theorem Args.free_size (args : Args) (p : Tree) (h : p ∈ args.free) :
    sizeOf p < sizeOf args := by
  cases args with
  | nil => simp [Args.free] at h
  | cons ts args =>
    have he : sizeOf (Args.cons ts args) = 1 + sizeOf ts + sizeOf args := rfl
    rcases List.mem_append.mp h with h | h
    · have hs := Types.free_size ts p h; omega
    · have hs := Args.free_size args p h; omega
end

/-- The binder introduced by a scope cannot already occur in its captured
arguments. Its name contains those arguments; such an occurrence would require
a finite syntax tree to contain itself as a proper subtree. -/
theorem Scope.bound_fresh (scope : Scope sig) (slot : Fin sig[scope.head].binders.length) :
    (scope.bound slot).1 ∉ scope.rawArgs.free := by
  intro h
  have hs := Args.free_size scope.rawArgs (scope.bound slot).1 h
  have he : sizeOf (scope.bound slot).1 =
      1 + sizeOf scope.head.val + sizeOf scope.rawArgs + sizeOf slot.val := rfl
  omega

/-- Constructor applications do not secretly introduce an unquantified
parameter. Only an owned bound label has a parameter kind. -/
theorem Equations.kind_application (equations : Equations) (scope : Scope equations.signature) :
    equations.graph.parameterKinds scope.label = none := by
  simp only [graph, NormalGraph.ofRowMap, row, Scope.view_label, Template.instantiate]
  have hv := (equations.body scope.head).2
  cases h : (equations.body scope.head).1 <;>
    simp_all [RowTemplate.wellBound, GraphRow.map]

#print axioms Equations.row_application
#print axioms Equations.kind_bound
#print axioms Equations.kind_application
#print axioms Scope.bound_fresh

end Verification.Model.EquationGraphs
