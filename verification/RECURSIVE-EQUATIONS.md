# Recursive equations

This document specifies how generic declarations whose instances form an
infinite family, `Promise` among them, reach the verifier. Each declaration is
one parameterized equation, and each instance is a finite term: an application
of that equation to arguments. A check unfolds an application one step, and
only when it reads it. The document covers:

- the representation and its meaning;
- instantiation by substitution;
- the subtyping rules that relate two members of one family;
- the lowering from source;
- the wire format;
- the acceptance statement.

The meaning of a type is the one in [SEMANTICS](SEMANTICS.md) and
[POSITIVE-TYPES](POSITIVE-TYPES.md). Equations present graphs to that
semantics; they add no second interpretation of types.

**Proof scope.** Sections 3 to 5 are proved in Lean, meet labels (3.3)
excepted. Meet labels and sections 6 to 10 are specifications: each rule
there needs its soundness lemma before any source program depends on it.
Source and CLI acceptance use only the finite checker. How far the work has
got is recorded in [DESIGN: status](DESIGN.md#status).

## 1. The problem: non-regular families

A finite type table ([REQUEST-PROTOCOL](REQUEST-PROTOCOL.md#request-fields))
presents a regular graph: finitely many distinct types, recursion by
reference back to a row. Many generic declarations are regular at each
instance: the rows of a `List<number>` mention only `List<number>` and
`number`. Others are not:

```ts
interface Promise<T> {
  then<R>(f: (x: T) => R): Promise<R>; // simplified
  catch<R>(f: (e: unknown) => R): Promise<T | R>;
}
interface Pair<T> {
  first(): T;
  push<U>(u: U): Pair<[T, U]>;
}
```

Unfolding `Promise<number>` reaches `Promise<number | R>`. Its `catch` binds
another `R′` and reaches `Promise<number | R | R′>`, and so on. Each member
mentions a larger one, so the family is infinite and has no regular
presentation. `Pair` grows the same way through its argument. The finite lowering
([PROGRAM-TYPING: one row per application](PROGRAM-TYPING.md#one-row-per-application))
enumerates applications up to a budget and refuses the entire declaration past
it. Reading the tail as `unknown` would be unsound; a larger budget moves the
refusal and does not remove it.

The semantics never needed finiteness. A `NormalGraph` may have any label
type, and a type's meaning is a guarded fixed point, not an enumeration of
rows. What must be finite is what a check inspects. So:

- a family is presented by finitely many equations with parameters;
- a member is named by a finite term, an application of one equation to
  arguments;
- a member's row is computed when a check reads it, by instantiating its one
  equation, which leaves every application inside it unexpanded;
- two members are related by rules that inspect finitely many rows:
  substitution into finite terms instantiates a generic member (section 4),
  and a finite family argument relates two members for subtyping (section 7).

## 2. What is delayed, and related work

An application $`h(\vec A)`$ is a closure: an equation paired with an
environment for its parameters. It delays unfolding a named definition
(δ-reduction), not substitution. Instantiation substitutes into the whole
finite template at once and stops at the applications the template contains,
because those are references to definitions. The type level has no β-redexes.
So the apparatus of explicit substitutions
([Abadi et al. 1991](REFERENCES.md#abadi-cardelli-curien-and-lévy-1991)) has
nothing to do here: substitutions as term formers, their propagation,
confluence. What is kept is the closure reading, and a substitution lemma
relating syntactic to semantic substitution (section 4.3).

The families are parameterized type definitions
([Solomon 1978](REFERENCES.md#solomon-1978)); the non-regular ones unfold to
trees with infinitely many distinct subtrees. Subtyping between recursive
types is checked coinductively over a finite set of assumed pairs
([Amadio and Cardelli 1993](REFERENCES.md#amadio-and-cardelli-1993),
[Brandt and Henglein 1998](REFERENCES.md#brandt-and-henglein-1998)), as the
[core tables](POSITIVE-TYPES.md#core-tables) already do. Section 7 lifts the
assumed pairs to pairs with parameters, so one entry covers a whole family.
Subtyping with variance over expanding definitions is undecidable in general
([Kennedy and Pierce 2007](REFERENCES.md#kennedy-and-pierce-2007)). The
checker therefore checks a certificate the producer proposes; it decides
nothing beyond its rules.

## 3. Equations and labels

### 3.1 Signature, templates and labels

A **signature** fixes, for each head $`h`$, its arity (how many parameters
an application takes) and its local binders with their kinds (value or
argument list). A head's **template** $`E_h`$ is a row whose operands are
finite trees over:

- applications $`g(\vec A)`$ and owned parameters $`\mathsf{bound}(g,\vec A,j)`$;
- the placeholders $`\mathsf{arg}\ i`$ ($`i`$ below $`h`$'s arity) and
  $`\mathsf{local}\ j`$ ($`j`$ below $`h`$'s binder count).

A **label** is a closed tree, with no placeholder:

```math
\begin{aligned}
L &::= h(A_1,\ldots,A_n) \;\mid\; \mathsf{bound}(h,[A_1,\ldots,A_n],j) \;\mid\; \mathsf{meet}(L_1,\ldots,L_k)\\
A &::= [L_1,\ldots,L_m]\qquad\text{a union of labels}
\end{aligned}
```

Scope and arity are checked at every nested application. A template is
**constructor-headed**: a clause row or a scheme row. Parameter and meet rows
are not templates: parameters come from applications, and intersections are
meet labels (3.3). A scheme template binds exactly its head's locals, in
order, and its bounds do not mention them. Any other template introduces no
local.

### 3.2 The row equation

```math
G\bigl(h(\vec A)\bigr)=\mathrm{instantiate}(E_h,\vec A),
\qquad
G\bigl(\mathsf{bound}(h,\vec A,j)\bigr)=\mathsf{param}\bigl(\mathrm{kind}_h(j)\bigr).
```

Instantiation replaces $`\mathsf{arg}\ i`$ by the whole union $`A_i`$ and
$`\mathsf{local}\ j`$ by $`\mathsf{bound}(h,\vec A,j)`$. It visits only the
finite template and leaves every application inside it unexpanded. The rows
feed `NormalGraph.ofRowMap`, the same interpretation as finite wire tables.

A local parameter is **owned** by its application. Its name contains its
owner's argument tree, so it cannot occur inside that tree: an application's
binders are fresh for its captured arguments by construction
(`Scope.binders_nodup`, `Scope.bound_injective`). Nested instantiation cannot
capture an enclosing binder, and no renaming discipline is needed. A binder
name is atomic when computing free support. Its owner's arguments identify
the name; they are not further dependencies of its assigned meaning.

Lean: `Header`, `Tree`, `Label`, `Scope`, `Template`, `Equations.row`,
`Equations.graph`, `Equations.row_application`, `Equations.kind_bound`
(`Types/EquationGraphs.lean`).

### 3.3 Meet labels

**Specification; not yet in Lean.** An intersection is a label of its own:

```math
G\bigl(\mathsf{meet}(L_1,\ldots,L_k)\bigr)=
\begin{cases}
\mathrm{smeet}\bigl(G(L_1),\ldots,G(L_k)\bigr) & \text{no part is a parameter},\\
p\sqcap\vec q\sqcap\mathrm{smeet}\bigl(G(L_i)\mid L_i\notin P\bigr) & P=\{p\}\cup\vec q\ \text{the parameter parts}.
\end{cases}
```

$`\mathrm{smeet}`$ is the **source meet** that lowering uses today
(`DeclarationGraph.meetRow`, `sourceMeetLists`). It is the
[normalized conjunction](POSITIVE-TYPES.md#conjunction-and-normalization) of
the parts' clauses, except that a record met with a function becomes one
`callable` clause, which is what TypeScript means by that intersection. The
parts are flat (no part is a meet), distinct, at least two, and in a
canonical order. No part is a scheme application: a meet with a generic
callable is refused, as it is now. The source meet concatenates operands and
never meets two operands. So a meet label's row names only labels its parts'
rows name, creates no new application, and cannot grow a family.

A meet label means what its row says. The checker's soundness needs nothing
more: meanings come from rows, and support, congruence and substitution are
proved for meet trees as for applications. Where no record is met with a
function, the row is the model's intersection (`normalize_sound`,
`meetLists_sound`, and the meet-row semantics for parameter parts):

```math
⟦\mathsf{meet}(L_1,\ldots,L_k)⟧^\eta=⟦L_1⟧^\eta\cap\cdots\cap⟦L_k⟧^\eta .
```

That equation is a fidelity property of lowering, not a premise of any
rule.

Templates get the corresponding placeholder former. Instantiation
distributes over unions, since intersection distributes over union:

```math
\mathsf{meet}(A_1,\ldots,A_k)=\textstyle\bigvee\{\,\mathsf{meet}(L_1,\ldots,L_k)\mid L_i\in A_i\,\},
```

and a single remaining part is that part. A meet whose normal form is
$`\bot`$ is refused where it is lowered, as today. The row reads its parts'
rows at the same level, not under a guard. This is well founded because
parts are applications or parameters, whose rows come from templates, never
from another meet. The congruence proof (4.2) must take this step
explicitly: a meet's row agrees at level $`n`$ when its parts' rows do.

## 4. Support, congruence and substitution

### 4.1 Free support

The free parameters of a label are the owned parameters carried by its
arguments, computed on the finite tree. Agreement on them implies equal
meaning, for values and argument lists together:

```math
\bigl(\forall p\in\mathrm{FV}(A).\ \eta(p)=\theta(p)\bigr)
\;\Longrightarrow\;
⟦A⟧^\eta=⟦A⟧^\theta .
```

The support over-approximates: it may retain a captured parameter a row does
not use. The proof reuses semantic independence for ordinary graph rows.
`FreeSupport` states local closure conditions over a possibly infinite
domain:

- a parameter is free in itself;
- an operand's support belongs to its row's support or to that row's scheme
  binders;
- bounds depend only on the outer support;
- meets retain their parameters.

For a finite table, the executable `FreeOk` establishes these conditions.
For equation templates they hold by structural induction on instantiation,
so no family is enumerated.

Lean: `Label.free`, `FreeSupport`, `Equations.free_support`,
`Equations.agree_free` (`Types/EquationSupport.lean`).

### 4.2 Application congruence

Two applications of one head at arguments with equal meanings have equal
meanings. The two environments may differ, because an equation receives its
free parameters only through its arguments:

```math
\bigl(\forall i.\ ⟦A_i⟧^\eta=⟦B_i⟧^\theta\bigr)
\;\Longrightarrow\;
⟦h(\vec A)⟧^\eta=⟦h(\vec B)⟧^\theta .
```

The proof is by induction on the level $`n`$:

1. Value rows are compared at $`n`$, using operand agreement below $`n`$.
   Quantified bounds are compared in the outer environments. Signatures are
   compared after assigning matching local families; binder order is checked
   exactly, not as a set.
2. Argument packs are compared at $`n`$. Their element contracts use the
   current-level values from step 1.

The induction closes the intermediate `ApplicationsAgree` premise. Neither
the producer nor a certificate supplies a semantic assumption.

Lean: `Equations.applications_agree`, `Equations.application_congr`,
`Equations.clauses_step`, `Equations.scheme_step`, `Equations.arguments_step`
(`Types/EquationCongruence.lean`).

### 4.3 Checked substitution

Substitution traverses the finite argument syntax and never reads a
recursive row:

- it replaces a bound name atomically;
- a name the substitution does not map is left unchanged;
- replacements are simultaneous, so the context is not applied again inside
  a replacement;
- the result applications own the locals introduced when their rows are
  unfolded, so a captured parameter stays captured and does not become a
  fresh universal.

```math
⟦A⟧^{\eta[\vec b\mapsto⟦\vec U⟧^\eta]}=⟦A[\vec b:=\vec U]⟧^\eta .
```

Each replacement must have its parameter's kind (value or argument list).
Substituting a label into itself is allowed: $`a:=a\mid r`$ is a
simultaneous substitution and the theorem covers it. Section 7 relies on
this.

Lean: `Tree.substitute`, `Label.substitute`, `Label.substitute_meaning`,
`Equations.assignment_parameterImages` (`Types/EquationSubstitution.lean`).

## 5. Instance images

Eliminating a scheme at an instance, `inst` in
[POSITIVE-TYPES](POSITIVE-TYPES.md#instances-of-a-scheme-row), needs each
named image of a signature type to have the meaning of that type at the
instance. This obligation is `InstanceImages`. The subtype checker is stated
once over an `InstanceImageCheck`: an executable image check together with a
proof that acceptance establishes `InstanceImages`. It has two
implementations:

- **finite** (`finiteInstanceImages`): the closed table with its closure,
  free-variable and kind checks (`TableOk`);
- **equations** (`Equations.instanceImageCheck`): each image must equal the
  structural substitution of section 4.3 (`substitutionTableOk`). No
  recursive row closure or expansion cutoff is used.

Bounds, kinds, fixed and variadic signatures, receivers and effects use the
same checks in both. Expression typing (`HasTyUsing`) and program
certificates (`ProgramCertificates.checkUsing`) are stated over the same
interface, so both checkers reach them with the soundness proofs unchanged.
Other proof forms still check their own closure and free-support evidence.

Lean: `InstanceImageCheck`, `checkUsing`, `checkUsing_sound`,
`Equations.substitutionTable_instanceImages`, `Equations.checkSubtype_sound`
(`Types/PositiveCertificates.lean`, `Types/EquationCertificates.lean`).

## 6. Quantified coverage modulo binder renaming

**Specification; not yet in Lean.** The
[quantified rule](POSITIVE-TYPES.md#core-tables) relates two scheme rows
only when they bind the same parameter rows. The finite lowering arranges
this by sharing binder rows by member key and colour. Equation binders are
owned, so the `then` of `Promise<number>` and the `then` of
`Promise<number | string>` bind different labels. The rule therefore renames
the target's binders to the source's:

```math
\frac{\begin{array}{c}
i=(\vec p;\Sigma;\beta;\Sigma_\ldots)\qquad j=(\vec q;\Sigma';\beta';\Sigma'_\ldots)\qquad
|\vec p|=|\vec q|\qquad \forall k.\ \mathrm{kind}(p_k)=\mathrm{kind}(q_k)\\
\vec p\cap\mathrm{FV}(j)=\emptyset\qquad
\beta\subseteq\beta'[\vec q:=\vec p]\qquad
\Delta\vdash\mathsf{arrs}(\Sigma;\Sigma_\ldots)\sqsubseteq\mathsf{arrs}(\Sigma';\Sigma'_\ldots)[\vec q:=\vec p]
\end{array}}
{\Delta\vdash i\sqsubseteq_\forall j}\ \mathsf{Quantified}\text{-}\alpha
```

The substitution is the one of section 4.3, computed by the checker, not
supplied. The freshness premise uses the computed support.

**Soundness.** Take a member of $`i`$ and an instance $`\vec X`$ within
$`\beta'`$. Then $`\vec X`$ is within $`\beta`$ at $`\vec p`$. The member
meets $`\Sigma`$ at $`\eta[\vec p:=\vec X]`$, and the premise gives the
renamed target signatures there. Since $`\vec p\notin\mathrm{FV}(j)`$,
substitution gives

```math
⟦\Sigma'[\vec q:=\vec p]⟧^{\eta[\vec p:=\vec X]}=⟦\Sigma'⟧^{\eta[\vec q:=\vec X]} ,
```

which is what membership in $`j`$ requires. The table premise is read at the
instance's assignment. It holds there because every entry holds at every
assignment, or, inside a family (section 7), at every assignment satisfying
the family's hypotheses; those do not mention $`\vec p`$. The existing rule is
the case $`\vec q=\vec p`$. The restriction is the one the existing rule
takes from [Pierce 1994](REFERENCES.md#pierce-1994): target binders are
rigid, and bounds are compared by inclusion only.

## 7. Family subtyping

**Specification; not yet in Lean.** Relating
`Promise<number> ≤ Promise<number | string>` by ordinary core tables with
quantified-α needs these pairs:

```text
Promise<number>          ≤ Promise<number | string>              (then: identical after renaming)
Promise<number | r>      ≤ Promise<number | string | r>          (catch)
Promise<number | r | r′> ≤ Promise<number | string | r | r′>     (catch of catch)
…
```

Each binder is a new label, so no finite table closes. The pairs differ
only in their arguments. So an entry may quantify over its arguments: one
entry states $`\mathit{Promise}(a)\le\mathit{Promise}(b)`$ for every $`a\le b`$,
and every later pair is an instance of it.

That entry is a fact about the declaration, not about any use: `Promise` is
covariant because its body only reads `T`. The fact is established once, by
looking inside the definition, and every use then compares arguments only.
Entries therefore live in two places:

- **Variance declarations** (7.5). Each head declares a variance per
  parameter, and the declaration is checked once, as a family entry, when
  the equations are accepted. A use `h(A⃗) ≤ h(B⃗)` needs only the
  per-position argument premises and never unfolds `h`. This is the
  ordinary case.
- **Certificate entries** (7.1–7.4). A subtype certificate may carry its own
  entries for what a variance cannot state: relations between different
  heads (`Promise<T> ≤ PromiseLike<T>`), or hypotheses that are not
  per-position.

Both are checked by the same rule and justified by the same theorem (7.4).

### 7.1 Family entries

A **family entry** is

```math
f=\bigl(\,h(\vec a)\le h'(\vec b),\ \Pi_f,\ \Delta_f\,\bigr)
```

where:

- $`\vec a,\vec b`$ are the family's **variables**: parameter labels of
  declared kinds, owned by the entry. They occur in no equation template, no
  claim, and no other entry. A variable may appear on both sides, which
  expresses invariance by sharing ($`h(a,c)\le h(b,c)`$).
- $`\Pi_f`$ is a finite set of **hypotheses** $`x\le y`$ between variables of
  one kind. Two-way hypotheses $`x\le y`$ and $`y\le x`$ state equivalence
  without sharing.
- $`\Delta_f`$ is a finite table of pairs of types whose free parameters are
  the variables, owned binders reached by unfolding, or both.

A **family certificate** is a finite set $`F`$ of entries, with no two
sharing a variable. An ordinary core table is an entry with no variables and
no hypotheses. So a plain `S ≤ T` is checked as the goal of a
variable-free entry, or as a pair in its table.

### 7.2 Premises

Operand premises in coverage (the $`\Delta(A,B)`$ of
[clause coverage](POSITIVE-TYPES.md#clause-coverage)) are read in an entry
$`f`$ by the relation $`\Delta_f\Vdash A\sqsubseteq B`$. It holds when either:

1. $`(A,B)\in\Delta_f`$; or
2. every label $`l`$ of $`A`$ satisfies one of:
   - $`l\in B`$;
   - $`l`$ is a variable with $`(l\le y)\in\Pi_f`$ and $`y\in B`$;
   - $`l=g(\vec X)`$, some $`g'(\vec Y)\in B`$, and an entry
     $`f'\in F`$ relates $`g(\vec x)\le g'(\vec y)`$ such that every
     hypothesis $`(x_s\le y_t)\in\Pi_{f'}`$ is met at the instance: the pair
     $`(X_s,Y_t)`$, with the instance's shared positions equal, is in
     $`\Delta_f`$, is a subset, or is a hypothesis of $`\Pi_f`$.

Case 2 is not recursive: an instance's hypotheses are discharged by table
membership, not by another derivation.

### 7.3 Checking an entry

Entry $`f`$ is **valid** when its goal and every pair of $`\Delta_f`$ meet
the three [core conditions](POSITIVE-TYPES.md#core-tables), with two changes:

- **Opaque rows.** A variable $`x`$ of the source may instead be covered by a
  hypothesis $`(x\le y)\in\Pi_f`$ with $`y`$ in the target.
- **Coverage** reads operand premises through $`\Delta_f\Vdash\cdot`$, and
  scheme rows are related by quantified-α.

Everything else is unchanged: the same kinds, clause coverage, known rows
and instance checks. An invariant field still needs $`\Delta^{\pm}`$, that
is, both directions. So a family whose declaration has a writable field at
$`T`$ is valid only with $`a`$ shared, or with both $`a\le b`$ and
$`b\le a`$. Variance is never read from TypeScript. The producer proposes
$`\Pi_f`$ (for example by trying covariance and weakening to invariance on
failure), and the checker checks it.

### 7.4 Soundness

Write $`\eta\models_n\Pi`$ when
$`⟦x⟧^\eta_j\subseteq⟦y⟧^\eta_j`$ for every hypothesis and every level
$`j\le n`$. The theorem to prove:

```math
\forall n.\ \forall f\in F.\ \forall\eta.\
\eta\models_n\Pi_f\ \Longrightarrow\
\forall (A,B)\in\Delta_f\cup\{\mathrm{goal}_f\}.\ ⟦A⟧^\eta_n\subseteq⟦B⟧^\eta_n
```

for values and argument lists. The proof is by strong induction on
$`n`$, the shape of `Core.mixed_sound`:

- **Opaque by hypothesis** holds at $`n`$ because $`\eta\models_n\Pi_f`$.
- **Clause coverage** reads operand premises below $`n`$. A table pair holds
  there by induction (hypotheses hold at every $`j<n`$), and a subset holds
  outright.
- **Family instance.** Instantiate $`f'`$ at
  $`\eta'=\eta[\vec x:=⟦\vec X⟧^\eta,\vec y:=⟦\vec Y⟧^\eta]`$. Its hypotheses
  hold at $`\eta'`$ for every $`j<n`$, because the discharging pairs do (by
  induction, or as hypotheses of $`f`$). By induction at $`j`$ the goal of
  $`f'`$ holds at $`\eta'`$. Substitution (section 4.3) turns it into
  $`⟦g(\vec X)⟧^\eta_j\subseteq⟦g'(\vec Y)⟧^\eta_j`$. When $`f'=f`$ and
  $`\vec X`$ mentions $`f`$'s own variables, the substitution is still
  simultaneous and the theorem applies.
- **Quantified-α** as in section 6. Hypotheses do not mention scheme
  binders, so they survive the reassignment.

A variable-free entry has no hypotheses, which recovers the existing core
theorem. The declarative family rule, its checker and the checker's
completeness for the rule are stated as for the core rule.

### 7.5 Variance declarations

Each head $`h`$ of arity $`n`$ declares a variance
$`v_i\in\{\mathsf{co},\mathsf{contra},\mathsf{inv},\mathsf{none}\}`$ for each
parameter. The declaration stands for the family entry

```math
f_h=\bigl(\,h(x_1,\ldots,x_n)\le h(y_1,\ldots,y_n),\ \Pi_h,\ \Delta_h\,\bigr),
\qquad
\Pi_h=\{x_i\le y_i\mid v_i=\mathsf{co}\}\cup\{y_i\le x_i\mid v_i=\mathsf{contra}\},
```

where $`x_i`$ and $`y_i`$ are one shared variable when $`v_i=\mathsf{inv}`$,
and $`\mathsf{none}`$ imposes nothing.

**Proposed by lowering, carried as evidence.** Variances and the tables
$`\Delta_h`$ are evidence, not part of the request, so the acceptance
premise gains nothing. In the source path, Lean's untrusted lowering
proposes them, since it is the only component that sees the templates. It
computes a least fixpoint over the finite head graph on the lattice
$`\mathsf{none}<\mathsf{co},\mathsf{contra}<\mathsf{inv}`$:

- a writable field, a cell, an index cell or a mutable tuple element gives
  $`\mathsf{inv}`$;
- a readonly view, a result or a readonly element gives $`\mathsf{co}`$;
- a parameter or receiver gives $`\mathsf{contra}`$;
- a nested application composes with that head's current variance;
- a scheme bound gives $`\mathsf{inv}`$.

$`\mathsf{inv}`$ shares one variable, so it is always valid, and weakening
never fails. The untrusted certificate producer searches $`\Delta_h`$ with
the variables as opaque parameters under the hypotheses. The OCaml producer
proposes nothing.

**Checked once.** The declarations of all heads form one set of entries,
checked together by 7.3 once per document, before any request certificate
(`checkEquations`, called from `checkRequests`). Declaration heads are shared
by every unit of the document. Extraction adds only arity-0 heads, which
carry no variance obligation and do not change older heads' rows; this needs
a signature-extension lemma. In the request protocol the check runs in
`verify`. A declaration may rely on the others, and on itself: `catch`'s
$`\mathit{Promise}(a\mid r)\le\mathit{Promise}(b\mid r)`$ is discharged by
$`f_{\mathit{Promise}}`$. If a declaration is invalid, the request is
refused with a located diagnostic naming the head and the parameter. Variances
are never read from TypeScript, whose measured variance treats method
parameters bivariantly.

**The rule.** For applications of one head:

```math
\frac{\forall i.\ \begin{cases}
A_i\le B_i & v_i=\mathsf{co}\\
B_i\le A_i & v_i=\mathsf{contra}\\
A_i\le B_i\ \text{and}\ B_i\le A_i & v_i=\mathsf{inv}\\
\text{nothing} & v_i=\mathsf{none}
\end{cases}}
{h(\vec A)\le h(\vec B)}\ \mathsf{Var}
```

As a premise case of 7.2, the per-position premises are discharged the way
an instance's hypotheses are: a table pair, a subset or a hypothesis. As a
structural rule of `Sub`, they are derivations. An invariant position meets
the rule with two derivations; the entry itself shares one variable, since
that is how 7.3 validates a writable position. Equal meanings suffice for
the soundness step.

**Soundness.** An instance of a valid $`f_h`$, by 7.4 and substitution
(4.3). A derivation holds at every level, so `Var` is sound as a structural
rule too.

Unfolding `Promise` at a use, and carrying a family in the certificate,
become unnecessary for same-head pairs. Certificate entries remain only for
the cases a variance cannot state.

### 7.6 Examples

**`Promise<number> ≤ Promise<number | string>`.** The declaration
$`v=(\mathsf{co})`$ is the entry $`\mathit{Promise}(a)\le\mathit{Promise}(b)`$
with $`\Pi=\{a\le b\}`$, checked once. Its members check as follows:

- **`then`** binds $`r`$ on the left and $`r'`$ on the right; the rule
  renames $`r'`$ to $`r`$. The callback parameter is contravariant: the
  target's `(x: b) => r` must be within the source's `(x: a) => r`, which
  needs $`a\le b`$. That is a hypothesis. The results are both
  $`\mathit{Promise}(r)`$, a subset.
- **`catch`** has results $`\mathit{Promise}(a\mid r)`$ and
  $`\mathit{Promise}(b\mid r)`$. These are an instance of $`f`$ itself, with
  premise $`a\mid r\le b\mid r`$, which is a table pair of $`\Delta_f`$.

That pair is valid: $`a`$ is opaque by hypothesis and $`r`$ is in the
target. The use is `Var`, whose one premise `number ≤ number | string` is a
subset; `Promise` is not unfolded. `Promise<never> ≤ Promise<number>` is the
same rule, with the empty union as the premise.

**The negative control** `Promise<number | string> ≤ Promise<number>` fails.
The `Var` premise `number | string ≤ number` is not derivable. Unfolding
directly fails at `then`'s callback parameter. No certificate exists.

**Writable positions.** In `interface Cell<T> { v: T }`, `v` is an invariant
field. The declaration $`(\mathsf{co})`$ is invalid, because the field needs
$`b\le a`$ too, so the request is refused unless the producer declares
$`(\mathsf{inv})`$. Then `Cell<A> ≤ Cell<B>` needs `A` and `B` to be
equivalent.

**`Pair`.** The result of `p.push("a")` is the image of `push`'s result at
`U := string`: $`\mathit{Pair}(\mathit{Lit}_{\mathit{push}}([\mathit{number}],[\mathit{string}]))`$
by substitution. The written return type `Pair<[number, string]>` lowers to
$`\mathit{Pair}(\mathit{Tup})`$, where $`\mathit{Tup}`$ is a nullary head for
the ground tuple `[number, string]`. The two tuple heads have different
templates, so no sharing identifies them. `Var` on `Pair`, which is
invariant through `push`'s mutable tuple, needs the two tuples both ways.
Each direction unfolds both tuple heads once to identical operands: a plain
core check. So `generic-growing-application-push` closes with `Var`, not
with lowering alone.

**Different heads.** `Promise<number> ≤ PromiseLike<number | string>` involves two
heads, so it takes a certificate entry
$`\mathit{Promise}(a)\le\mathit{PromiseLike}(b)`$ with $`a\le b`$, whose
check may use `Var` on both heads.

### 7.7 Required controls

Each is a request or certificate the checker must reject. No source
program reaches an invalid variance declaration, since lowering only
proposes valid ones, so the first three are forged-evidence tamper tests:

- a variance declaration its head's body contradicts (`Cell` declared
  $`\mathsf{co}`$; a callback parameter declared $`\mathsf{co}`$);
- a `Var` use whose premise fails;
- an instance whose hypothesis pair is missing from the table;
- a hypothesis that is false at the instance (`invalid-promise-covariance`);
- a writable field with a covariant hypothesis only;
- a family variable that also occurs in a claim;
- two entries that share a variable;
- quantified-α with a source binder free in the target.

A `none` declaration must also be checked: a parameter declared unused and
then read by the body is refused.

## 8. Lowering from source

**Specification; not yet in Lean.** Lowering happens in Lean. The parser
emits a declaration document (`tools/declaration-types.mts`); today
`Source/DeclarationGraph.lean` lowers it into a finite table, and it will
lower it into equations instead. The OCaml producer never builds a
declaration row: its inference already treats `Named` types as equations,
and only its encoding touches rows. Every source type becomes a union of
labels over one equation table. Heads are created per source declaration,
per unit and per source type-literal occurrence, never per instance. That
is what keeps the table finite for every family.

### 8.1 Heads

| Source | Head | Parameters | Binders | Template |
| --- | --- | --- | --- | --- |
| Primitive, literal, non-generic declaration | nullary | none | none | its row |
| Interface or class instance type `D<T⃗>`, merged declarations included | `D` | `T⃗` | none | clause row of its members, met with its bases (below) |
| Generic method `m<U⃗>` of `D<T⃗>` | `D.m` | `T⃗` | `U⃗` | scheme row; `D`'s template names `D.m(arg…)` |
| Any other scheme (a generic callable type) | hash-consed by template | the enclosing parameters it mentions | its own | scheme row |
| Generic function, closure, class or imported generic value (a **unit head**) | `f` | none | its binders | its scheme; a rigid binder is $`\mathsf{bound}(f,[],j)`$, a bounded one $`\mathsf{meet}(\mathsf{bound}(f,[],j),B)`$ |
| Type literal, tuple, array or function type occurring inside a template | `Lit` of that occurrence | the enclosing parameters and binders it mentions, in first-occurrence order | none | its row, with those as `arg` placeholders |
| Arrays | `Array`, one per readonly flag | the element union | none | the array clause over `arg 0` |
| The realm's array prototype | `ArrayProto` | none | none | `Equations.realm` |

A literal head lifts a literal over its free type variables, as closure
conversion lifts a function over its free variables. In
`push<U>(u: U): Pair<[T, U]>`, the tuple is
$`\mathit{Lit}(\mathsf{arg}\,0,\mathsf{local}\,0)`$ in the template of
`Pair.push`. Heads are keyed by source occurrence, and that is what makes
recursive aliases terminate (8.3). Lifting a literal over all its operands,
or keying it by instance, would loop. Literal heads with equal templates are
additionally shared (hash-consed); that sharing is only an efficiency
matter.

Parameters and binders have a kind: value or argument list (`pack`). The
receiver `self` inside `D`'s members is $`D(\mathsf{arg}\,0,\ldots)`$.

**Heritage.** `D`'s template is the source meet (3.3) of its own members
with each base's template instantiated at the placeholder arguments `D`
passes to it. This is finite because heritage is acyclic.

**Class generic methods.** The parser spells a class generic method's
binder as `"key"#k:null^0` (`tools/fragment-parse.mts`), a leftover of colours.
Lowering maps it to the owned binder $`\mathsf{bound}(C.m,\vec A,k)`$ and
the `^0` goes. Members declared in different heads then bind different
labels, so the positives that relate them (`generic-method-instances`,
`method-members`, `class-generic-method`) need quantified-α (section 6)
before the cutover.

A finite wire table is the nullary case of this lowering. Today's tables are
not: they contain shared parameter rows, meet rows and scheme rows whose
binders are shared, and templates forbid all three.

### 8.2 Type expressions

Lowering $`⟦\tau⟧`$ in a scope of enclosing parameters and binders:

| Source | Lowered |
| --- | --- |
| a declaration's type parameter | $`\mathsf{arg}\ i`$ |
| a method's or unit's type parameter | $`\mathsf{local}\ j`$, or the owned binder outside a template |
| `D<τ⃗>` | $`D(⟦\vec\tau⟧)`$; an omitted argument is its default, which may mention earlier parameters; one without a default is refused |
| `τ₁ \| τ₂` | the concatenation of the unions |
| `τ₁ & τ₂` | meet labels over the product of the operands' unions (3.3); an empty meet is refused |
| a literal | its `Lit` head applied to the parameters it mentions |
| an alias `A<τ⃗>` | its body lowered with `τ⃗` for its parameters (8.3) |
| `object`, callable atoms, index signatures, the `prototype` overlay | as today |
| `keyof`, indexed access, mapped, conditional, `typeof` types | refused, as today |

**Declared parameter bounds** are checked where the source or a claim writes
an application, and once per template with the parameters read as bounded
parameter labels. Applications created by instantiation are not checked
again: bounds carry no meaning, so an unchecked application is still
meaningful, only possibly unintended.

Library declarations (`Promise`, `PromiseLike`, `Array`, …) take the same
path. The budgeted memo, colours and `rigidClaim` expansion of
`DeclarationGraph.lean` are deleted.

### 8.3 Aliases and guardedness

An alias is inlined at each use: its body is lowered in place with the
arguments substituted. Inlining terminates when every cycle through aliases
passes through a constructor (a literal head or a declaration head), because
a literal head is keyed by its source occurrence, not by its instance. In

```ts
type Box<T> = { v: T; next: Box<[T]> };
```

`Box<number>` is $`\mathit{Lit}_1(\mathit{number})`$. The template of
$`\mathit{Lit}_1`$ inlines `Box<[T]>` to
$`\mathit{Lit}_1(\mathit{Lit}_2(\mathsf{arg}\,0))`$, where $`\mathit{Lit}_2`$
is the tuple `[T]`, and stops. An alias whose recursive reference is not
under a constructor, such as `type T<X> = X | T<[X]>`, is **unguarded** and
refused (today's "unguarded alias cycle"). The diagnostic is located at the
using unit, because a library alias's span is not a span in the checked
file. TypeScript rejects such an alias as circular.

## 9. Wire formats

**Specification; not yet implemented.** There are two wires, and they
change differently.

### 9.1 Source-claims document

The producer names labels in terms it can see. Lean-internal heads (method,
literal, unit, array heads) never appear on this wire. A label is a `types`
row index, or one of:

| Label | Spelling |
| --- | --- |
| application of declaration `k` (its position in the declaration document's `definitions`) | `{"decl": k, "args": [[L, …], …]}`, `args` left out when nullary, arity always full with defaults completed |
| intersection | `{"meet": [L, …]}` |
| array | `{"array": [L, …], "readonly": b}` |
| a binder in scope | `{"binder": "T"}` |

`types` keeps only the producer's content rows. The reserved empty rows, and
the `applications`, `arrays` and `meets` fields, are deleted, as are the
producer's `param` rows (replaced by `binder` labels) and its `expand_rigid`
mirror of Lean's `rigidClaim`.

### 9.2 Request protocol and evidence

The standalone request (`verifyJson`) decodes its graph, so there `equations`
replaces `types`:

```json
{
  "equations": [
    {
      "name": "Promise",
      "parameters": [{ "name": "T", "kind": "value" }],
      "body": [{ "refs": { "views": [["then", [{ "app": 7, "args": [[{ "arg": 0 }]] }]]] } }]
    }
  ]
}
```

Each entry has a `name` (diagnostic only), `parameters`, `binders` (left out
when none) and a `body` in the row format of
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md#request-fields). A body's operands
are lists of trees. Each tree form has exactly one spelling:

| Tree | Spelling |
| --- | --- |
| nullary application of head `h` | `h` |
| application with arguments | `{"app": h, "args": [[…], …]}`, `args` non-empty |
| owned parameter | `{"bound": h, "args": [[…], …], "slot": j}`, `args` left out when empty |
| meet | `{"meet": [L, …]}`: flat, at least two parts, canonical order |
| template placeholder (bodies only) | `{"arg": i}`, `{"local": j}` |
| family variable (inside its entry only) | `{"var": k}` |

Evidence, in both paths (the source path's evidence bundle and the protocol's
response), uses the same tree spelling and carries:

- the variance of every parameter of every head (`"co"`, `"contra"`,
  `"inv"`, `"none"`, no default) and the tables $`\Delta_h`$, as
  `[[h, [[A, B], …]], …]`, left out when empty;
- `inst` instances that name their images, checked by
  `substitutionTableOk`; the finite `table`, `domain` and `free` fields go;
- `core` certificates with `families`, each
  `{"source": L, "target": L, "variables": [kind, …], "hypotheses": [[x, y], …], "table": [[A, B], …]}`,
  left out when none; the present table becomes the variable-free entry;
- the `var` proof form, relating two applications of one head with one
  proof per non-`none` position (two for `inv`), citing the head's
  checked declaration.

Diagnostics show labels through a depth-bounded projection onto a finite
table, with names for applications (`Promise<number | R>`).

## 10. Acceptance statement

`SourceClaimJson.checkJson_safe` keeps its premise: the exact CLI success
condition. The variance check sits inside `checkRequests`, so it adds
nothing to that premise. The conclusion changes from
`RequestJson.graph r.toRequest` to `Equations.graph` of the checked
request's equations, which are built by lowering in memory, not decoded.
`checkRequests_safe_at` is restated the same way. The request protocol's
`verifyJson_safe` speaks of decoded equations. A finite table is the nullary
case, so the present theorems are instances of the new ones. The new rules
enter only through `Sub.sound`: quantified-α, family entries, `Var` and meet
labels. The trust surface gains nothing. Every semantic premise a new rule
uses is proved from the equations, never supplied by evidence.

## 11. Lean files and closing tests

- Proved: `Types/GraphRows.lean`, `Types/EquationGraphs.lean`,
  `Types/EquationSupport.lean`, `Types/EquationCongruence.lean`,
  `Types/EquationSubstitution.lean`, `Types/EquationCertificates.lean`.
- `generic-growing-application` verifies at the cutover. `-push`,
  `promise-covariance` and `invalid-promise-covariance` (rejected at its own
  obligation) move with `Var`. The Promise closing cases are listed in the
  [status table](DESIGN.md#status).
- At the cutover, every gap refused as an unsupported recursive generic
  contract is rerun and reclassified by its new first blocker: verified,
  blocked on `Var`, blocked on `then` through `PromiseLike` (Promise b), or
  a new located refusal.
