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

**Proof scope.** Sections 3 to 7 are proved in Lean, meet labels (3.3)
excepted. Meet labels and sections 8 to 10 are specifications: each rule
there needs its soundness lemma before any source program depends on it.
Source and CLI acceptance use only the finite checker; the rules of sections
6 and 7 are reached from the kernel's own checkers and tests. How far the work has
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
\mathrm{nf}\bigl(G(L_1)\wedge\cdots\wedge G(L_k)\bigr) & \text{no part is a parameter},\\
p\sqcap\vec q\sqcap\mathrm{nf}\bigl(\bigwedge_{L_i\notin P}G(L_i)\bigr) & P=\{p\}\cup\vec q\ \text{the parameter parts}.
\end{cases}
```

The parts are flat (no part is a meet), distinct, at least two, and in a
canonical order. No part is a scheme application: a meet with a generic
callable is refused, as it is now. The row is the
[normalized conjunction](POSITIVE-TYPES.md#conjunction-and-normalization) of
the parts' rows. That normalization concatenates operands and never meets
two operands, so a meet label's row names only labels its parts' rows name.
It creates no new application, and it cannot grow a family. The meaning is
the intersection of the parts' meanings (`normalize_sound`,
`meetLists_sound`, and the meet-row semantics for parameter parts):

```math
⟦\mathsf{meet}(L_1,\ldots,L_k)⟧^\eta=⟦L_1⟧^\eta\cap\cdots\cap⟦L_k⟧^\eta .
```

Templates get the corresponding placeholder former. Instantiation
distributes over unions, since intersection distributes over union:

```math
\mathsf{meet}(A_1,\ldots,A_k)=\textstyle\bigvee\{\,\mathsf{meet}(L_1,\ldots,L_k)\mid L_i\in A_i\,\},
```

and a single remaining part is that part. A meet whose normal form is
$`\bot`$ is refused where it is lowered, as today. The row reads its parts'
rows at the same level, not under a guard. This is well founded because
parts are applications or parameters, whose rows come from templates, never
from another meet.

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

The [quantified rule](POSITIVE-TYPES.md#core-tables) relates two scheme rows
only when they bind the same parameter rows. The finite lowering arranges
this by sharing binder rows by member key and colour. Equation binders are
owned, so the `then` of `Promise<number>` and the `then` of
`Promise<number | string>` bind different labels. The rule therefore renames
the target's binders to the source's:

```math
\frac{\begin{array}{c}
i=(\vec p;\Sigma;\beta;\Sigma_\ldots)\qquad j=(\vec q;\Sigma';\beta';\Sigma'_\ldots)\qquad
|\vec p|=|\vec q|\qquad \vec p,\ \vec q\ \text{each distinct}\qquad \forall k.\ \mathrm{kind}(p_k)=\mathrm{kind}(q_k)\\
\forall (p_k,B)\in\beta.\ \exists (q_k,B')\in\beta'.\ \Delta(B',B)\qquad
\bigl(\mathrm{FV}(\Sigma';\Sigma'_\ldots)\setminus\vec q\bigr)\cap\vec p=\emptyset\\
\Delta\vdash\mathsf{arrs}(\Sigma;\Sigma_\ldots)\sqsubseteq\mathsf{arrs}(\Sigma';\Sigma'_\ldots)[\vec q:=\vec p]
\end{array}}
{\Delta\vdash i\sqsubseteq_\forall j}\ \mathsf{Quantified}\text{-}\alpha
```

The substitution is the one of section 4.3, computed by the checker, not
supplied. The freshness premise uses the computed support: no source binder
is free in the target's signatures, unless it is also a target binder. Each
source bound is matched by the target's bound on the renamed binder, which
must be within it. Bounds are read outside both schemes, so this premise is
an ordinary one, read at the table's assignment. Equal bounds are the case
$`B'=B`$, a subset.

The substitution and the support belong to the representation. A graph
supplies them as a `Renaming`: the executable operations with their laws,
`substitute_meaning` and `agree_free`, proved by verified code and never read
from a certificate. Equation graphs have one (`Equations.renaming`, from
`Label.substitute` and `Label.free`). A finite table has none. It keeps the
same-binder rule, the case $`\vec q=\vec p`$, and the checked rule is the
disjunction of the two (`SchemeCoversAlpha`).

**Soundness.** Take a member of $`i`$ and an instance $`\vec X`$ within
$`\beta'`$. Each source bound is matched by a target bound within it, so
$`\vec X`$ is within $`\beta`$ at $`\vec p`$. The member meets $`\Sigma`$ at
$`\eta[\vec p:=\vec X]`$, and the premise gives the renamed target
signatures there. At
$`\zeta=\eta[\vec p:=\vec X][\vec q:=\vec X]`$ every parameter means its
replacement, so substitution gives
$`⟦\Sigma'[\vec q:=\vec p]⟧^{\eta[\vec p:=\vec X]}=⟦\Sigma'⟧^{\zeta}`$.
Freshness makes $`\zeta`$ agree with $`\eta[\vec q:=\vec X]`$ on the support
of $`\Sigma'`$:

```math
⟦\Sigma'[\vec q:=\vec p]⟧^{\eta[\vec p:=\vec X]}=⟦\Sigma'⟧^{\eta[\vec q:=\vec X]} ,
```

which is what membership in $`j`$ requires. The table premise is read at the
instance's assignment. It holds there because every entry holds at every
assignment, or, inside a family (section 7), at every assignment satisfying
the family's hypotheses; no scheme binds a family variable, so those survive.
The restriction is the one the existing rule takes from
[Pierce 1994](REFERENCES.md#pierce-1994): target binders are rigid. Bounds
are compared contravariantly, by a premise, as in full F<: but on one fixed
pairing of binders, so the check stays a check.

Lean: `Renaming`, `SchemeRenames`, `SchemeCoversAlpha`, `renamed_meaning`,
`renames_sound`, `alpha_sound` (`Types/PositiveRules.lean`);
`Equations.renaming` (`Types/EquationFamilies.lean`).

## 7. Family subtyping

Relating
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
variable-free entry, or as a pair in its table. An entry also names the
instances its premises use (7.2): an entry's index and the types its
variables are instantiated at.

**Variables are labels of their own.** On an equation graph a variable is
`Tree.var owner slot kind` (`Label.familyVar`), a parameter row of the kind
it carries, not a parameter owned by an application. Every owned parameter
is a binder of its application's scheme, and entering a scheme reassigns its
binders, while the soundness proof (7.4) needs every hypothesis to survive
entering any scheme. A reserved head per family would make its variables
the binders of that head's scheme. With labels of their own, no scheme binds
a variable (`Equations.scheme_binders`), and no template can contain one,
since a variable is not a lexical tree. The checker enforces the rest of the
discipline: each variable is a family-variable label of the renaming, each
hypothesis relates two variables of its own entry, no variable belongs to
two entries (the declarations of 7.5 included), and the claim mentions no
variable anywhere in its syntax (`VariablesOk`, `variablesOk`, `claimOk`).
A graph without a renaming admits no variable.

Lean: `Entry`, `VariablesOk`, `variablesOk`, `claimOk`
(`Types/PositiveRules.lean`, `Types/PositiveCertificates.lean`);
`Tree.var`, `Label.familyVar` (`Types/EquationGraphs.lean`).

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

As checked, an instance is a variable assignment $`\sigma`$ of kinded types:
$`l`$ is a label of the source goal under $`\sigma`$, every label of the
target goal under $`\sigma`$ is in $`B`$, and every hypothesis of $`f'`$,
under $`\sigma`$, is discharged in $`f`$ as above. One type per variable
makes shared positions equal by construction. The instance is one the entry
names, or one `Var` proposes (7.5); a proposal is only a candidate, checked
the same way.

Lean: `Discharge`, `InstanceOk`, `Prem` (`Types/PositiveRules.lean`).

### 7.3 Checking an entry

Entry $`f`$ is **valid** when its goal and every pair of $`\Delta_f`$ meet
the three [core conditions](POSITIVE-TYPES.md#core-tables), with two changes:

- **Opaque rows.** A variable $`x`$ of the source may instead be covered by a
  hypothesis $`(x\le y)\in\Pi_f`$ with $`y`$ in the target.
- **Coverage** reads operand premises through $`\Delta_f\Vdash\cdot`$, and
  scheme rows are related by quantified-α.

Everything else is unchanged: the same kinds, clause coverage, known rows
and instance checks. The three conditions are one definition for a core
table and for an entry (`PairOk`), and the checker decides them with checked
arrow evidence (`checkEntries`). It is complete for the declarative rule
(`familyValid_iff_checked`), as the core checker is for the core rule. An invariant field still needs $`\Delta^{\pm}`$, that
is, both directions. So a family whose declaration has a writable field at
$`T`$ is valid only with $`a`$ shared, or with both $`a\le b`$ and
$`b\le a`$. Variance is never read from TypeScript. The producer proposes
$`\Pi_f`$ (for example by trying covariance and weakening to invariance on
failure), and the checker checks it.

Lean: `PairOk`, `OpaqueFamily`, `FamilyValid`, `checkEntries`,
`checkEntries_complete`, `familyValid_iff_checked`
(`Types/PositiveRules.lean`, `Types/PositiveCertificates.lean`).

### 7.4 Soundness

Write $`\eta\models_n\Pi`$ when $`⟦x⟧^\eta_j\subseteq⟦y⟧^\eta_j`$ for every
hypothesis and every level $`j\le n`$, in both components, and
$`\eta\models^{\mathsf v}_n\Pi`$ when this holds below $`n`$ and, at $`n`$,
for values. The theorem proved:

```math
\begin{aligned}
&\forall n.\ \forall f\in F.\ \forall\eta.\
\eta\models_n\Pi_f\ \Longrightarrow\
\forall (A,B)\in\Delta_f\cup\{\mathrm{goal}_f\}.\ ⟦A⟧^\eta_n\subseteq⟦B⟧^\eta_n,\\
&\forall n.\ \forall f\in F.\ \forall\eta.\
\eta\models^{\mathsf v}_n\Pi_f\ \Longrightarrow\
\forall (A,B)\in\Delta_f\cup\{\mathrm{goal}_f\}.\ ⟦A⟧^\eta_n\subseteq⟦B⟧^\eta_n\ \text{for values.}
\end{aligned}
```

The proof is by strong induction on $`n`$, the shape of `Core.mixed_sound`.
At each level it proves values first, then argument lists:

- **Values** at $`n`$ read premises below $`n`$. A table pair holds there by
  induction, since the hypotheses hold at every $`j<n`$. A subset holds
  outright. A variable of the source that is opaque by hypothesis holds at
  $`n`$ because $`\eta\models^{\mathsf v}_n\Pi_f`$.
- **Argument lists** at $`n`$ read the element contracts of packs, value
  premises at $`n`$ itself. They follow from the values just proved, for
  every entry and every assignment.
- **Family instance.** Instantiate $`f'`$ at
  $`\eta'=\eta[\vec x:=⟦\vec X⟧^\eta,\vec y:=⟦\vec Y⟧^\eta]`$. Every
  parameter means its replacement there, so each hypothesis of $`f'`$ means
  its discharged pair, which holds by induction, as a subset, or as a
  hypothesis of $`f`$. Read below $`n`$, the pair holds in both components.
  Read at $`n`$ by an argument list, it holds for values by the first step.
  So $`\eta'\models\Pi_{f'}`$ in the form the level needs, the goal of
  $`f'`$ holds at $`\eta'`$, and substitution (section 4.3) turns it into
  $`⟦g(\vec X)⟧^\eta\subseteq⟦g'(\vec Y)⟧^\eta`$. When $`f'=f`$ and
  $`\vec X`$ mentions $`f`$'s own variables, the substitution is still
  simultaneous and the theorem applies.
- **Quantified-α** as in section 6. No scheme binds a variable, so the
  hypotheses survive the reassignment.

The second statement is the refinement the level bookkeeping needs. An
argument-list premise at $`n`$ may be an instance, and its hypotheses are
then discharged at $`n`$ only for values. The first statement is the one
the claims use.

A variable-free entry has no hypotheses, which recovers the existing core
theorem: `Core.mixed_sound` is the one-entry case of the same induction
(`pairs_sound`), premises read through its table. Entries may draw on base
entries proved sound before, as a certificate's entries draw on the
variance declarations (7.5). A claim is a pair of a variable-free entry of
the certificate, sound at every assignment.

Lean: `MixedLe`, `HypsHold`, `HypsHoldValues`, `pair_values_sound`,
`pair_arguments_sound`, `pairs_sound`, `Core.mixed_sound`,
`assignment_images`, `InstanceOk.transport`, `EntrySound`, `family_sound`,
`family_entries_sound`, `family_closed_sound` (`Types/PositiveRules.lean`);
`checkFamilyUsing`, `checkFamilyUsing_sound` (`Types/PositiveCertificates.lean`).

### 7.5 Variance declarations

Each head $`h`$ of arity $`n`$ declares a variance
$`v_i\in\{\mathsf{co},\mathsf{contra},\mathsf{inv},\mathsf{none}\}`$ for each
parameter. The declaration stands for the family entry

```math
f_h=\bigl(\,h(x_1,\ldots,x_n)\le h(y_1,\ldots,y_n),\ \Pi_h,\ \Delta_h\,\bigr),
\qquad
\Pi_h=\{x_i\le y_i\mid v_i=\mathsf{co}\}\cup\{y_i\le x_i\mid v_i=\mathsf{contra}\},
```

where $`\mathsf{inv}`$ states both $`x_i\le y_i`$ and $`y_i\le x_i`$, and
$`\mathsf{none}`$ imposes nothing. $`\Delta_h`$ is evidence the producer
proposes. The variables are $`h`$'s own labels, $`x_i`$ at slot $`2i`$ and
$`y_i`$ at slot $`2i+1`$, of the declared kind: a declaration states each
parameter's kind as well as its variance.

**Checked once.** The declarations of all heads form one set of entries,
checked together by 7.3 when the equations are accepted, before any claim
is read. A declaration may rely on the others, and on itself: `catch`'s
$`\mathit{Promise}(a\mid r)\le\mathit{Promise}(b\mid r)`$ is discharged by
$`f_{\mathit{Promise}}`$. If a declaration is invalid, the request is
refused with a located diagnostic naming the head and the parameter. The
producer proposes variances, for example by starting from $`\mathsf{co}`$ or
$`\mathsf{none}`$ and weakening to $`\mathsf{inv}`$ on failure. They are
never read from TypeScript, whose measured variance treats method
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
an instance's hypotheses are: a table pair, a subset or a hypothesis. `Var`
proposes the instance of $`f_h`$ at $`\vec x:=\vec A`$, $`\vec y:=\vec B`$
for a label $`h(\vec A)`$ of the source and a label $`h(\vec B)`$ of the
target (`varGen`), and it is checked as any instance. As a structural rule,
the premises are derivations, one per hypothesis of $`f_h`$, in order: two
for an invariant position.

An invariant position has two variables with two-way hypotheses, not one
shared variable. A shared variable makes the entry trivial, but using it
needs a congruence step: $`h(\ldots A_i\ldots)`$ and $`h(\ldots B_i\ldots)`$
have equal meanings because $`A_i`$ and $`B_i`$ do. Inside an entry those
equal meanings hold only up to the current level. At the argument-list step
of 7.4 they would need the argument-list component of a table pair at
$`n`$, the very statement being proved. Two variables need no congruence:
the instance assigns each separately. A writable field is still validated
with both hypotheses, since $`\Delta^{\pm}`$ holds by one hypothesis each
way. A bound mentioning the parameter is related through the hypotheses as
well, since quantified-α compares bounds by a premise.

**Soundness.** An instance of a valid $`f_h`$, by 7.4 and substitution
(4.3). A derivation holds at every level, so `Var` is sound as a structural
rule too.

Lean: `Variance`, `Header.variance` (`Types/EquationGraphs.lean`);
`varianceEntry`, `varianceEntries`, `varGen`, `Equations.checkVariance`,
`Equations.varianceRefused`, `Variances`, `Variances.sound`,
`Equations.checkVar`, `Equations.checkVar_sound`, `Equations.checkFamily`,
`Equations.checkFamily_sound` (`Types/EquationFamilies.lean`);
`entry_instance_sound`, `checkEntryInstanceUsing_sound`
(`Types/PositiveRules.lean`, `Types/PositiveCertificates.lean`).

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
`U := string`: $`\mathit{Pair}(\mathit{Lit}(\mathit{number},\mathit{string}))`$
by substitution. The written return type `Pair<[number, string]>` lowers to
the same label when literal heads are shared (section 8.2), and then no
subtyping step is needed. When they are not shared, a certificate entry
relates the two tuple heads both ways, and `Var` on `Pair`, invariant
through `push`'s tuple, relates the results.

**Different heads.** `Promise<number> ≤ PromiseLike<number | string>` is not
same-head, so it takes a certificate entry
$`\mathit{Promise}(a)\le\mathit{PromiseLike}(b)`$ with $`a\le b`$, whose
check may use `Var` on both heads.

These examples, `Pair` aside, are concrete checks in
`Tests/EquationFamilyTests.lean`, together with the controls of 7.7.
`Pair` turns on lowering (section 8.2), which is not in Lean.

### 7.7 Required controls

Each is a request or certificate the checker must reject:

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
then read by the body is refused. Each control is a rejected check in
`Tests/EquationFamilyTests.lean`. A refused declaration is located at its
head (`Equations.varianceRefused`).

## 8. Lowering from source

**Specification; not yet in Lean or OCaml.** Every source type becomes a
union of labels over one equation table. Heads are created per source
declaration and per source type-literal occurrence, never per instance. That
is what keeps the table finite for every family.

### 8.1 Heads

| Source | Head | Parameters | Binders | Template |
| --- | --- | --- | --- | --- |
| Primitive, literal, non-generic declaration | nullary | none | none | its row |
| Interface or class instance type `D<T⃗>`, merged declarations included | `D` | `T⃗` | none | clause row of its members |
| Generic method `m<U⃗>` of `D<T⃗>` | `D.m` | `T⃗` | `U⃗` | scheme row; `D`'s template names `D.m(arg…)` |
| Type literal, tuple, array or function type occurring inside a template | `Lit` of that occurrence | the enclosing parameters and binders it mentions, in first-occurrence order | none | its row, with those as `arg` placeholders |

The last row lifts a literal over its free type variables, as closure
conversion lifts a function over its free variables. In
`push<U>(u: U): Pair<[T, U]>`, the tuple is $`\mathit{Lit}(\mathsf{arg}\,0,\mathsf{local}\,0)`$
in the template of `Pair.push`. Literal heads with equal templates, up to
parameter numbering, are shared (hash-consed). Sharing is an efficiency and
completeness matter only: two heads with equal templates are two equations
with equal meanings, and section 7 relates them either way.

A finite table row is the nullary case. The present `types` array is exactly
the list of nullary heads, which is why there is one representation (section
9).

### 8.2 Type expressions

Lowering $`⟦\tau⟧`$ in a scope of enclosing parameters and method binders:

| Source | Lowered |
| --- | --- |
| a declaration's type parameter | $`\mathsf{arg}\ i`$ |
| a method's type parameter | $`\mathsf{local}\ j`$ |
| `D<τ⃗>` | $`D(⟦\vec\tau⟧)`$; an omitted argument is its default, and one without a default is refused |
| `τ₁ \| τ₂` | the concatenation of the unions |
| `τ₁ & τ₂` | meet labels over the product of the operands' unions (3.3) |
| a literal | its `Lit` head applied to the parameters it mentions |
| an alias `A<τ⃗>` | its body lowered with `τ⃗` for its parameters (8.3) |
| `keyof`, indexed access, mapped, conditional, `typeof` types | refused, as today |

Library declarations (`Promise`, `PromiseLike`, `Array`, …) take the same
path; the budgeted `DeclarationGraph` path is retired.

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
refused with a located diagnostic. TypeScript rejects such an alias as
circular.

## 9. Wire format

**Specification; not yet implemented.** The request's `types` field is
replaced by `equations`. Per the protocol's rules, the old field is removed,
not kept beside the new one.

```json
{
  "equations": [
    {
      "name": "Promise",
      "parameters": [{ "name": "T", "kind": "value", "variance": "co" }],
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

Every parameter states its `variance` (`"co"`, `"contra"`, `"inv"` or
`"none"`), with no default. The request also carries `variance`: the
evidence tables $`\Delta_h`$ for the heads whose declaration needs pairs
beyond hypotheses and subsets, as `[[h, [[A, B], …]], …]`, left out when
empty.

Claims, results and inputs are lists of closed labels. Validation checks
scope, arity, kinds, constructor-headedness, a scheme's binders, the meet
normal form and the variable discipline of section 7.1. Anything else is
refused.

In certificates:

- An `inst` instance names its images and is checked by
  `substitutionTableOk`. The finite `table`, `domain` and `free` fields go.
- `core` carries `families`, each
  `{"source": L, "target": L, "variables": [kind, …], "hypotheses": [[x, y], …], "table": [[A, B], …]}`,
  left out when none. Same-head pairs use `Var` and need no entry. The
  present table becomes the variable-free entry.
- A structural proof form `var` relates two applications of one head, with
  one proof per non-`none` position (two for `inv`).

## 10. Acceptance statement

`SourceClaimJson.checkJson_safe` keeps its statement. The graph it speaks
of becomes `Equations.graph` of the decoded equations instead of
`RequestJson.tableGraph`. A finite table is the nullary case, so the present
theorem is an instance of the new one. Its premise adds that the variance
declarations were checked. The new rules enter only through `Sub.sound`:
quantified-α, family entries, `Var` and meet labels. So the proof
changes only at subtyping soundness and decoding. The trust surface gains
nothing. Equations are decoded and checked, and every semantic premise a new
rule uses is proved from the equations, never supplied by a certificate.

## 11. Lean files and closing tests

- Proved: `Types/GraphRows.lean`, `Types/EquationGraphs.lean`,
  `Types/EquationSupport.lean`, `Types/EquationCongruence.lean`,
  `Types/EquationSubstitution.lean`, `Types/EquationCertificates.lean`,
  `Types/EquationFamilies.lean`; the generic rules of sections 6 and 7 in
  `Types/PositiveRules.lean` and `Types/PositiveCertificates.lean`.
- Kernel tests: `Tests/EquationFamilyTests.lean`.
- Closing cases: `generic-growing-application` and
  `generic-growing-application-push` verify unchanged; `promise-covariance`
  verifies and `invalid-promise-covariance` is rejected at its own
  obligation. The Promise closing cases are listed in the
  [status table](DESIGN.md#status).
