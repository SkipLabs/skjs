# Recursive generic types as equations

Generic declarations such as TypeScript's `Promise` define infinite families
of types that no finite type graph can present. This section describes how
the verifier represents them: each declaration is a parameterized equation,
each type is a finite term applying an equation to arguments, and a check
unfolds a term one step, only when it reads it. The meaning of types is
unchanged: equations present graphs to the step-indexed semantics of
[SEMANTICS](SEMANTICS.md) and [POSITIVE-TYPES](POSITIVE-TYPES.md). What they
add is a finite syntax for the checks that relate members of a family:
substitution for instantiation, and parametric entries for subtyping.

Sections 2 to 4 are mechanized in Lean (section 8). The lowering of section 5
is untrusted: the checker validates everything it proposes.

## 1. The problem

A finite type graph presents a *regular* type: finitely many distinct types,
recursion by reference back to a row. Many generic types are regular at each
instance: the rows of `List<number>` mention only `List<number>` and
`number`. Others are not:

```ts
interface Promise<T> {
  then<R>(f: (x: T) => R): Promise<R>;
  catch<R>(f: (e: unknown) => R): Promise<T | R>;
}
```

Unfolding `Promise<number>` reaches `Promise<number | R>` through `catch`,
whose own `catch` reaches `Promise<number | R | R′>`, and so on. Every member
mentions a larger one; the unfolding has infinitely many distinct subtrees.
Such definitions are *non-regular* ([Solomon 1978](REFERENCES.md#solomon-1978)).
A presentation that enumerates instances can only stop somewhere: past a
budget it must refuse the declaration, since reading the tail as `unknown`
would be unsound.

The semantics does not need finiteness. A type graph may have any set of
labels, and a type's meaning is a guarded fixed point, not an enumeration of
rows. What must be finite is what a check inspects. The design follows:
name each member by a finite term, compute its row on demand, and relate
members by rules that inspect finitely many rows.

## 2. Equations

### 2.1 Syntax

A **signature** assigns each head $`h`$ an arity $`n_h`$ and a list of local
binders with their kinds, value or argument list. A **template** $`E_h`$ is a
row (a union of clauses, or a scheme) whose operands are trees over
applications, owned parameters, and the placeholders
$`\mathsf{arg}\,i`$ ($`i<n_h`$) and $`\mathsf{local}\,j`$. Only a scheme
template has locals, and it quantifies exactly them. A **label** is a closed
tree:

```math
\begin{aligned}
L &::= h(A_1,\ldots,A_{n_h}) \;\mid\; \mathsf{bound}(h,\vec A,j) \;\mid\; \mathsf{meet}(L_1,\ldots,L_k)\\
A &::= \{L_1,\ldots,L_m\}\qquad\text{a union}
\end{aligned}
```

An application's arguments are unions. A binder of a scheme is not a free
name but a parameter **owned** by the application that introduces it:
$`\mathsf{bound}(h,\vec A,j)`$ contains its owner's arguments, so it cannot
occur in them.

### 2.2 Meaning

Equations present the graph

```math
G\bigl(h(\vec A)\bigr)=E_h[\vec A/\mathsf{arg},\ \mathsf{bound}(h,\vec A,\cdot)/\mathsf{local}],
\qquad
G\bigl(\mathsf{bound}(h,\vec A,j)\bigr)=\mathsf{param}_{\mathrm{kind}_h(j)} .
```

Instantiation replaces placeholders throughout the finite template and
leaves every application in it unexpanded, so a row is computed in time
linear in its template. The meaning $`⟦L⟧^\eta`$ at a parameter assignment
$`\eta`$ is the existing guarded fixed point over $`G`$. Because binders are
owned, nested instantiation never captures: an application's binders are
fresh for its arguments by construction, and no renaming is ever needed.

A meet means the intersection of its parts:

```math
⟦\mathsf{meet}(L_1,\ldots,L_k)⟧^\eta=⟦L_1⟧^\eta\cap\cdots\cap⟦L_k⟧^\eta .
```

Its row is the exact normalized conjunction of its parts' clauses, with its
parameter and scheme parts kept as parts, read at the meet's own level. This
is well founded because a part is never a meet. The meet must be exact.
Instantiating $`\mathsf{meet}(\mathsf{arg}\,0,M)`$, or substituting for a
parameter part, turns a meet over a parameter into a meet over whatever
replaces it. The lemmas of section 3 hold only if a meet's meaning is a
function of its parts' meanings, and the parameter case fixes that function
as intersection. Instantiation distributes over unions:
$`\mathsf{meet}(A_1,\ldots,A_k)=\bigcup\{\mathsf{meet}(L_1,\ldots,L_k)\mid L_i\in A_i\}`$.

## 3. Metatheory

Three lemmas let a check work on finite syntax while the meaning is a fixed
point over infinitely many rows. Each is proved for values and argument
lists together.

**Lemma 1 (support).** Let $`\mathrm{FV}(L)`$ be the owned parameters
occurring in $`L`$, computed on the tree. If $`\eta`$ and $`\theta`$ agree on
$`\mathrm{FV}(L)`$, then $`⟦L⟧^\eta=⟦L⟧^\theta`$.

*Proof sketch.* The graph semantics already has an independence theorem
parameterized by local closure conditions on a support map. For equation
graphs these conditions hold by induction on the template, so no family is
enumerated. $`\square`$

**Lemma 2 (congruence).** If $`⟦A_i⟧^\eta=⟦B_i⟧^\theta`$ for every $`i`$, then
$`⟦h(\vec A)⟧^\eta=⟦h(\vec B)⟧^\theta`$.

*Proof sketch.* By induction on the level $`n`$:
- *Value rows* at $`n`$ read their operands below $`n`$. Operands are
  instantiated templates, so they agree by an inner induction on the
  template, and meets agree part by part at the same level.
- *Quantified signatures* compare after assigning matching families to the
  two applications' owned binders.
- *Argument lists* at $`n`$ use the values at $`n`$ just established.

The statement is about arbitrary environments, which is what lets the two
applications own different binders. $`\square`$

**Lemma 3 (substitution).** For simultaneous substitution of unions
$`\vec U`$ for parameters $`\vec b`$ of matching kinds,

```math
⟦L⟧^{\eta[\vec b\mapsto⟦\vec U⟧^\eta]}=⟦L[\vec b:=\vec U]⟧^\eta .
```

*Proof sketch.* Substitution traverses the finite argument syntax and never a
row. An application's meaning depends on its arguments' meanings only
(Lemma 2), so the statement follows by structural induction on $`L`$; meets
distribute. Simultaneity matters: the case $`a:=a\cup r`$ is covered, and
section 4.2 uses it. $`\square`$

The lemmas replace enumeration where the checker needs it. Instantiating a
generic member at a call is checked by recomputing the substitution of
Lemma 3 on the signature's syntax; the image is correct by that lemma. The
checker is stated once over an interface, an image check plus a proof that
it yields correct images, of which this and the former finite-closure check
are two instances. The proofs of expression typing, control flow and
evidence search are stated over that interface too.

## 4. Subtyping

Subtyping between recursive types is checked coinductively: a certificate
supplies a finite table of pairs, and the checker verifies that each pair's
clauses are covered, assuming the pairs themselves for the operands, which
are read one level lower
([Amadio and Cardelli 1993](REFERENCES.md#amadio-and-cardelli-1993),
[Brandt and Henglein 1998](REFERENCES.md#brandt-and-henglein-1998),
[POSITIVE-TYPES: core tables](POSITIVE-TYPES.md#core-tables)). Two things
break this for non-regular families: binders differ between members, and
the table needed is infinite.

### 4.1 Renaming binders

Two applications of one head own different binders. The `then` of
`Promise<number>` binds another label than the `then` of
`Promise<number | string>`. Scheme coverage therefore renames the target's
binders to the source's with the substitution of Lemma 3:

```math
\frac{\begin{array}{c}
i=\forall\vec p{\le}\beta.\ \Sigma\qquad j=\forall\vec q{\le}\beta'.\ \Sigma'\qquad
|\vec p|=|\vec q|,\ \text{kinds equal}\\
\forall k.\ \beta'_k\le\beta_k\qquad
\vec p\cap\bigl(\mathrm{FV}(\Sigma')\setminus\vec q\bigr)=\emptyset\qquad
\Delta\vdash\Sigma\sqsubseteq\Sigma'[\vec q:=\vec p]
\end{array}}
{\Delta\vdash i\sqsubseteq_\forall j}
```

*Soundness.* Take a member of $`i`$ and $`\vec X`$ within $`\beta'`$, hence
within $`\beta`$. The member meets $`\Sigma`$ at $`\eta[\vec p:=\vec X]`$,
and hence $`\Sigma'[\vec q:=\vec p]`$ there. By Lemma 3 and the freshness
premise, that is $`\Sigma'`$ at $`\eta[\vec q:=\vec X]`$, which is membership
in $`j`$. Target binders are rigid and bounds compared by a premise on one
fixed pairing, which keeps the rule a check
([Pierce 1994](REFERENCES.md#pierce-1994)).

### 4.2 Parametric entries

With renaming, `Promise<number> ≤ Promise<number | string>` still needs
`Promise<number | r> ≤ Promise<number | string | r>` for `catch`'s result,
then a pair with one more binder, without end. These pairs differ only in
their arguments. So an entry of the table may quantify over them.

A **parametric entry** is $`f=(h(\vec x)\le h'(\vec y),\ \Pi_f,\ \Delta_f)`$:
- $`\vec x,\vec y`$ are *variables*, parameter labels that no equation, claim
  or other entry mentions and no scheme binds;
- $`\Pi_f`$ is a finite set of *hypotheses* $`u\le v`$ between variables;
- $`\Delta_f`$ is a finite table of pairs over the variables and the binders
  reached by unfolding.

An ordinary table is the entry without variables. Inside $`f`$, an operand
premise $`A\sqsubseteq B`$ holds if it is a pair of $`\Delta_f`$, or if every
label of $`A`$ is:
- in $`B`$; or
- a variable below a member of $`B`$ by a hypothesis; or
- an **instance** $`g(\vec X)`$ of an entry $`g(\vec x')\le g'(\vec y')`$ with
  $`g'(\vec Y)\in B`$, each hypothesis of that entry, at $`\vec X,\vec Y`$,
  being a pair of $`\Delta_f`$, a subset, or a hypothesis of $`\Pi_f`$.

Discharging an instance is not recursive: its hypotheses are table pairs, not
derivations. An entry is **valid** when its goal and its pairs satisfy the
core conditions under these premises, with a variable of the source also
covered by a hypothesis. A meet's parameter parts are read through the
hypotheses as well: under $`x\le y`$, $`\mathsf{meet}(x,B)`$ is below $`y`$
and below $`\mathsf{meet}(y,B)`$, while a clause part is never covered by a
hypothesis.

**Theorem 1 (soundness of entries).** Let $`\eta\models_n\Pi`$ mean that
every hypothesis holds at $`\eta`$ at every level $`j\le n`$. For a set of
valid entries, for every $`n`$, every entry $`f`$ and every $`\eta`$ with
$`\eta\models_n\Pi_f`$, every pair $`(A,B)`$ of $`\Delta_f`$ and the goal of
$`f`$ satisfy $`⟦A⟧^\eta_n\subseteq⟦B⟧^\eta_n`$.

*Proof sketch.* By strong induction on $`n`$; at each level, values first,
then argument lists.
- **Value premises** are read below $`n`$: table pairs hold there by
  induction, and hypotheses by assumption.
- **An instance** is the goal of its entry at
  $`\eta'=\eta[\vec x':=⟦\vec X⟧^\eta,\vec y':=⟦\vec Y⟧^\eta]`$. Its hypotheses
  mean their discharging pairs there, so $`\eta'\models\Pi`$ and induction
  applies; Lemma 3 turns the goal at $`\eta'`$ back into
  $`⟦g(\vec X)⟧^\eta\subseteq⟦g'(\vec Y)⟧^\eta`$. An entry may use itself,
  with $`\vec X`$ mentioning its own variables, since substitution is
  simultaneous.
- **Renaming** reassigns scheme binders only, and no scheme binds a
  variable, so the hypotheses survive.
- **Argument lists** at $`n`$ read element contracts, which are value
  premises at $`n`$ itself. An instance used there has its hypotheses
  discharged at $`n`$ only for values. The theorem is therefore proved
  together with a second form whose hypotheses hold below $`n`$ and, at
  $`n`$, for values; this refinement is what the bookkeeping needs.

$`\square`$ Without variables this is the existing core theorem.

### 4.3 Variance

Covariance of `Promise` is a fact about its declaration, not about any use,
so it is established once. Each head declares a variance per parameter,
$`v_i\in\{\mathsf{co},\mathsf{contra},\mathsf{inv},\mathsf{none}\}`$, which
stands for the entry

```math
h(\vec x)\le h(\vec y),\qquad
\Pi_h=\{x_i\le y_i\mid v_i\in\{\mathsf{co},\mathsf{inv}\}\}\cup\{y_i\le x_i\mid v_i\in\{\mathsf{contra},\mathsf{inv}\}\}.
```

The declarations of all heads are checked together, once per document, and
may use one another and themselves. A use then needs no unfolding:

```math
\frac{\forall i.\ \ A_i\le B_i\ \text{if}\ v_i\in\{\mathsf{co},\mathsf{inv}\}\qquad B_i\le A_i\ \text{if}\ v_i\in\{\mathsf{contra},\mathsf{inv}\}}
{h(\vec A)\le h(\vec B)}\ \mathsf{Var}
```

`Var` is sound as an instance of a valid declaration (Theorem 1, Lemma 3).
An invariant position uses two variables related both ways, not one shared
variable. Sharing would need Lemma 2 inside the induction, at the level being
proved. Variance is never read from TypeScript, whose method parameters are
bivariant. A writable field needs both directions, so a head with one is
valid only when declared invariant there.

Relations between different heads, such as `Promise<T> ≤ PromiseLike<T>`,
are the certificate's own parametric entries, checked by the same rule.

### 4.4 Example

`Promise` is declared $`(\mathsf{co})`$. Its entry
$`\mathit{Promise}(a)\le\mathit{Promise}(b)`$ under $`a\le b`$ checks as
follows:
- **`then`:** its binders are renamed. The callback `(x: b) => r` must be
  within `(x: a) => r`, which is the hypothesis. Both results are
  $`\mathit{Promise}(r)`$.
- **`catch`:** its results are $`\mathit{Promise}(a\cup r)`$ and
  $`\mathit{Promise}(b\cup r)`$, an instance of the entry itself whose
  hypothesis $`a\cup r\le b\cup r`$ is a table pair. That pair is valid
  because $`a`$ is below $`b`$ by the hypothesis and $`r`$ is shared.

`Promise<number> ≤ Promise<number | string>` is then `Var` with the premise
`number ≤ number | string`. The converse fails at its premise, and unfolding
fails at `then`'s callback, so no certificate exists. For
`interface Cell<T> { v: T }` the covariant declaration is invalid, and
`Cell<A> ≤ Cell<B>` requires `A` and `B` equivalent.

## 5. From source

Lowering turns the parser's declaration document into equations. It creates
heads per source construct, never per instance:
- **Declarations:** a declaration whose type is an object type, or that has
  bases, is a head with its type parameters as parameters.
- **Methods:** each generic method is a head owning the method's binders.
- **Units:** each generic function, closure, class or imported generic value
  is a head whose binders are the unit's.
- **Literals:** each occurrence of an object, function, tuple or array type
  inside a template is a head lifted over the enclosing parameters and
  binders it mentions, as closure conversion lifts a function over its free
  variables.

Primitives are nullary heads, and equal literal templates are shared. The
number of heads is therefore bounded by the size of the source, whatever the
families it defines. `Pair<T>`'s `push<U>(): Pair<[T, U]>` lowers its result
to $`\mathit{Pair}(\mathit{Array}(\mathit{Lit}(\mathsf{arg}\,0,\mathsf{local}\,0)))`$:
the family grows by application, never by new heads.

Every other declaration is an alias, inlined at its uses. Inlining terminates
when every cycle through aliases passes through a head, because a literal
head is keyed by its occurrence. An alias such as `type T<X> = X | T<[X]>`,
whose recursive reference is under no constructor, is refused as unguarded.
TypeScript reads a record met with a function as one callable object, which
the model's exact meet would make empty. Lowering applies that reading only
to ground intersections it can resolve to rows, producing a literal head,
never a meet label.

Lowering also proposes each head's variances, as the least fixpoint over the
head graph on $`\mathsf{none}<\mathsf{co},\mathsf{contra}<\mathsf{inv}`$:
writable positions give $`\mathsf{inv}`$, results and readonly positions
$`\mathsf{co}`$, parameters $`\mathsf{contra}`$, and nested applications
compose. It proposes the tables the declarations need along with them. A
declaration that fails its check is weakened to $`\mathsf{inv}`$, which is
always valid.

## 6. Trust and acceptance

The division of labour is the one the verifier uses throughout: untrusted
code proposes, a small checker decides. Proposed and never trusted:
- the lowering;
- variances and entry tables;
- instances and their images;
- renamings;
- every certificate.

Checked:
- the equations' well-formedness (scope, arity, owned binders, meet normal
  form);
- every image, by substitution;
- every entry, by Theorem 1's conditions;
- every declaration, once per document.

No rule takes a semantic premise from a certificate: each is discharged by
Lemmas 1–3 and Theorem 1 from the equations themselves.

The acceptance theorem keeps its premise, the exact success condition of the
command-line checker. Its conclusion, safety of every accepted unit, is
stated over the graph of the unit's equations. A finite table is the case
where every head is nullary, so the theorem for finite tables is an instance.
The trust surface is unchanged: the parser and the reading of declared types
remain the trusted boundary, as before.

## 7. Related work

The families are Solomon's parameterized type definitions
([Solomon 1978](REFERENCES.md#solomon-1978)), whose equivalence he related to
that of deterministic pushdown automata. Here no equivalence is decided: a
checker validates certificates.

Coinductive subtyping over assumed pairs
([Amadio and Cardelli 1993](REFERENCES.md#amadio-and-cardelli-1993),
[Brandt and Henglein 1998](REFERENCES.md#brandt-and-henglein-1998))
handles regular types. Parametric entries extend the assumptions with
variables and hypotheses, so that one entry covers a non-regular family.
Subtyping with variance over expanding definitions is undecidable in general
([Kennedy and Pierce 2007](REFERENCES.md#kennedy-and-pierce-2007)), which is
why variance is proposed and checked rather than inferred by the checker.

An application is a closure, an equation with its arguments, as a suspended
substitution is in calculi of explicit substitutions
([Abadi et al. 1991](REFERENCES.md#abadi-cardelli-curien-and-lévy-1991)). But
what is delayed here is unfolding a definition, not substitution itself, and
the type level has no β-redexes; only the substitution lemma carries over.

## 8. Mechanization

| Concept | Lean |
| --- | --- |
| Signatures, templates, labels, the graph (2) | `Types/EquationGraphs.lean`, `Types/EquationMeets.lean` |
| Lemma 1 | `Types/EquationSupport.lean` |
| Lemma 2 | `Types/EquationCongruence.lean` |
| Lemma 3; images by substitution | `Types/EquationSubstitution.lean`, `Types/EquationCertificates.lean` |
| Renaming (4.1), entries and Theorem 1 (4.2) | `Types/PositiveRules.lean`, `Types/PositiveCertificates.lean` |
| Variance and `Var` (4.3) | `Types/EquationFamilies.lean` |
| Well-formedness, tree spelling | `Types/EquationValidator.lean`, `Types/EquationJson.lean` |
| Lowering (5) | `Source/EquationLowering.lean` |
| Tests, controls | `Tests/EquationFamilyTests.lean`, `Tests/EquationTreeTests.lean`, `Tests/EquationLoweringTests.lean` |

The wire spellings of labels are in [SOURCE-CLAIMS](SOURCE-CLAIMS.md#encoding)
and [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md). Progress is recorded in
[DESIGN: status](DESIGN.md#status).
