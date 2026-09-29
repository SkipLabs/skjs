# Recursive generic types as equations

Generic declarations such as TypeScript's `Promise` define infinite families
of types that no finite type graph can present. This section describes how
the verifier handles them. Each declaration is a parameterized type
definition. A type is a finite term that may apply a definition to
arguments, and a check unfolds an application one step, only when it reads
it. The meaning of types is unchanged: it is the step-indexed semantics of
[SEMANTICS](SEMANTICS.md) and [POSITIVE-TYPES](POSITIVE-TYPES.md). What is
new is a finite syntax for the checks that relate members of a family:
substitution for instantiation, and parametric assumptions for subtyping.

Sections 2 to 4 are mechanized in Lean (section 8). The lowering of section
5 is untrusted: the checker validates everything it proposes.

## 1. The problem

A finite type graph presents a *regular* type: finitely many distinct
types, recursion by reference back to a node. Many generic types are
regular at each instance: `List<number>` mentions only `List<number>` and
`number`. Others are not:

```ts
interface Promise<T> {
  then<R>(f: (x: T) => R): Promise<R>;
  catch<R>(f: (e: unknown) => R): Promise<T | R>;
}
```

Unfolding `Promise<number>` reaches `Promise<number | R>` through `catch`,
whose own `catch` reaches `Promise<number | R | R′>`, and so on. Every member
mentions a larger one, so the unfolding has infinitely many distinct
subtrees. Such definitions are *non-regular*
([Solomon 1978](REFERENCES.md#solomon-1978)). A presentation that enumerates
instances must stop somewhere. Past a budget it can only refuse the
declaration, since reading the tail as `unknown` would be unsound.

The semantics admits infinitely many nodes: a type's meaning is a guarded
fixed point.
What must be finite is what a check inspects. So each member is named by a
finite term, its structure is computed on demand, and members are related
by rules that inspect finitely many unfoldings.

## 2. Type definitions

### 2.1 Syntax

Types are the positive types of [POSITIVE-TYPES](POSITIVE-TYPES.md), with
type variables $`\alpha,\beta`$, applications of definitions, and
intersections:

```math
\tau \;::=\; \alpha \;\mid\; D\langle\tau_1,\ldots,\tau_n\rangle \;\mid\; c(\tau_1,\ldots,\tau_k) \;\mid\; \tau\lor\tau \;\mid\; \tau\land\tau \;\mid\; \bot
```

Here $`c`$ ranges over the constructors of the positive language: records,
arrays, functions with their signatures, primitives. A signature may be
quantified, $`\forall\vec\beta\le\vec\rho.\,\sigma`$, which binds
$`\vec\beta`$ in $`\sigma`$.

A **program of definitions** is a finite set of equations

```math
D\langle\alpha_1,\ldots,\alpha_n\rangle \;=\; \tau_D ,
```

one for each name $`D`$, where $`\mathrm{fv}(\tau_D)\subseteq\{\vec\alpha\}`$
and $`\tau_D`$ is *contractive*: a constructor $`c(\ldots)`$, a union of
constructors, or a quantified signature.
Definitions may refer to each other and to themselves, at any arguments.
`Promise` is

```math
\mathit{Promise}\langle\alpha\rangle=\{\ \mathit{then}:\forall\beta.\,(\alpha\to\beta)\to\mathit{Promise}\langle\beta\rangle,\ \ \mathit{catch}:\forall\beta.\,(\top\to\beta)\to\mathit{Promise}\langle\alpha\lor\beta\rangle\ \}.
```

### 2.2 Meaning

An application unfolds to its definition's body at its arguments:

```math
⟦D\langle\vec\tau\rangle⟧^\eta \;=\; ⟦\tau_D[\vec\tau/\vec\alpha]⟧^\eta ,
```

with capture-avoiding substitution, and $`\eta`$ assigning meanings to free
variables. Contractiveness makes this a guarded definition: an application
in the body sits under a constructor, whose operands are read at a lower
step. So the step-indexed fixed point exists, and it is the meaning the rest
of the verifier already uses. One unfolding substitutes into a finite body
and leaves the applications in it unexpanded, so a check pays only for the
unfoldings it performs. The family `Promise` has infinitely many members,
but every member a check reaches is a finite term.

An intersection means exactly the intersection of its operands,
$`⟦\tau\land\sigma⟧^\eta=⟦\tau⟧^\eta\cap⟦\sigma⟧^\eta`$. It must: once
$`\alpha\land\rho`$ appears in a body, substitution can put any type for
$`\alpha`$. The lemmas of section 3 require meaning to commute with
substitution, which fixes the intersection of the operands as the only
admissible reading.

## 3. Metatheory

Three lemmas let a check work on finite terms while the meaning is a fixed
point over infinitely many unfoldings. Each holds for values and argument
lists alike.

**Lemma 1 (support).** If $`\eta`$ and $`\theta`$ agree on
$`\mathrm{fv}(\tau)`$, then $`⟦\tau⟧^\eta=⟦\tau⟧^\theta`$.

**Lemma 2 (congruence).** If $`⟦\tau_i⟧^\eta=⟦\sigma_i⟧^\theta`$ for every
$`i`$, then $`⟦D\langle\vec\tau\rangle⟧^\eta=⟦D\langle\vec\sigma\rangle⟧^\theta`$.

*Proof sketch.* By induction on the step index $`n`$. Constructors read
their operands below $`n`$, and the operands are the body's subterms at the
two argument lists, equal by the induction hypothesis. Quantified signatures
compare their instances pairwise; argument lists at $`n`$ use the values
just established at $`n`$. The two environments may differ, which is what
lets the lemma relate two applications that bind their quantifiers
separately. $`\square`$

**Lemma 3 (substitution).** $`⟦\tau⟧^{\eta[\vec\alpha\mapsto⟦\vec\sigma⟧^\eta]}=⟦\tau[\vec\sigma/\vec\alpha]⟧^\eta`$
for simultaneous, capture-avoiding substitution at matching kinds.

*Proof sketch.* By structural induction on the finite term $`\tau`$: an
application is handled by Lemma 2, and intersection distributes over the
unions substituted into it. Substitution traverses only the finite term.
$`\square`$

Lemma 3 is what makes instantiation checkable. A call instantiates a
generic signature by substituting into its finite syntax, and the checker
recomputes that substitution rather than trusting a table of instances.
Before, a finite presentation had to close the table of instances. The
checker and its soundness proofs, expression typing and control flow
included, are stated once over an interface: an image check with a proof
that it computes correct images. The old closure check and substitution are
two instances of that interface.

## 4. Subtyping

Subtyping between recursive types is checked coinductively. A certificate
supplies a finite set of assumed pairs. The checker verifies that each
pair's structure is covered, reading the pairs themselves for the operands,
one step lower
([Amadio and Cardelli 1993](REFERENCES.md#amadio-and-cardelli-1993),
[Brandt and Henglein 1998](REFERENCES.md#brandt-and-henglein-1998),
[POSITIVE-TYPES](POSITIVE-TYPES.md#core-tables)). For a non-regular family
the needed set is infinite, since
`Promise<number> ≤ Promise<number | string>` needs
`Promise<number | β> ≤ Promise<number | string | β>` for `catch`, then a
pair with one more bound variable, without end. The pairs differ only in
their arguments, so the assumptions are made parametric.

**Soundness, not completeness.** The rules below are sound for the semantic
inclusion. They are not complete for it, and whether that inclusion is
decidable is open. Two results about related systems show where complete
rules become undecidable, and the rules avoid both.
- Subtyping in F<: is undecidable with its full rule for bounded quantifiers
  ([Pierce 1994](REFERENCES.md#pierce-1994)). Comparing quantifiers on one
  fixed pairing, as 4.1 does, is the standard decidable restriction.
- Nominal subtyping with variance is undecidable once inheritance is
  expansive ([Kennedy and Pierce 2007](REFERENCES.md#kennedy-and-pierce-2007)).
  The types here are structural, with no declared inheritance, so the result
  does not transfer directly. It is the nearest known result to relating
  expanding definitions such as `Promise`, which 4.3 does through
  per-position variance only.

Neither result is a theorem about this model's inclusion. They explain the
choice of restrictions; the price is completeness.

### 4.1 Quantified signatures

Two quantified signatures are compared up to renaming of bound variables,
with the target's quantifiers rigid and bounds compared contravariantly:

```math
\frac{\vec{\rho}'\le\vec\rho\qquad \sigma\le\sigma'[\vec\alpha/\vec\beta]\qquad \vec\alpha\notin\mathrm{fv}(\forall\vec\beta.\,\sigma')}
{\forall\vec\alpha\le\vec\rho.\,\sigma\ \le\ \forall\vec\beta\le\vec{\rho}'.\,\sigma'}
```

This is the kernel rule of F<: restricted to one fixed pairing of
quantifiers, which keeps it a check
([Pierce 1994](REFERENCES.md#pierce-1994)). Soundness is Lemma 3: an instance
of the source at $`\vec X`$ within $`\vec{\rho}'`$ is an instance of the
target at the same $`\vec X`$.

### 4.2 Parametric assumptions

An **assumption** $`a`$ is a constrained judgment with a finite table
$`T_a`$ of pairs over its variables:

```math
a\;=\;\forall\vec\alpha\vec\beta.\ \Pi_a\Rightarrow D\langle\vec\alpha\rangle\le D'\langle\vec\beta\rangle ,
```

where $`\Pi_a`$ is a finite set of hypotheses $`\gamma\le\delta`$ between
its variables. A plain pair is an assumption without variables. Fix a set
$`\mathcal A`$ of assumptions. Types are unions of labels; $`l`$ ranges over
labels, $`A,B`$ over unions.

**Premises.** An operand comparison is read by the judgment
$`\Pi;T\vdash A\sqsubseteq B`$:

```math
\frac{(A,B)\in T}{\Pi;T\vdash A\sqsubseteq B}\ \textsf{Tab}
\qquad
\frac{\forall l\in A.\ \ \Pi;T\vdash l\sqsubseteq B}{\Pi;T\vdash A\sqsubseteq B}\ \textsf{Union}
\qquad
\frac{l\in B}{\Pi;T\vdash l\sqsubseteq B}\ \textsf{Mem}
```

```math
\frac{(\gamma\le\delta)\in\Pi\qquad \delta\in B}{\Pi;T\vdash\gamma\sqsubseteq B}\ \textsf{Hyp}
\qquad
\frac{(\gamma\le\delta)\in\Pi\qquad \delta\land\rho\in B}{\Pi;T\vdash\gamma\land\rho\sqsubseteq B}\ \textsf{MeetHyp}
```

```math
\frac{\forall\vec\alpha\vec\beta.\ \Pi_a\Rightarrow D\langle\vec\alpha\rangle\le D'\langle\vec\beta\rangle\ \in\mathcal A\qquad D'\langle\vec\sigma\rangle\in B\qquad \forall(\gamma\le\delta)\in\Pi_a.\ \ \Pi;T\vdash\gamma\theta\sqsubseteq\delta\theta}
{\Pi;T\vdash D\langle\vec\tau\rangle\sqsubseteq B}\ \textsf{Inst}
```

where $`\theta=[\vec\tau/\vec\alpha,\vec\sigma/\vec\beta]`$. The premises of
$`\textsf{Inst}`$ compare $`\vec\tau`$ and $`\vec\sigma`$, strict subterms of
its conclusion, so derivations are finite and the judgment is decidable.

**Covering.** A pair is covered, $`\Pi;T\vdash A\le B`$, when every clause
of $`A`$'s one-step unfolding is covered by a clause of $`B`$'s, under the
[clause coverage rules](POSITIVE-TYPES.md#clause-coverage) with their
operand premises read by $`\sqsubseteq`$, and every variable of $`A`$ is in
$`B`$ or below a member of $`B`$ by a hypothesis. Quantified signatures are
compared by 4.1.

**Validity.**

```math
\frac{\forall(A,B)\in T_a\cup\{(D\langle\vec\alpha\rangle,D'\langle\vec\beta\rangle)\}.\ \ \Pi_a;T_a\vdash A\le B}
{\vdash a\ \mathsf{valid}}\ \textsf{Valid}
```

**Theorem 1.** Let every assumption of $`\mathcal A`$ be valid. Write
$`\eta\models_n\Pi`$ when every hypothesis of $`\Pi`$ holds at $`\eta`$ at
every step up to $`n`$. For every $`a\in\mathcal A`$, every $`n`$ and every
$`\eta\models_n\Pi_a`$, the conclusion of $`a`$ and every pair of $`T_a`$
hold at $`\eta`$ at step $`n`$.

*Proof sketch.* By strong induction on $`n`$, values before argument lists,
with an inner induction on the derivation of each premise.
- A premise is read below $`n`$. $`\textsf{Tab}`$ holds there by the outer
  induction, $`\textsf{Mem}`$ outright, and $`\textsf{Hyp}`$ and
  $`\textsf{MeetHyp}`$ by $`\eta\models_n\Pi`$.
- $`\textsf{Inst}`$ is the conclusion of its assumption at
  $`\eta'=\eta[\vec\alpha\mapsto⟦\vec\tau⟧^\eta,\vec\beta\mapsto⟦\vec\sigma⟧^\eta]`$.
  Its hypotheses hold there because their instances are premises, which
  hold by the inner induction. So the outer induction applies at
  $`\eta'`$, and Lemma 3 turns the conclusion into
  $`D\langle\vec\tau\rangle\le D'\langle\vec\sigma\rangle`$ at $`\eta`$.
  Substitution is simultaneous, so an assumption may be used at its own
  variables, as `catch` does.
- Quantified signatures reassign bound variables only, and hypotheses
  mention none.
- Argument lists read element contracts at step $`n`$ itself. An instance
  there has its hypotheses only for values at $`n`$, so the theorem is
  proved together with a variant whose hypotheses hold below $`n`$ and, at
  $`n`$, for values.

$`\square`$ With no variables this is the existing theorem for finite
tables.

### 4.3 Variance

That `Promise` is covariant is a fact about its definition, so it is
established once. A **variance** assigns each parameter of a
definition one of $`\mathsf{co},\mathsf{contra},\mathsf{inv},\mathsf{none}`$.
It stands for the assumption
$`\forall\vec\alpha\vec\beta.\ \Pi_D\Rightarrow D\langle\vec\alpha\rangle\le D\langle\vec\beta\rangle`$,
with $`\alpha_i\le\beta_i`$ in $`\Pi_D`$ when $`v_i`$ is co or inv, and
$`\beta_i\le\alpha_i`$ when it is contra or inv. A use then
compares arguments only:

```math
\frac{\forall i.\ \ \tau_i\le\sigma_i\ \ (v_i\in\{\mathsf{co},\mathsf{inv}\})\qquad \sigma_i\le\tau_i\ \ (v_i\in\{\mathsf{contra},\mathsf{inv}\})}
{D\langle\vec\tau\rangle\le D\langle\vec\sigma\rangle}\ \textsf{Var}
```

`Var` is sound as an instance of a valid variance, by Theorem 1 and Lemma 3.

**Computing variances.** The checker computes each definition's variance
from the definitions alone. Definitions are taken
in dependency order, one strongly connected component of the reference
graph at a time.
- *A definition on no cycle* is checked by one traversal of its body: an
  application of a definition below it is compared by that definition's
  variance, recursively on the arguments (4.2).
- *A cycle*, such as `Promise`, whose `catch` returns $`\mathit{Promise}\langle\alpha\lor\gamma\rangle`$,
  is checked with its members' candidate variances as assumptions. The
  assumption is guarded, since every self-reference sits under a
  constructor.

Candidates start permissive and are weakened where the check fails, on the
finite lattice $`\mathsf{none}<\mathsf{co},\mathsf{contra}<\mathsf{inv}`$.
$`\mathsf{inv}`$ is always valid, so the iteration ends in a valid variance.
A writable field forces $`\mathsf{inv}`$. An invariant position is stated
with two variables related both ways. A single shared variable would need
Lemma 2 inside the induction of Theorem 1, at the step being proved.

Variances are computed on demand, once per definition, for the definitions
a check actually compares.

**Other pairs.** When `Var` does not decide a pair, the pair is unfolded
into the coinductive check of assumed pairs, compared up to renaming of
bound variables. `Promise⟨number⟩ ≤ PromiseLike⟨number⟩` closes this way:
its `then` members lead to `Promise⟨ρ⟩ ≤ PromiseLike⟨ρ⟩` for a bound
$`\rho`$, which recurs only renamed. A pair that recurs with growing
arguments is refused.

### 4.4 Example

`Promise` is declared covariant. Its assumption
$`\forall\alpha\beta.\ \alpha\le\beta\Rightarrow\mathit{Promise}\langle\alpha\rangle\le\mathit{Promise}\langle\beta\rangle`$
checks member by member:
- **`then`:** after renaming the quantifiers, the callback
  $`\beta\to\gamma`$ must be within $`\alpha\to\gamma`$, which is the
  hypothesis. Both results are $`\mathit{Promise}\langle\gamma\rangle`$.
- **`catch`:** the results $`\mathit{Promise}\langle\alpha\lor\gamma\rangle`$
  and $`\mathit{Promise}\langle\beta\lor\gamma\rangle`$ are an instance of
  the assumption itself. Its hypothesis $`\alpha\lor\gamma\le\beta\lor\gamma`$
  is a table pair, covered by the hypothesis and by $`\gamma`$ on both
  sides.

`Promise<number> ≤ Promise<number | string>` is then `Var` with the premise
`number ≤ number | string`. The converse fails at its premise, and so does
the definition's unfolding, at `then`'s callback. For
`interface Cell<T> { v: T }` the covariant declaration is invalid, and
`Cell<A> ≤ Cell<B>` requires `A` and `B` equivalent.

## 5. From source

Lowering turns the parser's declarations into definitions:
- **Declarations:** an interface, a class instance type or an object alias
  becomes a definition over its type parameters. Its bases are met into
  its body.
- **Generic members:** a generic method becomes a quantified signature in
  that body.
- **Units:** a generic function, closure, class or imported generic value
  is typed by a quantified signature of its own.
- **Literals:** each occurrence of an object, function, tuple or array type
  inside a definition becomes a definition of its own, over the variables
  it mentions: $`L\langle\vec\gamma\rangle=\text{the literal}`$ with
  $`\vec\gamma`$ its free variables. This is λ-lifting of type literals.

Every other declaration is an alias, inlined at its uses. Inlining
terminates when every cycle through aliases passes through a definition:
lifted literals are keyed by their occurrence. An alias
such as `type T<X> = X | T<[X]>` recurs under no constructor, so it is
refused as unguarded.

Definitions are created per source construct, so their
number is bounded by the size of the source, whatever families it defines.
`Pair<T>`'s `push<U>(): Pair<[T, U]>` has the result type
$`\mathit{Pair}\langle\mathit{Array}\langle L\langle T,U\rangle\rangle\rangle`$
with $`L\langle\gamma,\delta\rangle=[\gamma,\delta]`$. The family grows by
application, over a fixed set of definitions.

TypeScript reads a record met with a function as one callable object, which
the model's exact intersection would make empty. Lowering applies that
reading only to ground intersections, producing a literal definition, out
of reach of substitution.

## 6. Trust and acceptance

Untrusted code proposes and a small checker decides, as everywhere in the
verifier.

- **Proposed:** the definitions, the assumptions a certificate relates
  different definitions by, and their tables, instances, and every
  certificate.
- **Checked:** the definitions' well-formedness (scoping, arity,
  contractiveness), every instantiation by substitution, every assumption
  by the conditions of Theorem 1. Variances are computed by the checker.

Every semantic premise of a rule is discharged by Lemmas 1–3 and Theorem 1
from the definitions themselves.

The acceptance theorem keeps its premise: the exact success condition of
the command-line checker. Its conclusion, safety of every accepted unit, is
stated over the unit's definitions. A finite type graph is the case where
every definition has no parameters, so the theorem for finite graphs is an
instance. The trust surface is unchanged: the parser and the reading of
declared types remain the trusted boundary.

## 7. Related work

The families are Solomon's parameterized type definitions
([Solomon 1978](REFERENCES.md#solomon-1978)), whose equivalence he related to
that of deterministic pushdown automata. Here a checker validates
certificates and computes variances.

Coinductive subtyping over assumed pairs
([Amadio and Cardelli 1993](REFERENCES.md#amadio-and-cardelli-1993),
[Brandt and Henglein 1998](REFERENCES.md#brandt-and-henglein-1998)) handles
regular types. Parametric assumptions extend it with variables and
hypotheses, so that one assumption covers a non-regular family. Kennedy
and Pierce prove nominal subtyping with variance undecidable under expansive
inheritance ([Kennedy and Pierce 2007](REFERENCES.md#kennedy-and-pierce-2007));
the definitions here are structural, and section 4 relates an expanding
definition to itself only through per-position variance.

An application is a closure, a definition with its arguments, like a
suspended substitution in calculi of explicit substitutions
([Abadi et al. 1991](REFERENCES.md#abadi-cardelli-curien-and-lévy-1991)).
What it delays is the unfolding of a definition; substitution is carried
out in full. The type level
has no β-redexes, so only the substitution lemma carries over.

## 8. Mechanization

The Lean development represents a bound variable by the application that
introduces it. The `β` of the `then` of `Promise⟨number⟩` is a distinct term
from the `β` of the `then` of `Promise⟨string⟩`, so capture-avoidance holds
by construction, and comparing quantifiers from two applications is an
explicit renaming (section 4.1). Definitions are numbered, and bodies refer
to parameters and quantified variables by position.

| Concept | Lean |
| --- | --- |
| Definitions, types, unfolding, intersection (2) | `Types/EquationGraphs.lean`, `Types/EquationMeets.lean` |
| Lemma 1 | `Types/EquationSupport.lean` |
| Lemma 2 | `Types/EquationCongruence.lean` |
| Lemma 3; instantiation by substitution | `Types/EquationSubstitution.lean`, `Types/EquationCertificates.lean` |
| Quantified signatures (4.1), assumptions and Theorem 1 (4.2) | `Types/PositiveRules.lean`, `Types/PositiveCertificates.lean` |
| Variance and `Var` (4.3) | `Types/EquationFamilies.lean` |
| Well-formedness, term spelling | `Types/EquationValidator.lean`, `Types/EquationJson.lean` |
| Lowering (5) | `Source/EquationLowering.lean` |
| Tests, controls | `Tests/EquationFamilyTests.lean`, `Tests/EquationTreeTests.lean`, `Tests/EquationLoweringTests.lean` |

The wire spellings are in [SOURCE-CLAIMS](SOURCE-CLAIMS.md#encoding) and
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md). Progress is recorded in
[DESIGN: status](DESIGN.md#status).
