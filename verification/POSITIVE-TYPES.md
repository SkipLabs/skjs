# Positive types: reference constraints and checked normalization

This specifies the maintained type representation, state-assertion grammar and
subtype rules. [State assertions](#state-assertion-grammar) extend point claims;
they are separate from ordinary types and their normalization. Lean
proves positive normalization preserves recursive type semantics, the declarative
rules are sound, and the certificate checker is sound and complete for those
rules. A first closed null/undefined/boolean fragment is connected to this consumer. Its foundation and integration boundary are in [SEMANTICS.md](SEMANTICS.md).

## Representation and mathematical rules

A label names a whole type, never a fragment of one. Operands appearing inside a
body are themselves types, so the syntax has two levels. A **type** is a union of
graph labels:

$$A ::= \bot\mid i\mid A\lor A.$$

A **clause** constrains one value shape. A value is null, undefined, a boolean, a location
or a function object with closed invocation code, and each clause pins exactly one of those:

$$
\begin{aligned}
c &::= \mathsf{null}\mid\mathsf{undefined}\mid\mathsf{bool}\mid\mathsf{true}\mid\mathsf{false}\mid r\mid f\mid o,\\
r &::= \mathsf{Ref}\,A\mid r\land\mathsf{Ref}\,A,\\
f &::= \mathsf{fun}\mid f\land(A\to A),\\
o &::= \mathsf{Callable}(A;[A_1,\ldots,A_m];[(B_1,C_1),\ldots,(B_k,C_k)]).
\end{aligned}
$$

| Clause | Denotes |
| --- | --- |
| $\mathsf{null}$ | the value null |
| $\mathsf{undefined}$ | exactly undefined, at every budget; disjoint from null |
| $\mathsf{bool}$ | true or false |
| $\mathsf{true}$, $\mathsf{false}$ | exactly that value, at every budget |
| $\mathsf{Ref}\,A$ | a location whose stored invariant agrees with $A$ |
| $r\land\mathsf{Ref}\,A$ | the same location, also agreeing with $A$ |
| $\mathsf{fun}$ | a function object with closed invocation code, carrying no call obligation |
| $f\land(A\to B)$ | also: applied to any argument in $A$, it is safe at $B$ |

$\mathsf{fun}$ is the empty arrow intersection. It is a terminal because an
intersection of zero arrows cannot be derived from a rule producing arrows, and
it is a real type: every function object with closed invocation code inhabits it. A single arrow $A\to B$
abbreviates $\mathsf{fun}\land(A\to B)$, since arrow membership already requires
closed invocation code.

For the maintained argument-list graph, `arrs L S` carries fixed signatures
`L` and variadic signatures `S` on the same function shape. Both instantiate
the [common behavioral call promise](SEMANTICS.md#one-meaning-for-callable-contracts);
they do not select disjoint code kinds. The empty function contract has both
lists empty. Callable fields add invariant property requirements to that same
value, and overload normalization conjoins its call promises.

References are asymmetric to arrows here: $r$ always carries a first operand, so
there is no bare "any location" clause. A cell's operand is the invariant that
makes it readable and writable at all; the nearest expressible thing is
$\mathsf{Ref}\,\bot$, which is a constraint rather than an absence.

Every conjunct of an $r$ constrains the **same location and its one stored
invariant**. They are not several separately allocated cells, and they are not
replaced by a single invariant over the intersection of their operands. A plain
reference is a single $\mathsf{Ref}\,A$.

The two Boolean singletons relate to $\mathsf{bool}$ by

$$
\mathsf{true},\mathsf{false}\leq\mathsf{bool},\qquad
\mathsf{true}\land\mathsf{bool}=\mathsf{true},\qquad
\mathsf{true}\land\mathsf{false}=\bot,
$$

and symmetrically for $\mathsf{false}$.

A graph body is a finite positive formula over clauses:

$$P ::= \bot\mid c\mid P\lor P\mid P\land P.$$

In the Lean development and the [request encoding](REQUEST-PROTOCOL.md#request-fields)
these clauses include `nul`, `undef`, `bool`, `boolLit`, `refs`, `dict`, `arrs`, and `callable`, where a reference
conjunction is a first operand plus the rest, and an arrow intersection is a
possibly-empty list of domain/result pairs. A `callable` clause carries a first
bag invariant, a list of further bag invariants, and its domain/result pairs.
All constraints apply to one object. Its shape is function, as for `arrs`;
`refs` still means a plain object. There is no callability-neutral bag clause yet.

The `dict` clause extends a plain object with readonly string-index contracts.
Its index operands constrain **every present own field**, including named
fields, through a read capability; they grant no write permission. The object
may have no fields, so an arbitrary indexed read has type `A | undefined`,
even when its index contract is `A`. Normalization retains all index operands
when dictionaries intersect each other or a named-field record. A checked
dictionary-to-dictionary inclusion covers every target index operand with a
source operand at a subtype, while retaining the named-field obligations.
Index operands are guarded through the world, so a recursive graph can contain
`JsonObject = { readonly [key: string]: Json | null }` without finite unfolding.
Inline readonly string-index annotations now translate to `dict` for the OCaml
producer, with a named indexed read checked by the graph's `readDict` rule and
a computed string-key read checked by `indexDict`.
Required named fields can accompany the index as invariants or readonly views;
the checked source annotation retains both obligations in one clause.
Translation of the imported recursive `Json` declaration is a separate source
closure step. The `allocDict` rule proves a fresh literal's dictionary view
from every initializer at the index element type.

### Keys, optional fields, bigints, symbols and construct signatures

A record operand maps **property keys** to types. A key is a string or a
symbol, and the two spaces are disjoint:

$$
\kappa ::= \mathsf{str}(s)\mid\mathsf{sym}(n),\qquad
\varphi ::= \overline{\kappa{:}A}.
$$

A `refs` or `dict` clause carries, besides its invariant operands $\varphi_0,
\ldots,\varphi_m$ and readonly views $\psi$, a list $\omega$ of **optional**
fields, and `dict` its index operands $\overline{D}$. Writing $\ell$ for the
object $\mathsf{obj}(\mathit{flds},\mathsf{absent})$ and $X$ for the meaning
of an operand,

$$
\begin{aligned}
\llbracket\mathsf{Ref}(\varphi_0\land\cdots\land\varphi_m;\psi;\omega)\rrbracket_n(W,v)
&\iff \textstyle\bigwedge_i\mathsf{rec}(X\varphi_i)_n(W,v)\land
      \mathsf{view}(X\psi)_n(W,v)\land\mathsf{opt}(X\omega)_n(W,v),\\
\mathsf{opt}(\overline{\kappa{:}T})_n(W,v)
&\iff v=\ell\ \land\ \forall(\kappa{:}T),\,\forall l.\;
      \mathit{flds}(\kappa)=l\Rightarrow
      \exists c.\;W(l)=c\land\forall j<n.\;c_j\equiv T_j,
\end{aligned}
$$

and a `dict` clause adds $\forall D\in\overline{D}.\;\mathsf{dictView}(XD)$, which
ranges over the object's **string** keys only (`optT`, `dictViewT`). An optional
field constrains its key only where the object has it, and there its location
holds exactly the contract; so a read gives $T$ or $\mathsf{undefined}$, and no
rule writes it, since an object's keys are fixed at allocation.

Two further primitive clauses and one callable clause:

$$
\begin{aligned}
\llbracket\mathsf{bigint}\rrbracket_n(W,v)&\iff\exists i.\;v=\mathsf{bigint}(i),\qquad
\llbracket\mathsf{symbol}\rrbracket_n(W,v)\iff\exists i.\;v=\mathsf{sym}(i),\\
\llbracket\mathsf{Ctors}\,\overline{(\vec A,B)}\rrbracket_k(W,v)
&\iff\mathsf{Constructible}(v)\ \land\ \forall(\vec A,B).\;\forall j<k,\;
   U\sqsupseteq W|_j,\ \mathit{heap}\models_j U,\ \vec a\in X\vec A.\\
&\qquad\exists t.\;\mathsf{new}\,v(\vec a)\to t\ \land\ t\in\mathsf{Safe}_j(XB)(U,\mathit{heap}),
\end{aligned}
$$

where $\mathsf{Constructible}(v)$ says $v$ is a closed object whose code is
construct-only, and $\mathsf{new}\,v(\vec a)\to t$ is the one step that binds
$\vec a$ and an `undefined` receiver into its body (`ctorsT`, `ConstructsTo`).
A `Ctors` clause has its own shape, so it meets no `arrs` or `callable` clause:
no class is callable and no arrow constructible.

Conjunction extends as before: same-shape clauses concatenate their operands,

$$
\begin{aligned}
\mathsf{Ref}(\vec\varphi;\psi;\omega)\land\mathsf{Ref}(\vec\varphi';\psi';\omega')
 &=\mathsf{Ref}(\vec\varphi\,\vec\varphi';\psi\psi';\omega\omega'),\\
\mathsf{Ctors}\,L\land\mathsf{Ctors}\,M&=\mathsf{Ctors}\,(L\,M),\qquad
c\land c=c\ \ (c\in\{\mathsf{bigint},\mathsf{symbol}\}),
\end{aligned}
$$

and `bigint`, `symbol` and `Ctors` meet every other shape as $\bot$.

A callable intersection concatenates both lists of requirements. Intersecting
it with `arrs` adds call obligations while retaining its bag invariants.
Subtyping between callable clauses requires the same bidirectional operand
coverage as references, together with arrow coverage. A callable can forget
its bag requirements to become `arrs`; the reverse requires evidence of those
requirements and has no unconditional rule.

A **normal body** is a union of clauses, with no conjunction above the clause
level:

$$N ::= \bot\mid c\mid N\lor N.$$

Normalization rewrites a body into that form. It is disjunctive normal form,
pushing $\land$ down through $\lor$ until every conjunction joins two clauses:

$$
\begin{aligned}
\operatorname{nf}(\bot)&=\bot,&\operatorname{nf}(c)&=c,\\
\operatorname{nf}(P\lor Q)&=\operatorname{nf}(P)\lor\operatorname{nf}(Q),\\
\operatorname{nf}(P\land Q)&=\textstyle\bigvee\{\,c\land d\;\mid\;
   c\ \text{a clause of}\ \operatorname{nf}(P),\
   d\ \text{a clause of}\ \operatorname{nf}(Q)\,\}.
\end{aligned}
$$

So the whole procedure reduces to one question: what is the conjunction of two
clauses? That turns on shapes.

Clauses of **different shapes** meet as $\bot$. A value is null, undefined, a boolean, a
location or a lambda, never two, so nothing satisfies both.

Clauses of the **same structured shape** need no computation: by the grammar
above, $r\land r'$ is again a reference conjunction and $f\land f'$ again an
arrow intersection. The operator is the answer, and the two merge lemmas say
exactly that their meaning is the intersection.

The **primitives** follow their small lattice: $c\land c=c$,
$\mathsf{bool}\land\mathsf{true}=\mathsf{true}$,
$\mathsf{bool}\land\mathsf{false}=\mathsf{false}$, and
$\mathsf{true}\land\mathsf{false}=\bot$.

Nothing is distributed through a reference operand or an arrow result. By the
grammar this is structural rather than a choice: an operand is a type, already
normal, so there is no formula down there to normalize. That is also why
guardedness survives untouched.

For example:

$$
\mathsf{Ref}\,A\land(\mathsf{Ref}\,B\lor\mathsf{null})
\quad\longmapsto\quad\mathsf{Ref}\,A\land\mathsf{Ref}\,B.
$$

The normalizer retains incompatible reference constraints. In this indexed
model, $\mathsf{Ref}\,\mathsf{null}\land\mathsf{Ref}\,\mathsf{bool}$ has a zero-budget witness but has no members at any
positive budget. A nested analogue has a witness at budget one in a satisfying
cyclic heap. These are checked examples, so replacing all such clauses by
bottom would be an incorrect normalization.

## State-assertion grammar

Point claims can combine ordinary types with facts about the current execution
state. The following notation describes the finite assertion layer; it does not
add constructors to the ordinary type grammar above. Let $x$ and $y$ name environment
slots, $A$ and $B$ be ordinary types, and $R$ be a finite disjunction of primitive predicates:

$$
\begin{aligned}
a &::= \mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{Number}\mid\mathsf{numLit}(b),\\
R &::= \{a_1,\ldots,a_k\}\quad(k\geq 0),\\
J &::= \top\mid x:A\mid x=R\mid x=y\mid x\mapsto R\mid x\mapsto y\mid J\land J.
\end{aligned}
$$

| Assertion | What it states |
| --- | --- |
| $x:A$ | The value of $x$ belongs to the ordinary type $A$, interpreted against the current world and budget. |
| $x=R$ | $x$ satisfies one of the predicates in $R$. A statement about the environment, so no heap change can falsify it. |
| $x=y$ | $x$ and $y$ hold the same value, including the same location when they hold references. Again untouched by heap changes. |
| $x\mapsto R$ | The cell $x$ names currently holds a value satisfying $R$. It does not specify or change that location's storage invariant. |
| $x\mapsto y$ | The cell $x$ names currently holds the value of $y$. A write or a call can falsify this. |
| $\top$, $J_1\land J_2$ | No requirement, or both requirements. Conjunction does not assert ownership or disjoint locations. |

The two relations each take a primitive predicate disjunction or a variable on the right, which is
the whole grammar: $=$ speaks only about the environment, $\mapsto$ about the
heap as well. That division is what decides survival, and
[Program typing](PROGRAM-TYPING.md#the-reference-operations) states the rules
over it. Despite the notation there is no separating conjunction and no
ownership: these facts are duplicable, and $\mapsto$ carries no claim that the
cell is unaliased or that the heap holds nothing else.

An empty predicate list is an impossible content/value predicate, not an absent
assertion. There is no general assertion disjunction, negation or quantifier in
this finite grammar. The union within $R$ permits alternatives for one value;
it does not express arbitrary correlated alternatives between slots. The explicit
read and equality atoms express only the relationships listed above. `Number` means any numeric value; `numLit(b)` means exactly that bit pattern.
Singleton predicates imply `Number`, not conversely. Predicates on nested
references remain outside this vocabulary.

The notation requested for source claims is an abbreviation:

$$
x:\{\mathsf{value}:B=R\}
\quad\equiv\quad
x:\mathsf{ref}(B)\ \land\ x\mapsto R.
$$

Here $\mathsf{ref}(B)$ abbreviates the ordinary clause $\mathsf{Ref}\,B$, with no
additional reference conjuncts. In displayed source
claims, the right side of `=` uses type-like spelling for the finite predicate:
`true` denotes $\{\mathsf{true}\}$ and `boolean` denotes
$\{\mathsf{true},\mathsf{false}\}$. Thus `{ value: boolean = true }` combines
`ref(boolean)` with a current-cell fact. It is neither `ref(true)` nor an
ordinary type operand that can be inserted into arrows or recursive type bodies.
Forgetting the cell assertion leaves `ref(boolean)` and loses information.

The implementation stores these conjunctions as an ordinary context $\Gamma$
plus `HeapKnowledge.Knowledge`: cell facts $\Delta$, immutable-value facts $V$,
and a list of read/equality links. `HeapLinks.Holds` interprets the latter, with
an `alias` flag distinguishing timeless slot equality from a current read.
The grammar is mathematical notation for those components, not a new JSON or
TypeScript parser. `cell` corresponds to `HeapFacts.Holds`; `val` corresponds to
`HeapKnowledge.ValueHolds`. A source expression assertion uses its evaluated
result in place of $x$.

[Semantics](SEMANTICS.md#current-content-assertions-and-postconditions) defines
heap observations and their relationship to the world and satisfying heap.
[Program typing](PROGRAM-TYPING.md#checked-expression-postconditions) owns the
checked rules and fact transfer. [Source claims](SOURCE-CLAIMS.md#current-content-assertions)
owns the wire encoding and its restrictions. Expression checking, graph-edge
entailment and source consumption of supplied observations are all implemented;
the producer generates checked heap facts from supported operations.

## Recursive normalization

A source graph maps each label to a formula $P$; its normal form maps the same
label to a normal body $N$, one label at a time:

$$
\operatorname{nf}(G)(i)=\operatorname{nf}(G(i)).
$$

References to other labels occur only inside reference or arrow operands.
Thus recursion remains guarded even when the graph body contains unions and
intersections. No recursion is unfolded during normalization, and no new
labels are allocated. A finite graph stays finite, although a body can grow
exponentially through DNF distribution. There is no measured performance claim
or growth-control optimization yet.

`normalize_sound` proves preservation for every operand interpretation, budget,
world and value. Consequently, `normalized_layer` proves equality of the whole
guarded operators. `normalize_recursive` then establishes:

$$
\llbracket \operatorname{nf}(G)\rrbracket=\llbracket G\rrbracket.
$$

This is a general theorem for the explicit graph syntax, not just an example
or an unrolling to a fixed depth. Arbitrarily nested positive types can be
presented by naming their guarded operands in the graph.

Nothing in the current pipeline invokes the normalizer. Requests carry normal
bodies, and the [request grammar](REQUEST-PROTOCOL.md#request-fields) has no
conjunction above the clause level, so every graph reaching the consumer is
normal by construction. What is proved here is the interface a producer would
need if it did hold formula bodies: `checkSource` normalizes and checks, and
`accepted_source` transports the conclusion back to the original graph's
denotation, so a checked inclusion never has to be re-justified against the
unnormalized form. A verified compiler from textual type syntax to a graph, which
is what would first need that interface, has not been implemented here.

## Reference rules and usability

For a table of recursive obligations $\Delta$, the new reference-clause
coverage rule is:

$$
\frac{\forall j.\;\exists i.\;\Delta(A_i,C_j)\land\Delta(C_j,A_i)}
 {\Delta\vdash\textstyle\bigwedge_i\mathsf{Ref}\,A_i
   \le\bigwedge_j\mathsf{Ref}\,C_j}.
$$

It justifies every target constraint by an equivalent source constraint. It
supports conjunction elimination and retention of multiple constraints without
solving arbitrary semantic emptiness. It is a sufficient rule; more consequences
might be provable with additional sound rules.

The semantic probe also establishes:

- `adm`: admissibility of reference conjunctions for arbitrary operand families.
- `congr_below`: guarded dependence on those operand families.
- `operands_agree`: all operands agree below the current observation budget,
  because each agrees with the same stored contract.
- `read_all`: a read yields a value meeting every operand at the available lower
  budgets, assuming the heap satisfies the world.
- `write_first`: writing a value meeting the first operand at those budgets
  preserves heap satisfaction, including aliases. The invariant agreements
  explain why a separate write obligation for every operand is unnecessary.
- `cyclic_inhabited`: repeated constraints on a recursive reference have a real
  inhabitant in a satisfying cyclic heap.

These are semantic heap rules. They do not themselves constitute a new full
program typing system.

## Declarative arrow and structural rules

Write $\Delta(A,B)$ for membership of the pair $(A,B)$ in a finite table of
recursive subtype obligations. The judgment $\Delta;L\vdash C\Rightarrow D$
(`PositiveRules.Arrow`) derives an arrow from a source overload $L$:

$$
\frac{}{\Delta;L\vdash\bot\Rightarrow D}
\qquad
\frac{(A,B)\in L\quad\Delta(C,A)\quad(B=\bot\lor\Delta(B,D))}
     {\Delta;L\vdash C\Rightarrow D}.
$$

Union-domain composition and guarded result combination are:

$$
\frac{\Delta;L\vdash C\Rightarrow D\quad\Delta;L\vdash C'\Rightarrow D}
     {\Delta;L\vdash C\lor C'\Rightarrow D}
$$

$$
\frac{\Delta;L\vdash C\Rightarrow B\quad\Delta;L\vdash C\Rightarrow B'\quad
      \forall i\in B,k\in B'.\;\mathsf{compatible}_G(i,k)\Rightarrow\Delta(\{i\},D)}
     {\Delta;L\vdash C\Rightarrow D}.
$$

`compatible` checks whether some clause under label $i$ has the same outer
shape as some clause under label $k$. A type label can denote multiple shapes.
The condition is sufficient, not an exact decision of joint inhabitation.
Repeated combination can use arbitrarily many source conjuncts. Singleton
splitting is derivable by finite union composition (`Arrow.split`).

Clause coverage (`Covers`) matches identical atomic shapes, uses the reference
rule above, and checks every target arrow from the source overload. Union
coverage expands the clauses under the source labels, *splits* each of them, and
matches every part by a covered clause under the target labels. A core judgment
$G\vdash_c S\le T$ requires a finite table containing $(S,T)$ whose every entry
passes this coverage rule. All cyclic premises occur under a reference or
function constructor. Only clause rows have clauses; a parameter or scheme row
of a source (see [Parameter and scheme rows](#parameter-and-scheme-rows)) must
reappear in the target, or the target must admit every value (`Opaque`):

$$
\frac{(S,T)\in\Delta\qquad
      \forall(A,B)\in\Delta.\;
      \Bigl(\forall i\in A.\;\mathsf{plain}_G(i)\lor i\in B\lor\top\in\mathsf{cl}_G(B)\Bigr)
      \land\forall a\in\mathsf{split}(\mathsf{cl}_G(A)).\;\exists b\in\mathsf{cl}_G(B).\;
      \Delta\vdash a\sqsubseteq b}
     {G\vdash_c S\le T}
$$

where $\mathsf{cl}_G(A)$ is the list of clauses of $A$'s clause rows
(`clausesOf`).

Record coverage reads the target's operands one by one. Writing $\Delta^{\pm}(A,B)$
for $\Delta(A,B)\land\Delta(B,A)$ and $\Phi=\varphi_0\cdots\varphi_m$ for the
source's invariant operands,

$$
\frac{\begin{array}{c}
\forall j,\,(\kappa{:}B)\in\varphi'_j.\;\exists(\kappa{:}A)\in\Phi.\;\Delta^{\pm}(A,B)\\
\forall(\kappa{:}B)\in\psi'.\;\exists(\kappa{:}A)\in\Phi\,\psi.\;\Delta(A,B)\qquad
\forall(\kappa{:}B)\in\omega'.\;\exists(\kappa{:}A)\in\Phi\,\omega.\;\Delta^{\pm}(A,B)
\end{array}}
{\Delta\vdash\mathsf{Ref}(\Phi;\psi;\omega)\sqsubseteq\mathsf{Ref}(\varphi'_0\cdots\varphi'_k;\psi';\omega')}
$$

(`CoversFields`, `CoversViews`, `CoversOptional`), and a `dict` target also
needs every index operand covered by a source index operand at a subtype. An
optional target field is met by a required or optional source field of the same
key; a required target field only by a required one, since neither a view nor
an optional field says the key is present. A construct signature is covered by
one taking as many parameters, each at least as wide, with a result at most as
wide:

$$
\frac{\forall(\vec C,D)\in M.\;\exists(\vec A,B)\in L.\;
      |\vec A|=|\vec C|\land\forall i.\,\Delta(C_i,A_i)\land\Delta(B,D)}
     {\Delta\vdash\mathsf{Ctors}\,L\sqsubseteq\mathsf{Ctors}\,M}
\qquad
\frac{}{\Delta\vdash c\sqsubseteq c}\ \ c\in\{\mathsf{bigint},\mathsf{symbol}\}.
$$

Splitting (`splitClause`) replaces a source $\mathsf{bool}$ clause with the pair
$\mathsf{true},\mathsf{false}$ and leaves every other clause alone. It is
meaning preserving — `splitClause_sem` proves the union of the parts denotes
exactly the original clause, and `source_sem` lifts that to a label set — so it
adds no power beyond the model. It is what lets a single source clause be
discharged by *several* target clauses while `Covers` itself stays
clause-to-clause: $\mathsf{bool}\le\mathsf{true}\mid\mathsf{false}$ is derivable
because each singleton covers one part, and $\mathsf{bool}\le\mathsf{bool}$ still
is because a $\mathsf{bool}$ target covers both. $\mathsf{bool}\le\mathsf{true}$
remains underivable. $\mathsf{bool}$ is the only clause of this language with a
finite set of inhabitants that is not already a singleton, so it is the only one
that splits.

The final judgment `Sub` adds:

$$
\frac{G\vdash_c S\le T}{G\vdash S\le T}
\qquad
\frac{\forall i\in S.\ i\in T}{G\vdash S\le T}
\qquad
\frac{G\vdash S\le U\quad G\vdash U\le T}{G\vdash S\le T}.
$$

Two more rules read scheme rows ([Parameter and scheme rows](#parameter-and-scheme-rows)).
Both rules turn on which **parameter rows a row depends on**. A free-variable
certificate $V$ on a domain $D$ (`FreeOk`) assigns each $i\in D$ a set $V(i)$
of parameter rows, with $D$ closed under what its rows read (a clause row its
operands, a scheme row its signature types), such that

$$
i\ \text{a parameter row}\Rightarrow i\in V(i),\qquad
l\in\mathsf{reads}_G(i)\Rightarrow V(l)\subseteq V(i)\cup\mathsf{binders}(i),
$$

where $\mathsf{binders}(i)$ is empty unless $i$ is a scheme row. A scheme's own
binders are therefore not free in it. A row means the same at two assignments
that agree on $V(i)$ (`agree_free`).

An **instance map** $\theta$ sends labels to types; a label it does not name is
its own image, and $\theta(A)$ is the union of the images of $A$'s labels. For
the scheme's binders $\vec p$, let the **moved** binders $M$ be $\vec p$ and the
binders of every scheme row in $D$. $\theta$ is an instance on $(D,V)$
(`InstOk`) when $V$ is a free-variable certificate on $D$, each $\theta(p)$ for
$p\in\vec p$ lies in $D$ with no free row in $M$, and every $i\in D$ is one of:

- a binder $i\in\vec p$, a parameter row;
- another parameter row, with $\theta(i)=\{i\}$;
- **rigid**: $\theta(i)=\{i\}$ and $V(i)\cap M=\emptyset$;
- a clause row with $\theta(i)=\{j\}$, $j$ a clause row and $G(j)=G(i)[\theta]$
  (every operand of every clause mapped);
- a scheme row $(\vec q;\Sigma')$ with $\theta(i)=\{j\}$, $j$ the scheme row
  $(\vec q;\Sigma'[\theta])$ and $\vec q\cap\vec p=\emptyset$.

A receiver such as `Promise<number>`, whose `then` mentions `then`'s own
binders only under them, is rigid. Read at the assignment giving each binder
$p$ the meaning of $\theta(p)$, every $A\subseteq D$ means exactly $\theta(A)$
(`inst_row`, `inst_type`, proved at every assignment that differs from the
graph's only on $M$). Then, with
$\sigma[\theta]=(\theta(Q),\theta(\vec C),\theta(D))$ for a signature
$\sigma=(Q,\vec C,D)$:

$$
\frac{i\ \text{a scheme row}\ (\vec p;\Sigma)\quad
      \theta\ \text{an instance on}\ (D,V)\quad
      T\equiv_G\mathsf{arrs}(L)\quad
      \forall\tau\in L.\;\exists\sigma\in\Sigma.\;\sigma\subseteq D\land\tau=\sigma[\theta]}
     {G\vdash\{i\}\le T}\ \textsc{inst}
$$

A type below a scheme's signatures with the binders opaque is below the scheme,
provided none of its free parameter rows is a binder:

$$
\frac{j\ \text{a scheme row}\ (\vec p;\Sigma)\quad
      U\equiv_G\mathsf{arrs}(\Sigma)\quad
      V\ \text{a free-variable certificate on}\ D\quad
      \forall l\in S.\;l\in D\land V(l)\cap\vec p=\emptyset\quad
      G\vdash S\le U}
     {G\vdash S\le\{j\}}\ \textsc{gen}
$$

`Sub.inst` and `Sub.gen` are these rules. The second is sound because $S$ means
the same at any two assignments that differ only on $\vec p$ (`agree_free`),
and because every rule of `Sub` holds at every assignment (`Sub.sound_at`): the
premise $G\vdash S\le U$, derived once, holds at each instantiation of $\vec p$.

Reflexivity and invariance under reordering or duplicating union labels follow
(`Sub.refl`, `Sub.congr`). Transitivity composes completed proofs, not unchecked
back-references in a table. No general constructor-normalization theorem is
implied by the union-label congruence theorem.

## Certificate guarantees

`PositiveCertificates.lean` checks finite tables, arrow evidence, and explicit
structural proof trees. Its checker uses no semantic oracle or unbounded proof
search.

A proof is one of five forms. `core` carries a `Certificate`: the finite
candidate relation and its arrow evidence. `subset` is plain union inclusion of
the source labels in the target's. `trans` names an intermediate type and holds
a proof on each side. `inst` puts a scheme row below an instance of its
signatures: it carries the instance map, its domain and the domain's
free-variable certificate (`Sub.inst`). `gen` puts a type below a scheme row: it
carries a domain holding the type and its free-variable certificate, the type
stating the scheme's signatures with its binders opaque, and a proof of the
inclusion in that type (`Sub.gen`). All five are accepted, which is worth stating
separately from what the producer builds: `CertificateProducer` never emits
`trans`, and
[PROGRAM-TYPING.md](PROGRAM-TYPING.md#producing-evidence-from-supplied-claims)
records that its search does not enumerate transitivity derivations. That is a
restriction on search, not on the accepted language — a certificate written by
hand or by another producer may use `trans`, and the consumer checks it.

`check_sound` and `check_complete` prove:

$$
G\vdash S\le T\quad\Longleftrightarrow\quad
\exists p.\;\operatorname{check}(G,S,T,p)=\mathsf{true}.
$$

This is `derivable_iff_checked`, for the extended rules just specified. It is
not completeness for every inclusion true in the model. `SourceSub` applies the
same declarative judgment after normalization; `source_iff_checked` provides
the corresponding certificate theorem for source graphs.

Separately, `Sub.sound` proves semantic inclusion. `checkSource` normalizes a
positive graph and checks its proof; `accepted_source` composes checking,
rule soundness and normalization preservation:

$$
\operatorname{checkSource}(G,S,T,p)=\mathsf{true}
\Longrightarrow
\forall n,W,v.\;
\llbracket S\rrbracket_G(n,W,v)\Rightarrow
\llbracket T\rrbracket_G(n,W,v).
$$

`accepted_subsumption` transports an existing computation-safety judgment from
$S$ to $T$. It does not establish the initial judgment or a whole-program typing
theorem by itself. [PROGRAM-TYPING.md](PROGRAM-TYPING.md) now supplies the
separate typing theorem and incorporates checked subsumption. The operational
language and trust boundary are documented in
[SEMANTICS.md](SEMANTICS.md).

## Rigid inclusion

Direct types are a rigid name, ground graph labels, or a callable over direct
types. Inclusion under declared bounds, `RigidJudgments.Sub ps a b`, is stated
by four rules and no algorithm: a rigid name is below itself; it is below
whatever its declared bound is below; ground label lists are compared by
inclusion; and a callable is below another when the other's parameters are
each below its own and its result is below the other's. There is no
transitivity rule; the chain rule carries it. `Sub.refl` holds for every type.

`Sub.sound` proves the judgment semantically sound on its own: under any
assignment satisfying the declared bounds, a derivable inclusion is an
inclusion of families. It does not go through the executable relation.

`Ty.leUnder` is the executable relation, a fuelled walk. `leUnder_iff_Sub`
proves, for well-formed parameter lists,

$$
\mathsf{leUnder}(\bar P, a, b) = \mathsf{true}
\quad\Longleftrightarrow\quad
\bar P \vdash a \le b .
$$

Well-formed means the names are distinct, every rigid bound names an earlier
parameter, and every bound is ground or rigid; `SourceJudgments.parametersOf_wellFormed`
proves every list the source checker builds is. The left-to-right direction,
`Sub_of_leUnder`, needs no hypothesis.

Separately, the work exposed insufficient fuel outside the theorem's
well-formed-bound restriction. The old fuel charged for
the structure of the two sides and one step per parameter, and a parameter
bounded by a deep callable is declaratively below that callable while the
walk into the bound needs as many steps as the callable is deep.
`RigidJudgments.counterexample_derivable` is the derivation, and two kernel
guards record that the old fuel rejects it and the repaired fuel, which also
pays for each parameter's bound, accepts it. Callable bounds are excluded by
`WellFormed`, so this regression does not establish completeness for callable
bounds in general.

### Planned completeness extension: callable upper bounds

The restriction matches the current source bound parser and simplifies the
proof; it is not a design restriction on the eventual language or evidence
that completeness with callable bounds is false. Both `Sub.sound` and
`Ty.leUnder_sound` already cover callable bounds. What remains unproved is
that the executable relation accepts every derivable inclusion with such
bounds; repairing the one fuel counterexample does not settle that question.

First extend well-formedness to acyclic callable bounds whose rigid references,
including references inside parameter and result types, name earlier binders.
Prove a sufficient fuel bound or replace the walk with an algorithm whose
termination measure accounts for entering bounds and reversing comparisons
at callable parameters. Then extend `leUnder_iff_Sub` and the source bound
parser, preserving the existing semantic soundness connection. This is
expected to be achievable without changing the declarative rules, but that
expectation is not a theorem. Recursive bounds are a separate extension and
must not be admitted merely by removing the current restriction or increasing
fuel again.

## Scope and next decisions

The representational blocker for positive intersections of references is
removed. This graph syntax can retain general finite positive formulas at
program-type nodes and under guarded recursive reference/arrow operands. The
clause grammar does not add negation, difference, primitive types other
than null/undefined/boolean, object records, or a surface `extends` language.
First-order rigid parameters are a layer over graph labels, not a new clause:
a parameter is a label whose meaning is an assignment `η`, and substituting a
type argument is interpreting the original syntax under `η[T ↦ ⟦A⟧]`. See
[TypeParams.lean](lean/Verification/Model/Types/TypeParams.lean). That
layer's source connection is the identity scheme, `T extends boolean`, T-copy
bodies, and the identity/cell aliases; it does not yet handle higher-rank
polymorphism or parameter-changing recursion.

### Parameter and scheme rows

A graph's label is one of three kinds of row. A clause row means its clauses. A
parameter row means what the graph's assignment `env` gives it, a family of
closed values. A scheme row means one callable meeting its signatures at every
reassignment of its binders, which are parameter rows. The denotation is one
guarded fixed point over (assignment, label) (`qDenote`), and `meaning G` reads
it at `G.env`. No check reads `env`, so every theorem proved for all graphs
holds at every reassignment.

Formally, with $\eta$ an assignment of admissible families of closed values to
labels and $\llbracket A\rrbracket^\eta=\bigcup_{i\in A}\llbracket i\rrbracket^\eta$,
the denotation is the guarded fixed point of

$$
\llbracket i\rrbracket^\eta=
\begin{cases}
\eta(i) & i\ \text{a parameter row},\\[2pt]
\bigl\{\,v\;\bigm|\;\mathsf{Invocable}(v)\land\forall\vec X.\;
  v\in\mathsf{Calls}\bigl(\{(\llbracket Q\rrbracket^{\eta'},\llbracket\vec C\rrbracket^{\eta'},\llbracket D\rrbracket^{\eta'})\mid(Q,\vec C,D)\in\Sigma\}\bigr),\
  \eta'=\eta[\vec p\mapsto\vec X]\,\bigr\}
  & i\ \text{a scheme row}\ (\vec p;\Sigma),\\[2pt]
\textstyle\bigcup_{c\in G(i)}\llbracket c\rrbracket^\eta & i\ \text{a clause row},
\end{cases}
$$

where $\vec X$ ranges over admissible families of closed values, one per binder
(`qLayer`, `qDenote`), and $\llbracket A\rrbracket_G=\llbracket A\rrbracket^{G.\mathit{env}}$
is `meaning`. A member of a scheme row meets each instance's signatures
(`scheme_elim`), and a callable meeting them at every instantiation is a
member (`scheme_intro`). Without scheme rows this is the parametric semantics
`denoteP` (`qDenote_no_schemes`).

Only clause rows have clauses. A type holding a parameter or scheme row has no
expansion, so no rule that reads a clause (`Represents`, `Answers`, the atoms
of heap knowledge) applies to it. In subtyping, such a row of the source must
appear in the target, or the target must admit every value (`Opaque`).

Two subtyping rules read scheme rows. `Sub.inst` puts a scheme below an arrow
type whose signatures are its own under an instance map, which sends each
binder to a type and each clause row a signature reads to a clause row holding
its clauses with every operand mapped; read at the instance's assignment, a
mapped type means exactly its image. `Sub.gen` puts a type below a scheme when
it is below the scheme's signatures with the binders opaque and none of the
rows it reads is a binder. Subtyping is sound at every assignment
(`Sub.sound_at`): the judgments read a graph only through its rows. Scheme
rows are the graph form of generic methods, stage 2 of the quantified-types
plan in [the producer's README](ocaml-producer/README.md); the layer below
predates them.

### Quantified scheme layer

Quantified local callables form a second layer rather than a graph clause.
`TypeSchemes.schemeT` denotes one callable satisfying its signatures for every
admissible assignment while retaining the same captured world and field
contracts. The current source slice checks one local closure under
rigid binders and their bounds, then compiles each checked ground elimination
to fixed or variadic graph signatures. Thus the finite positive graph remains the ground evidence language;
the universal scheme is neither erased to one observed arrow nor encoded as a
recursive graph row.

For a scheme $S$, outer assignment $\eta_0$, and assignment $\eta$, define

$$
\begin{aligned}
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
\;\overset{\mathrm{def}}{\Longleftrightarrow}\;&
\mathsf{ClosedAssign}_P(\eta)
\;\land\;
\mathsf{Satisfies}_{G,P}(\eta,S.\mathsf{bounds})\\
&\land\;
\forall i\notin S.\mathsf{binders}.\;\eta(i)=\eta_0(i).
\end{aligned}
$$

Writing $\mathsf{Sig}_{G,P,\eta}(S)$ and $\mathsf{RestSig}_{G,P,\eta}(S)$
for its fixed and variadic signatures interpreted under $\eta$, its denotation is exactly

$$
\begin{aligned}
\llbracket S\rrbracket^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
\;\overset{\mathrm{def}}{\Longleftrightarrow}\;&
\mathsf{Invocable}(v)\\
&\land\;\forall\eta.\;
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
\Rightarrow
(\mathsf{Calls}(\mathsf{Sig}_{G,P,\eta}(S),n,W,v)
\land\mathsf{Rests}(\mathsf{RestSig}_{G,P,\eta}(S),n,W,v)).
\end{aligned}
$$

The quantifier is inside membership of one $v$ at one $n,W$. It therefore
cannot be witnessed by allocating or checking a different closure for each
observed call. The last conjunct of `Instance` keeps every non-binder meaning,
including types used by the captured environment, fixed across instantiations.

The program-typing theorem now incorporates these certificates, including an
overload domain-splitting example. Executable program evidence checking and
local supplied-environment edge obligations are now proved as well. The next
integration work is source extraction and faithful claim translation. A bounded
producer constructs checked evidence from supplied point annotations, and the
[serialized consumer](REQUEST-PROTOCOL.md) checks serialized calculus requests.
The graph consumer covers every actual node and outgoing edge and proves global
safety, including cycles and explicit slot maps. Producer success is checked;
producer completeness is not claimed. A textual type-to-graph compiler still needs its own correctness
account.
Do not resume semantic completeness research as a prerequisite: normalization
preservation and subtype soundness already give the guarantees needed here.

Implementation files:

- `lean/Verification/Model/Types/ReferenceConjunctions.lean`
- `lean/Verification/Model/Types/PositiveNormalization.lean`
- `lean/Verification/Model/Types/PositiveGraphs.lean`
- `lean/Verification/Model/Types/PositiveRules.lean`
- `lean/Verification/Model/Types/PositiveCertificates.lean`
- `lean/Verification/Model/Tests/PositiveNormalizationTests.lean`
- `lean/Verification/Model/Types/TypeParams.lean`
- `lean/Verification/Model/Source/GenericSource.lean`
- `lean/Verification/Model/Source/GenericAlias.lean`

Tests cover distribution, cross-shape elimination, retained incompatible
contracts, nested constraints, cyclic normalization/checking, domain splitting,
three-conjunct combination, and rejection of invented constraints or false
bottom claims. The program-typing tests additionally cover application, binding,
stateful overloaded dispatch and checked subsumption.

Validation: `lake build` checks the complete Lean library and executable,
including positive and negative certificate tests and the program-typing
development. The maintained
files contain no `sorry` or custom axioms. `check_sound` uses `propext`;
`check_complete` uses `propext` and `Quot.sound`; semantic soundness also uses
standard `Classical.choice`.
