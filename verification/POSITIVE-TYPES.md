# Positive types: reference constraints and checked normalization

This specifies the maintained type representation, state-assertion grammar and
subtype rules. [State assertions](#state-assertion-grammar) extend point claims;
they are separate from ordinary types and their normalization. Lean
proves positive normalization preserves recursive type semantics, the declarative
rules are sound, and the certificate checker is sound and complete for those
rules. A first closed null/boolean source slice is connected to this consumer. Its foundation and integration boundary are in [SEMANTICS.md](SEMANTICS.md).

## Representation and mathematical rules

A label names a whole type. A graph body is a finite positive formula:

$$
P ::= \bot\mid c\mid P\lor P\mid P\land P.
$$

A clause is an atom, a reference conjunction, or an arrow intersection:

$$
c ::= \mathsf{null}\mid\mathsf{bool}\mid\mathsf{boolLit}(b)\mid
       \mathsf{refs}(A;B_1,\ldots,B_k)\mid
       \mathsf{arrs}((C_1,D_1),\ldots,(C_m,D_m)).
$$

Here $b$ is true or false. A singleton denotes exactly that boolean value at
every budget. Its additional atomic rules are

$$
\mathsf{boolLit}(b)\leq\mathsf{bool},\qquad
\mathsf{boolLit}(b)\land\mathsf{bool}=\mathsf{boolLit}(b),\qquad
\mathsf{boolLit}(\mathsf{true})\land\mathsf{boolLit}(\mathsf{false})=\bot.
$$

Each operand $A,B_i,C_i,D_i$ is a finite union-list of graph labels. The
reference list is nonempty because $A$ is explicit. It means:

$$
\llbracket\mathsf{refs}(A;B_1,\ldots,B_k)\rrbracket
=\llbracket\mathsf{ref}(A)\rrbracket\cap
 \bigcap_i\llbracket\mathsf{ref}(B_i)\rrbracket.
$$

All conjuncts constrain the **same location and its one stored invariant**.
They are not multiple separately allocated cells, and they are not replaced
by a single invariant over the intersection of their operands. A plain
reference is `refs A []`. Function clauses retain the existing intersection
of arrows, including the empty overload list, which denotes closed lambdas without call obligations.

Normalization returns a finite union-list of clauses:

$$
\begin{aligned}
N(\bot)&=[],&N(c)&=[c],\\
N(P\lor Q)&=N(P)+N(Q),\\
N(P\land Q)&=\mathop{\mathrm{concat}}_{c\in N(P),d\in N(Q)}\mathrm{meet}(c,d).
\end{aligned}
$$

`meet` discards different outer shapes, preserves identical atoms, and uses:

$$
\begin{aligned}
\mathrm{meet}(\mathsf{refs}(A;\vec B),\mathsf{refs}(C;\vec D))
  &=[\mathsf{refs}(A;\vec B+C+\vec D)],\\
\mathrm{meet}(\mathsf{arrs}(L),\mathsf{arrs}(M))
  &=[\mathsf{arrs}(L+M)].
\end{aligned}
$$

Here $+$ denotes list concatenation, with $C$ inserted as one operand.
Nothing is distributed through a reference operand or an arrow result.

For example:

$$
\mathsf{ref}(A)\land(\mathsf{ref}(B)\lor\mathsf{null})
\quad\longmapsto\quad[\mathsf{refs}(A;B)].
$$

The normalizer retains incompatible reference constraints. In this indexed
model, `refs null [bool]` has a zero-budget witness but has no members at any
positive budget. A nested analogue has a witness at budget one in a satisfying
cyclic heap. These are checked examples, so replacing all such clauses by
bottom would be an incorrect normalization.

## State-assertion grammar

Point claims can combine ordinary types with facts about the current execution
state. The following notation describes the finite assertion layer; it does not
add constructors to the ordinary type grammar above. Let $x$ name an environment
slot, $A$ and $B$ be ordinary types, and $R$ be a finite literal set:

$$
\begin{aligned}
a &::= \mathsf{null}\mid\mathsf{true}\mid\mathsf{false},\\
R &::= \{a_1,\ldots,a_k\}\quad(k\geq 0),\\
J &::= \top\mid x:A\mid\operatorname{cell}(x,R)
       \mid\operatorname{val}(x,R)\mid J\land J.
\end{aligned}
$$

| Assertion | What it states |
| --- | --- |
| $x:A$ | The value in slot $x$ belongs to the ordinary type $A$, interpreted against the current world and budget. |
| $\operatorname{cell}(x,R)$ | Slot $x$ holds a location whose current heap contents belong to $R$. It does not specify or change that location's storage invariant. |
| $\operatorname{val}(x,R)$ | The immutable value in slot $x$ belongs to $R$. This is a snapshot fact, independent of subsequent heap mutation. |
| $\top$, $J_1\land J_2$ | No requirement, or both requirements. Conjunction does not assert ownership or disjoint locations. |

An empty literal set is an impossible content/value predicate, not an absent
assertion. There is no general assertion disjunction, negation or quantifier in
this finite grammar. The union within $R$ permits alternatives for one value;
it does not express correlations between different slots. Numbers and predicates
on nested references are not part of the implemented literal language.

The notation requested for source claims is an abbreviation:

$$
x:\{\mathsf{value}:B=R\}
\quad\equiv\quad
x:\mathsf{ref}(B)\ \land\ \operatorname{cell}(x,R).
$$

Here $\mathsf{ref}(B)$ abbreviates the ordinary clause
$\mathsf{refs}(B;)$, with no additional reference conjuncts. In displayed source
claims, the right side of `=` uses type-like spelling for the finite predicate:
`true` denotes $\{\mathsf{true}\}$ and `boolean` denotes
$\{\mathsf{true},\mathsf{false}\}$. Thus `{ value: boolean = true }` combines
`ref(boolean)` with a current-cell fact. It is neither `ref(true)` nor an
ordinary type operand that can be inserted into arrows or recursive type bodies.
Forgetting the cell assertion leaves `ref(boolean)` and loses information.

The implementation stores these conjunctions as an ordinary context $\Gamma$
plus `HeapKnowledge.Knowledge`: cell facts $\Delta$ and immutable-value facts $V$.
The grammar is mathematical notation for those components, not a new JSON or
TypeScript parser. `cell` corresponds to `HeapFacts.Holds`; `val` corresponds to
`HeapKnowledge.ValueHolds`. A source expression assertion uses its evaluated
result in place of $x$.

[Semantics](SEMANTICS.md#current-content-assertions-and-postconditions) defines
heap observations and their relationship to the world and satisfying heap.
[Program typing](PROGRAM-TYPING.md#checked-expression-postconditions) owns the
checked rules and fact transfer. [Source claims](SOURCE-CLAIMS.md#current-content-assertions)
owns the wire encoding and its restrictions. Expression checking is proved;
whole-source graph propagation of these facts remains integration work.

## Recursive normalization

A source graph maps each label to a formula; its normal form maps the same
label to a union-list of clauses:

$$
N(G)(i)=N(G(i)).
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
\llbracket N(G)\rrbracket=\llbracket G\rrbracket.
$$

This is a general theorem for the explicit graph syntax, not just an example
or an unrolling to a fixed depth. Arbitrarily nested positive types can be
presented by naming their guarded operands in the graph. A verified compiler
from textual type syntax to that graph has not been implemented here.

## Reference rules and usability

For a table of recursive obligations $\Delta$, the new reference-clause
coverage rule is:

$$
\frac{\forall B\in(C;\vec D).\;\exists A'\in(A;\vec B).\;
          \Delta(A',B)\land\Delta(B,A')}
 {\Delta\vdash\mathsf{refs}(A;\vec B)\le\mathsf{refs}(C;\vec D)}.
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
\frac{}{\Delta;L\vdash\varnothing\Rightarrow D}
\qquad
\frac{(A,B)\in L\quad\Delta(C,A)\quad(B=\varnothing\lor\Delta(B,D))}
     {\Delta;L\vdash C\Rightarrow D}.
$$

Union-domain composition and guarded result combination are:

$$
\frac{\Delta;L\vdash C\Rightarrow D\quad\Delta;L\vdash C'\Rightarrow D}
     {\Delta;L\vdash C+C'\Rightarrow D}
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
coverage expands the clauses under the source labels and matches each by a
covered clause under the target labels. A core judgment $G\vdash_c S\le T$
requires a finite table containing $(S,T)$ whose every entry passes this coverage
rule. All cyclic premises occur under a reference or function constructor.

The final judgment `Sub` adds:

$$
\frac{G\vdash_c S\le T}{G\vdash S\le T}
\qquad
\frac{\forall i\in S.\ i\in T}{G\vdash S\le T}
\qquad
\frac{G\vdash S\le U\quad G\vdash U\le T}{G\vdash S\le T}.
$$

Reflexivity and invariance under reordering or duplicating union labels follow
(`Sub.refl`, `Sub.congr`). Transitivity composes completed proofs, not unchecked
back-references in a table. No general constructor-normalization theorem is
implied by the union-label congruence theorem.

## Certificate guarantees

`PositiveCertificates.lean` checks finite tables, arrow evidence, and explicit
structural proof trees. Its checker uses no semantic oracle or unbounded proof
search. `check_sound` and `check_complete` prove:

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

## Scope and next decisions

The representational blocker for positive intersections of references is
removed. This graph syntax can retain general finite positive formulas at
program-type nodes and under guarded recursive reference/arrow operands. The
extension does not add negation, difference, polymorphism, primitive types other
than null/boolean, object records, or a surface `extends` language.

The program-typing theorem now incorporates these certificates, including an
overload domain-splitting example. Executable program evidence checking and
local supplied-environment edge obligations are now proved as well. The next
integration work is source extraction and faithful claim translation. A bounded
producer constructs checked evidence from supplied point annotations, and the
[serialized consumer](REQUEST-PROTOCOL.md) checks versioned calculus requests.
The graph consumer covers every actual node and outgoing edge and proves global
safety, including cycles and explicit slot maps. Producer success is checked;
producer completeness is not claimed. A textual type-to-graph compiler still needs its own correctness
account.
Do not resume semantic completeness research as a prerequisite: normalization
preservation and subtype soundness already give the guarantees needed here.

Implementation files:

- `lean/Verification/ExperimentState/ReferenceConjunctions.lean`
- `lean/Verification/ExperimentState/PositiveNormalization.lean`
- `lean/Verification/ExperimentState/PositiveGraphs.lean`
- `lean/Verification/ExperimentState/PositiveRules.lean`
- `lean/Verification/ExperimentState/PositiveCertificates.lean`
- `lean/Verification/ExperimentState/PositiveNormalizationTests.lean`

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
