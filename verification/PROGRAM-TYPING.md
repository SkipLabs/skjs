# Program typing over positive recursive types

[ProgramTyping.lean](lean/Verification/ExperimentState/ProgramTyping.lean) gives
syntactic program-typing rules for the stateful language. Its fundamental theorem
connects those rules to the model in [SEMANTICS.md](SEMANTICS.md). Subsumption uses
the certificate checker specified in [POSITIVE-TYPES.md](POSITIVE-TYPES.md).
The ordinary and graph rules below are used by the current verifier, as are the
[current-content rules](#current-content-rules-semantic-layer): supplied source
observations reach checked obligations, specified under
[source observation checkpoints](#source-observation-checkpoints). This document owns
rule statements, side conditions, soundness scope and evidence construction;
[Design](DESIGN.md) owns the integration roadmap.

## Notation

| | Ranges over |
| --- | --- |
| $t$, $u$ | [terms](SEMANTICS.md#operational-language) |
| $t_1$, $t_2$ | a branch's two arms, in that order |
| $a$, $a'$ | terms, where a rule admits an arbitrary one rather than a variable |
| $x$, $y$, $z$ | variables, which are terms |
| $c$ | a term in condition position |
| $\gamma$ | a [clause](POSITIVE-TYPES.md#representation-and-mathematical-rules) |
| $r$ | the binding a rule gives its result |
| $k$ | one of the tests in [the operational language](SEMANTICS.md#operational-language) |
| $A$, $B$, $C$ | types, each a finite list of graph labels read as their union |
| $R$ | a finite set of constants |
| $\operatorname{lits}(A)$ | the constants $A$ denotes, defined only for a primitive $A$ (`literals`) |
| $G$ | the normalized positive graph |
| $\Gamma$ | a typing context, one type per variable |
| $\Pi$, $\Sigma$ | the [equality and heap parts](#checked-expression-postconditions) of the assertion state |
| $\rho$, $h$, $W$, $n$ | an environment, heap, world and budget, from [the model](SEMANTICS.md#types-worlds-and-heaps) |
| $\Delta$ | a target claim environment, and in [POSITIVE-TYPES](POSITIVE-TYPES.md) a table of subtype obligations |

$r$ never names an operand, and a premise can never mention it: it is bound by
the rule's conclusion and scoped to the postcondition.

## Expressions

Typing a term against the positive graph, with no notion of state. Everything
later rests on this layer and none of it changes these rules.

### Judgments and constructor views

Fix a normalized positive graph $G$. A type $A$ is a finite list of graph labels,
interpreted as their union. Write $A\equiv_G\gamma$ when expanding those labels
yields exactly the singleton clause $[\gamma]$. This is a finite syntactic equality, not a
semantic-equivalence oracle. Below, writing a constructor as a type abbreviates
such a view of its graph labels.

The judgment $\Gamma\vdash_G t:A$ is `HasTy`. The rules are:

$$
\frac{\Gamma(x)=A}{\Gamma\vdash_G x:A}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{null}:\mathsf{Null}}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{undefined}:\mathsf{Undefined}}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{true},\mathsf{false}:\mathsf{Bool}}
$$

Singleton introduction is also available, retaining the ordinary Boolean rules:

$$
\frac{}{\Gamma\vdash_G \mathsf{true}:\mathsf{boolLit}(\mathsf{true})}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{false}:\mathsf{boolLit}(\mathsf{false})}.
$$

$$
\frac{\forall(A,B)\in L.\;\Gamma,x:A\vdash_G t:B}
     {\Gamma\vdash_G \lambda x.t:\bigwedge_{(A,B)\in L}(A\to B)}
\qquad
\frac{\Gamma\vdash_G f:\bigwedge_{(C,D)\in L}(C\to D)
      \quad(A,B)\in L\quad\Gamma\vdash_G a:A}
     {\Gamma\vdash_G f(a):B}
$$

$$
\frac{\Gamma\vdash_G a:A\quad\Gamma,x:A\vdash_G b:B}
     {\Gamma\vdash_G \mathsf{let}\ x=a\ \mathsf{in}\ b:B}
$$

`let` is represented by application of a lambda in the operational language;
it does not require allocating a type-graph label for that intermediate lambda.

$$
\frac{\Gamma\vdash_G a:A}{\Gamma\vdash_G\mathsf{alloc}(a):\mathsf{Ref}(A)}
\qquad
\frac{\Gamma\vdash_G a:\mathsf{Ref}(A)}{\Gamma\vdash_G\mathsf{read}(a):A}
$$

$$
\frac{\Gamma\vdash_G a:\mathsf{Ref}(A)\quad\Gamma\vdash_G a':A}
     {\Gamma\vdash_G\mathsf{write}(a,a'):\mathsf{Null}}
\qquad
\frac{\Gamma\vdash_G t:A\quad\operatorname{check}(G,A,B,p)=\mathsf{true}}
     {\Gamma\vdash_G t:B}
$$

For branching, $\operatorname{Answers}_G(A,k,q)$ checks that every expanded
clause of $A$ gives the same Boolean answer $q$ to shape test $k$:

$$
\frac{\Gamma(x)=A\quad\operatorname{Answers}_G(A,k,q)
      \quad(q=\mathsf{true}\Rightarrow\Gamma\vdash_G t_1:B)
      \quad(q=\mathsf{false}\Rightarrow\Gamma\vdash_G t_2:B)}
     {\Gamma\vdash_G\mathsf{if}\ k(x)\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:B}.
$$

The shape-test rule checks each overload body under its own argument type. It
handles shape dispatch between overloads.

Ordinary Boolean conditionals use a separate rule. Define
$\operatorname{Boolean}_G(C)$ as
$\operatorname{Answers}_G(C,\mathsf{isBool},\mathsf{true})$; this accepts Boolean
singleton unions as well as the Boolean clause.

$$
\frac{\Gamma\vdash_G c:C\quad\operatorname{Boolean}_G(C)
      \quad\Gamma\vdash_G t_1:A\quad\Gamma\vdash_G t_2:A}
     {\Gamma\vdash_G\mathsf{if}\ c\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
$$

A condition with a proved singleton type needs only its reachable arm. For
$q\in\{\mathsf{true},\mathsf{false}\}$, write $B_q$ for a type represented by
$\mathsf{boolLit}(q)$, and let $t_q$ select the arm that $q$ reaches:

$$
\frac{\Gamma\vdash_G c:B_q\qquad\Gamma\vdash_G t_q:A}
     {\Gamma\vdash_G\mathsf{if}\ c\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
$$

`ifKnown q` carries two proofs: one for the condition at its singleton type,
and one for the selected arm. This is a typing rule, not constant folding:
the condition still runs, and all of its heap effects precede the arm. The Lean
soundness proof uses evaluation-context composition and consumes the ordinary
conditional step. A checked execution example includes a condition that writes
through a reference and an unreachable stuck arm.

The general Boolean rule requires both branches at the supplied result type
$A$. No least-upper-bound is computed. Both use the same context: that rule
does not justify narrowed branch environments. Another rule handles a directly
tested immutable variable. Write $\Gamma[x:=T]$ for replacing $x$'s type:

$$
\frac{\Gamma(x)=C\quad\operatorname{Boolean}_G(C)
      \quad\Gamma[x:=\mathsf{True}]\vdash_G t_1:A
      \quad\Gamma[x:=\mathsf{False}]\vdash_G t_2:A}
     {\Gamma\vdash_G\mathsf{if}\ x\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
$$

Here $\mathsf{True}$ and $\mathsf{False}$ must expand to the corresponding singleton
clauses. `HasTy.ifBoolVar` proves this rule sound: the selected branch's actual
value justifies the changed binding, and all others retain their meanings.
It neither refines mutable heap contents nor supplies general union splitting.
Graph edges use the common [observation-based refinement contract](#refinement-under-an-observed-outcome)
below, currently connected to Boolean dispatch.

Reference rules use a single invariant operand; eliminating a conjunction to such a reference view
can be justified by subsumption. No direct multi-contract program rule is assumed.

### Eliminating a variable's union type

A finite union can be split in one immutable binding. Write $[a]$ for
one graph label viewed as a type. Every member must establish the same term and
result; all other bindings retain their original types:

$$
\frac{\Gamma(x)=C\qquad
      \forall a\in C.\;\Gamma[x:=[a]]\vdash_G t:A}
     {\Gamma\vdash_G t:A}.
$$

`unionVar i` carries one premise for each label in $C$, in list order. The checker
rejects missing alternatives, changed terms/results, and changes to unrelated
bindings. An empty union needs no premises because that input environment has
no inhabitants. Soundness chooses the member containing the actual immutable
value and applies that premise's existing world-indexed soundness theorem.
There is no runtime case split added by this rule and no join computation.

Combined with `ifTag`, this checks a term such as
`if isNull(x) then true else x` under `x : Null | Bool`, at result `Bool`.
Proof search uses the rule for tag tests over explicit unions of labels. It does
not repeatedly split a singleton label whose graph definition itself contains
mixed shapes; that representation needs additional decomposition rules.

### Binding and soundness

`Bindings.lean` defines de Bruijn scope, simultaneous closing substitution, and
its application law:

$$
(\operatorname{close}_{\rho}(\lambda x.b))(a)
\longrightarrow \operatorname{close}_{a::\rho}(b).
$$

The formal statement is `instantiate_beta`; environment entries must be closed.
Arrow membership explicitly requires a closed lambda, so every value in a
positive graph type is both a value and closed (`meaning_value`). Semantic
environments retain these properties when extended, when their world grows,
and when their observation budget decreases.

`HasTy.sound` proves:

$$
\Gamma\vdash_G t:A\ \land\ \operatorname{EnvOk}_G(\Gamma,\rho,n,W)\ \land\
\operatorname{WorldAdm}(W)\ \land\ \operatorname{HeapOk}(n,W,h)
\ \Longrightarrow\
\operatorname{Safe}(\llbracket A\rrbracket_G,n,W,h,\operatorname{close}_{\rho}(t)).
$$

`HasTy.closed_safe` specializes this to a closed program with an empty typing
environment. It explicitly requires the term to be scoped: the total semantic environment
must not silently supply meanings for unbound source variables. Safety is partial
correctness and absence of stuck execution, not termination.

The general evaluation-context lemma `bind` composes computations across heap
changes and future worlds. The typing theorem is an induction on derivations;
none of its constructor rules has a semantic safety premise.

### Integration example

`ProgramTypingTests.lean` derives safety for a program equivalent to:

```text
let r = alloc true;
let f = x => if isNull x then read r else null;
let alias = r;
write alias false;
f(true);
f(null)
```

One closure has both `Null → Bool` and `Bool → Null`. Before the final call, a
checked certificate widens that overload to `(Null | Bool) → (Null | Bool)` by
splitting the union domain. The program is safe in every admissible world and
satisfying heap. A separate execution theorem confirms it returns `false` from
an empty heap; the safety proof does not depend on that trace. A negative theorem
rules out any typing derivation for applying null as a function.

### Executable program evidence

`ProgramCertificates.lean` checks finite evidence trees. Each node contains a
sequent (context, term, result type), a rule name, and its premise trees.
Subsumption nodes carry the existing positive subtype certificate. Lambda nodes
must supply precisely one body derivation per overload entry, in order. The two
branch rules supply evidence for the selected branch; the shape-answer check
must justify that selection.

`checkTree` checks every local rule and premise tree. The public
`check G t A evidence` additionally binds the root to the **requested** program,
empty context and result type, and checks the entire program's scope. That last
check includes unselected branches and bodies of empty overloads. A certificate
cannot substitute another program or exploit a vacuous body obligation to hide
free variables.

Lean proves both directions:

$$
\operatorname{Scoped}(0,t) \land ([] \vdash_G t : A)
\quad\Longleftrightarrow\quad
\exists p.\; \operatorname{check}(G,t,A,p)=\mathsf{true}.
$$

In words: the program is closed and has a typing derivation exactly when some
finite evidence is accepted for that program and result type.

This is `derivable_iff_checked`: completeness for the declared typing rules,
including checked subsumption. It neither asserts completeness for semantic
membership nor supplies proof search. `accepted_safe` derives computation safety
directly from acceptance. Checker recursion follows the finite evidence tree;
there is no user-supplied fuel and no semantic level in the evidence.

The explicit sequents keep this initial in-memory format easy to inspect, at the
cost of repeating terms and contexts. This is not a commitment to a serialized
format. The in-memory producer below uses this interface; a decoder or compact
representation can be developed against it.

`ProgramCertificateTests.lean` supplies concrete executable evidence for the
stateful overload program above. Tests reject altered programs/result types,
missing overload premises, changed captured contexts, unjustified branch choices,
incorrect writes, malformed subtype evidence, extra premises and unbound variables.
Its safety theorem is obtained from the successful check, with no embedded typing
proof in the certificate.

## Control flow

A finite graph over those expressions: one term per node, an edge discipline
that transfers bindings, and a certificate that checks every node and edge.

### Supplied point claims and incoming edges

`PointClaims.lean` checks supplied type environments. Write $\Gamma \preceq_G \Delta$
when every slot in the target claim $\Delta$ has a source slot at the same
position in the incoming environment $\Gamma$, with a proved subtype relation:

$$
\Gamma \preceq_G \Delta
\quad\Longleftrightarrow\quad
|\Delta| \leq |\Gamma|
\;\land\;
\forall i < |\Delta|.\; \Gamma_i \leq_G \Delta_i.
$$

`checkEdge` takes one subtype certificate per target slot. Lean proves that
acceptance implies coverage and that every derivation of coverage has accepted
evidence. Coverage also transfers semantic environments: any concrete environment
meeting $\Gamma$ meets $\Delta$, with closed values preserved.

`checkEdge` is the position-preserving specialization: it can widen types and
forget a suffix. `checkMapped` additionally checks an explicit list of source
indices, with exactly one index and subtype certificate per target slot.
Repeated indices retain aliases, and an interior binding can be dropped.
Every selected source index must exist; no missing binding acquires a type from
the total environment's default value.

For a supplied map $m$, the rule and its semantic action are:

$$
\frac{
  |m|=|\Delta|
  \qquad
  \forall i<|\Delta|.\;m_i<|\Gamma|\;\land\;\Gamma_{m_i}\leq_G\Delta_i
}{
  \Gamma\preceq_G^{m}\Delta
}
\qquad
\operatorname{mapEnv}(m,\rho)(i)=\rho(m_i).
$$

`checkMapped_sound` proves mapped coverage, and `MappedCovers.env` proves that
this simultaneous selection preserves the target semantic environment in the
same world. It does not copy or change heap contents. The absent map means
identity selection, retaining the earlier edge interface.

`checkIncoming` checks each supplied predecessor against the supplied target
claim independently. No join is computed. When a computation binds a new result,
`checked_bind_claim` proves composition through the edge
$A :: \Gamma \preceq_G \Delta$ into a continuation checked under $\Delta$:

$$
\frac{
  \Gamma \vdash_G a : A
  \qquad A :: \Gamma \preceq_G \Delta
  \qquad \Delta \vdash_G b : B
}{
  \operatorname{Safe}\!\left(
    \llbracket B \rrbracket_G,n,W,h,
    \operatorname{close}_{\rho}
      (\mathsf{let}\;x=a\;\mathsf{in}\;b)
  \right)
}.
$$

The conclusion assumes that $\rho$ meets $\Gamma$ at budget $n$ and world $W$,
that $W$ is admissible, and that $h$ satisfies $W$. This is a semantic composition
theorem with checked evidence at both ends; its proof accommodates heap changes
and world extension. Tests cover two predecessors merging into `Null | Bool`,
rejected narrowing and slot invention or reordering, and a checked write followed
by a supplied claim and a read through the retained reference.

These are local obligations. `checkIncoming` checks the edges it is given;
it does not establish that they enumerate a graph's actual predecessors.
The graph checker below discharges that enumeration obligation.

### Checked control-flow graphs

`ControlFlow.lean` adds a finite control-flow graph over the existing expression
language. A program is a finite list of nodes indexed by label; each node is one
[term](SEMANTICS.md#operational-language) and one of these six continuations:

| Continuation | Action after evaluating the expression |
| --- | --- |
| `ret` | Return its value as the graph's declared result type. |
| `bind` to a target | Push the value, apply the target slot map, and enter its label. |
| `effect`, then a target | Discard the value, apply the target slot map, and enter its label. |
| `branch` | Select a target according to the Boolean value and apply its slot map. |
| `branchBind` | Select a target, push the tested Boolean, and apply its slot map with a singleton refinement. |
| `tagBind` | Test the returned value's shape, select a target, push that value, and apply its slot map with the refinement the answer justifies. |

Conditionals therefore exist at two levels: `if` inside a single node's term, and
these branch continuations between nodes. Source lowering uses the continuations
for statement control flow and the term form inside closure bodies and direct
proofs. It emits every continuation except plain `branch`, which remains
available to graphs written against the protocol directly.

A target contains its label and an optional slot map. These are executable
program data, shared by the machine and checker; evidence cannot supply a
different binding transfer. Numeric targets abbreviate an identity map. A bind
or `branchBind` map indexes the environment **after** pushing the result; effect
and ordinary branch maps index the unchanged incoming environment.

Node evidence supplies its entry environment, expression type and program
evidence, and exactly the edge certificates required by its continuation. It
also supplies an input fact context and an output fact context. Checked expression
evidence must establish the output from the input; every outgoing edge checks
fact entailment against its destination under the executable slot map. Ordinary
expressions discard cell facts; the [effect rules](#checked-expression-postconditions)
justify stronger postconditions. Fact transfer is checked on both branch edges;
Boolean branch outcomes refine cells only through checked, still-valid read
links. Tag outcomes currently retain facts without adding cell refinements.
`checkGraph` enumerates **every node in the actual program**. It requires one
certificate per node, binds expression evidence to that node's actual code,
checks scope, and obtains successor labels directly from the continuation.
Every target must exist in both the program and the certificate. Both branch
edges are checked even when the condition is a literal, and unreachable nodes
are checked too. Omitting a predecessor list cannot bypass these obligations.

`checkEntry` checks the graph and requires the start claim to equal a separately
supplied input context $\Gamma_0$, with an empty input fact context.
`accepted_inputs_safe` proves:

$$
\begin{gathered}
\operatorname{checkEntry}(G,R,P,C,p,\Gamma_0)=\mathsf{true}
\\
\land\;\operatorname{EnvOk}_G(\Gamma_0,\rho,n,W)
\land\;\operatorname{WorldAdm}(W)
\land\;\operatorname{HeapOk}(n,W,h)
\\
\Longrightarrow\quad
\operatorname{SafeGraph}_P(\llbracket R\rrbracket_G,n,W,h,\operatorname{at}(p,\rho)).
\end{gathered}
$$

[`SafeGraph` and the machine state $\operatorname{at}(p,\rho)$](SEMANTICS.md#computations-and-recursive-types)
are the graph-level analogues of `Safe`: the run starts at the entry label with
the input environment, and stays safe through every transition.
The arguments, world, heap and budget are arbitrary subject to these premises.
`checkClosed` is exactly `checkEntry` with an empty input context;
`accepted_closed_safe` retains the empty-world, empty-heap corollary.
`accepted_entry_safe` is the underlying theorem for a checked point and its
claimed environment and heap facts, both of which its caller must establish.
The proof inducts on execution budget, so it covers cycles without unrolling
the graph or computing invariants. Expressions use the existing small-step
relation, with `SafePost` carrying checked output facts to the continuation.
Node dispatch and control transfer each consume
one step; a control-flow cycle cannot masquerade as progress at zero cost.

`Transition.det` proves determinism of this combined machine.
`accepted_no_stuck` proves that after any finite actual execution, the machine
has returned a typed value or can take another step. `accepted_result` proves
that any returned value meets the declared result type at every positive
remaining budget, in an admissible world satisfied by the final heap. These
are safety and partial-correctness theorems, not termination guarantees.

`ControlFlowTests.lean` checks a cyclic program that creates an overloaded
closure over a Boolean cell, calls it, writes through the original reference,
traverses a back edge, calls the same closure again and returns `false`. Its
operational trace traverses the back edge; its safety theorem does not depend
on that trace. A separate diamond graph joins null and Boolean predecessors at
one supplied union claim. A nonterminating self-loop is also proved safe.
Negative tests reject invalid destinations, missing branch evidence, unjustified
merge narrowing, missing or extra node evidence, changed code and invalid starts.

The graph layer does not change the type-family or expression semantics.
Closures still contain expression-language bodies, not graph-backed function
bodies. Boolean result refinement is proved as described below. A primitive source slice with parameters
is connected; broader source extraction remains integration work. The next section supplies
an in-memory certificate producer; [REQUEST-PROTOCOL.md](REQUEST-PROTOCOL.md)
describes its serialized consumer boundary. No graph-level completeness theorem is claimed here; the
program-evidence and edge-evidence completeness results above retain their
stated scope.


#### Refinement under an observed outcome

[BranchRefinement.lean](lean/Verification/ExperimentState/BranchRefinement.lean)
uses one contract for Boolean equality and tag observations. An observation $o$
is either equality to a Boolean value or the result of a runtime tag test.
Define the semantic obligation:

$$
A\preceq_o B
\quad\Longleftrightarrow\quad
\forall n,W,v.\;
\bigl(v\in\llbracket A\rrbracket_{n,W}\land o(v)\bigr)
\Longrightarrow v\in\llbracket B\rrbracket_{n,W}.
$$

This is `ObservedSub`. The destination type $B$ is supplied. The contract does
not require computing a canonical intersection, difference, or filtered type.
It is a semantic specification; the executable checker uses sufficient finite
checks, not a semantic oracle. No completeness of these checks is claimed.

`ObservedCovers` checks each destination slot selected by a map $m$. For the
tested slot $i$, it requires $\Gamma(i)\preceq_o\Delta(j)$; other selected slots
require ordinary subtyping. The common environment theorem is:

$$
\frac{
 \operatorname{EnvOk}_G(\Gamma,\rho,n,W)
 \quad o(\rho(i))
 \quad \operatorname{ObservedCovers}_G(\Gamma,\Delta,i,o,m)
}{
 \operatorname{EnvOk}_G(\Delta,\operatorname{mapEnv}(m,\rho),n,W)
}.
$$

`checkObserved` checks slot existence, map and evidence lengths, and each of
these obligations. `checkObserved_sound` and `ObservedCovers.env` prove the
common path. The observation is established by execution, never accepted as a
producer assertion. Heap contents are not refined.

Two implementations discharge the tested-slot obligation:

- **Boolean equality:** `booleanMember` checks that the supplied destination
  contains the observed Boolean. `subset` is the canonical evidence marker for
  this check, not an ordinary subset derivation. No synthetic singleton label
  is needed.
- **Tag outcome:** `tagSlice` discards a label only if every clause contradicts
  the observation, then checks an ordinary subtype certificate from the remaining
  labels to the supplied destination. Mixed-shape labels are retained intact.
  Filtering is a conservative algorithm, not the definition of `ObservedSub`.
  A more precise algorithm can implement the same contract without changing the
  edge or environment rule.

For the current primitive profile, null filtering gives:

$$
F_{\mathrm{null},\mathrm{true}}(\mathrm{null}\lor\mathrm{bool})=\mathrm{null},
\qquad
F_{\mathrm{null},\mathrm{false}}(\mathrm{null}\lor\mathrm{bool})=\mathrm{bool}.
$$

A regression also proves a semantic refinement of a mixed label that the current
filtering checker cannot establish. This records the precision boundary explicitly.
A Boolean shape test does not establish equality to `true`; these observations
have separate tests to prevent conflation.

The existing `branchBind` dispatch now uses this common checker and environment
theorem with a Boolean observation of the actual pushed value. Its all-budget
safety and deterministic execution proofs still apply, including cyclic graphs.
The source compiler maps a tested immutable Boolean variable to that pushed
value and preserves the other slot identities. Negations swap branch polarity.

The `tagBind` continuation tests the actual returned value, pushes that value,
and selects the matching edge. Its schematic rule is:

$$
\frac{\Gamma\vdash_G t:A
\quad\operatorname{ObservedCovers}_G(A::\Gamma,\Delta_y,0,\operatorname{tag}(k,\mathsf{true}),m_y)
\quad\operatorname{ObservedCovers}_G(A::\Gamma,\Delta_n,0,\operatorname{tag}(k,\mathsf{false}),m_n)}
{\operatorname{NodeOk}_G(\Gamma,t,\operatorname{tagBind}(k;y,m_y;n,m_n))}.
$$

Both edges are checked. Unlike Boolean dispatch, tag dispatch accepts any typed
value. Safety and deterministic execution use the actual `tagHolds` outcome;
the certificate cannot supply it. `tagBind` shares the observed-edge checker
and environment theorem with `branchBind`.

Source branches and loop heads use null or undefined tag dispatch only for syntactically
identified immutable variables, including repeated negations and either literal
operand order. The original condition runs once and its operand/result claims
remain obligations. A subsequent lookup of that immutable variable supplies the
value for tag dispatch; no source call or property read is repeated. Maps retain
the observed value in the target binding and discard saved condition temporaries.
Closure null guards use existing `unionVar` and `ifTag` evidence instead of a new
rule. The condition is evaluated into an anonymous slot. The immutable tested
slot is split into its primitive labels; each label has a known tag answer and
checks the selected arm. Source arm-entry and expression claims remain separate
obligations in the corresponding filtered contexts. The final ordinary term
certificate checks the complete construction. This supports parameters, captured
immutable values, negations and effects in the selected arm within the existing
closure control-flow slice. It does not retain observations of mutable properties.
The finite-label split is a source-profile strategy, not a new semantic rule for
arbitrary mixed-shape type labels.

## State

What is known about the heap and the environment as execution proceeds, layered
over both of the above: expression typing decides whether an operation is
admitted, the graph decides where its knowledge travels, and these rules decide
what it establishes.

### Current-content rules (semantic layer)

The finite [type and assertion syntax](POSITIVE-TYPES.md#state-assertion-grammar)
is defined alongside the ordinary type grammar. This section owns its rules.

These rules are proved in [HeapObservations.lean](lean/Verification/ExperimentState/HeapObservations.lean)
and [HeapFacts.lean](lean/Verification/ExperimentState/HeapFacts.lean).
[HeapExpressionRules.lean](lean/Verification/ExperimentState/HeapExpressionRules.lean)
checks finite expression evidence against them. They are not additional `HasTy`
constructors. The maintained graph checker now accepts the checked effect forms;
the source adapter binds supplied observations to checked graph checkpoints.
The producer can also derive facts through supported operations.
The [semantic reference](SEMANTICS.md#current-content-assertions-and-postconditions)
defines `Obs`, `ObservedRef`, and `SafePost`; ordinary immutable-value branch
observations above must not be confused with these mutable-heap assertions.

All rules below assume an admissible world and satisfying initial heap. Write
$\widehat R(n,W,v)=R(v)$ for a heap-independent content predicate, and require
$R(v)$ to imply that $v$ is a value. The observed-read rule is:

$$
\frac{\operatorname{Obs}(h,\ell,R)}
 {\operatorname{SafePost}(\widehat R,Q,n,W,h,\mathsf{read}(\ell))},
\qquad Q(h',v)\equiv h'=h\land h'(\ell)=v.
$$

`read_contents` proves this: its result type gives $R(v)$, and its postcondition
preserves the entire heap, hence other observations. For a value $v$ permitted by
the invariant $B$, the write rule is:

$$
\frac{\operatorname{Ref}(B)(n,W,\ell)\quad B(n,W,v)\quad\operatorname{isVal}(v)}
 {\operatorname{SafePost}(\mathsf{Null},Q,n,W,h,\mathsf{write}(\ell,v))},
\qquad Q(h',u)\equiv h'=h[\ell:=v]\land u=\mathsf{null}.
$$

`write_observed` requires `Adm B`. It needs no old-content premise. `write_new`
establishes the new observation; `write_frame` preserves a fact at another
location only with proved runtime inequality. A write through an alias has the
same effect. Allocation uses `alloc_observed` to return an invariant reference
and the exact appended heap; `alloc_new` and `alloc_frame` give the fresh fact and
preservation of existing facts.

| Rule | Premise and consequence |
| --- | --- |
| `test_refines` | A current lookup links the tested value to the cell; a predicate on that value then refines current contents. An old snapshot alone does not suffice. |
| `call_forget` | Ordinary arrow membership supplies result safety and heap-invariant preservation, with postcondition `True`. It supplies no retained observation. |
| `bind` | For an evaluation context that lifts steps, its continuation receives the actual resulting heap, value membership and postcondition in the future world at the remaining budget. |
| `consequence` | Implication weakens the result family and postcondition. |
| `write_then_read` | Composing write, bind, beta and read proves that the immediate subsequent read returns the written value; there is no ownership or non-escape premise. |

The finite assertion layer represents a fact as a slot $i$ and a set $R$ of
null/undefined/Boolean literals. Its meaning is:

$$
\operatorname{Holds}(\Delta,\rho,h)
\equiv \forall(i,R)\in\Delta.\;
\exists\ell,v.\ \rho(i)=\ell\land h(\ell)=v\land v\in R.
$$

For a slot map $m$, the executable entailment check uses this sufficient rule:

$$
\frac{\forall(i,R)\in\Sigma'.\;\exists(j,S)\in\Sigma.\ j=m(i)\land S\subseteq R}
 {\operatorname{Holds}(\Sigma,\rho,h)\Longrightarrow
  \operatorname{Holds}(\Sigma',\operatorname{mapEnv}(m,\rho),h)}.
$$

`HeapFacts.check_sound` proves it. Repeated slot mappings retain aliases; different
slots do not prove disjoint locations. `shift_holds` transports facts when a bind
pushes a result. The finite `read` rule preserves facts. `write` conservatively
drops all old facts and establishes the written literal. `alloc` preserves shifted
old facts and adds the fresh cell at the result slot. These are semantic rules;
source compilation must still supply and check their graph-level use.

#### Checked expression postconditions

`HeapKnowledge.Knowledge` pairs the cell facts above with immutable slot facts
$V$, interpreted as $\forall(i,R)\in V.\;\rho(i)\in R$. This distinction is
necessary when the producer claims a wide type for a read: the ordinary type
remains unchanged, while a proved fact about the returned value can justify a
narrower subsequent return contract. Mutation invalidates cell contents and read-to-cell relationships, not
values already read into immutable slots or equalities between copied values.

The [assertion layer](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch)
splits in two. $\Pi$ is a conjunction of **equalities** — $x\in\{c_1,\dots,c_k\}$
between a variable and constants, and $x=y$ between two variables — and mentions
only the environment. $\Sigma$ is a list of points-to atoms $x\mapsto R$ and
$x\mapsto y$ — the cell $x$ names currently holds one of those constants, or the
value of $y$ — and so mentions the heap. Neither relation carries ownership:
$\mapsto$ here is duplicable and says nothing about what else the heap holds.

Checking an expression is then a **Hoare typing**: an ordinary typing carrying a
precondition and a postcondition. Write

$$\Gamma;\Pi;\Sigma\vdash_G r\leftarrow t:A\dashv \Pi';\Sigma'$$

for: with variables typed by $\Gamma$, in an environment satisfying $\Pi$ and a
heap satisfying $\Sigma$, evaluating $t$ is safe, its value has type $A$, and
binding that value to $r$ leaves a state satisfying $\Pi'$ and $\Sigma'$.

The binder is written $\leftarrow$ rather than $=$, which is already the equality
assertion these rules produce, and rather than $:=$, since nothing is assigned:
$r$ is a fresh binding, and it is the graph's `bind` continuation that makes it.
$r$ is in scope in the postcondition only, so a premise can never mention it.

$\Gamma$ does not appear on the right. It types the variables and is fixed for
the derivation; only $\Pi$ and $\Sigma$ are transformed. Note that $\Gamma$ and $\Pi$ both
constrain the environment, in different languages: $\Gamma$ gives each variable a
graph type, and $\Pi$'s constant equalities refine that for primitives — `valuesAt`
reads a value fact when there is one and falls back to the variable's type when
there is not. What $\Pi$ adds beyond $\Gamma$ is equalities *between* variables,
which a type cannot express.

Every rule binds the value it produces. Write $r$ for that binding, so a
postcondition can speak about the result alongside everything already in scope.

Rules below name their bindings, and one paragraph justifies that. Environments
are positional, and the implementation pushes the result at position $0$, moving
every existing binding up by one; `HeapKnowledge.shift` performs that
renumbering and `shift_holds` proves it preserves meaning. Naming the bindings is
that theorem applied: the precondition may appear unchanged in a postcondition
because nothing about the old bindings changed except their numbers. A name here
is a display for a position, not syntax — the calculus has no identifiers — and
it carries no source scoping; the adapter's own shadowing rules are
[a separate matter](REQUEST-PROTOCOL.md#source-mode). Positions reappear exactly
where a certificate carries a permutation, in
[binding transfer](#supplied-point-claims-and-incoming-edges) and on the wire.

Two auxiliary forms. $(\Gamma;\Pi)(x)$ looks $x$ up in both contexts, $\Pi$
first: it is the finite disjunction of constants recorded for $x$ there, or
failing that the one $\Gamma(x)$ denotes when that type is a finite primitive
union. It extends the $\Gamma(x)$ of the ordinary rules to the pair, is partial
in the same way, and is a lookup rather than a search — `valuesAt` computes it in
that order and `valuesAt_sound` proves the equality it yields.

$y\approx_\Pi x$ says $\Pi$ contains the equality $x=y$, or $y$ is $x$ itself. It
is deliberately not written as an entailment, because it is **one step and not
the transitive closure**: with $x=y$ and $y=z$ in $\Pi$, the relation holds of
$y$ and not of $z$ (`HeapLinks.aliases`). A write therefore propagates to the
directly recorded aliases only. That is sound — `aliases_eq` proves each one
denotes the same value — and incomplete, and the rules below say $\approx_\Pi$
rather than $=$ so as not to claim otherwise.

#### The reference operations

These four rules are the heart of the state discipline. Each is proved in
`HeapExpressionRules.lean`, and each is the postcondition the checker computes,
not one it assumes.

Each has an ordinary typing above the line and a Hoare typing below it, which is
the layering: $\Gamma\vdash_G t:A$ is the
[judgment of the ordinary rules](#judgments-and-constructor-views), `HasTy`, and
it knows nothing about state; the conclusion adds what evaluating $t$ does to
$\Pi$ and $\Sigma$. So an operation is admitted only if it already types, and
these rules say what it then establishes. $\operatorname{Ref}A$ and
$\mathsf{Null}$ are [constructor views](#judgments-and-constructor-views): a type
whose labels expand to exactly that clause.

Here $x$ and $y$ range over variables, where the ordinary rules write $a$ for an
arbitrary term. A variable is a term, so each premise is an ordinary rule at a
special case and no kind is mismatched. The reason for the restriction is that
$\Pi$ and $\Sigma$ speak only about variables: $x=R$, $x\mapsto y$ and
$z\approx_\Pi x$ all name one. With an arbitrary operand the expression still
types and the operation still runs, but the postcondition would have nothing to
name, and the rule would degenerate into the catch-all below. Naming the operand
buys precision, not soundness.

$r$ is reserved throughout for the result of the operation being typed, and
never names one of its operands.

**Allocation** puts $x$'s value in a fresh cell and returns it, so the result is
a reference whose contents are whatever $x$ was known to equal. Nothing already
known is disturbed: a cell that did not exist cannot be one an existing atom
names, so all of $\Sigma$ survives.

$$
\frac{\Gamma\vdash_G\operatorname{alloc}(x):\operatorname{Ref}A
      \qquad(\Gamma;\Pi)(x)=R}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\operatorname{alloc}(x):\operatorname{Ref}A
  \dashv \Pi\;;\;\Sigma,\;r\mapsto R}
$$

**Reading** has two rules for the same term, and neither subsumes the other.

The first applies whenever the read types and $x$'s type is a plain reference. It
claims nothing about the contents; what it records is where the result came from,
$r$ now holding what the cell $x$ names holds — which is what a later test of $r$
needs in order to refine $x$ itself.

The second applies when $\Sigma$ already holds an atom for $x$ and the result type
is primitive. It consumes that atom and returns it as an equality on the result.
It needs no typing derivation: the atom and its premise establish the result type
between them, which is why its first premise is a membership in $\Sigma$ rather
than a judgment. Writing $\operatorname{lits}(A)$ for the constants a type
denotes — defined only when $A$ is primitive, so the premise also fails for a
reference or an arrow result:

$$
\frac{\Gamma\vdash_G\operatorname{read}(x):A\qquad\Gamma(x)=\operatorname{Ref}B}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\operatorname{read}(x):A
  \dashv \Pi\;;\;\Sigma,\{y\mapsto r\mid y\approx_\Pi x\}}
$$

$$
\frac{(x\mapsto R)\in\Sigma\qquad R\subseteq\operatorname{lits}(A)}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\operatorname{read}(x):A
  \dashv \Pi,\;r=R\;;\;
   \Sigma,\{y\mapsto r\mid y\approx_\Pi x\}}
$$

Two fixtures show the difference. In
[`write-refined-read.ts`](tests/skjs-incomplete/write-refined-read.ts),

```ts
const cell: { value: boolean } = { value: false };
cell.value = true;
return cell.value;
```

the allocation leaves $\Sigma$ holding $\mathit{cell}\mapsto\{\mathsf{false}\}$
and the write replaces it with $\mathit{cell}\mapsto\{\mathsf{true}\}$. At the
read that atom is present and the result type is `boolean`, whose constants
include $\mathsf{true}$, so the second rule applies and returns
$r=\mathsf{true}$ — a fact the wider claimed type does not carry, and enough for
a return contract demanding exactly $\mathsf{true}$.

In [`captured-refinement.ts`](tests/skjs-unsound/captured-refinement.ts) the same
read follows a call:

```ts
const done: null = reset(false);
return cell.value;
```

The call empties $\Sigma$, so no atom for `cell` remains and only the first rule
applies: the read is well typed and records where its value came from, but
establishes nothing about the contents. Nothing about what `cell` holds is
provable at that point, whatever the claimed type says.

Each covers cases the other does not. Reading a $\operatorname{Ref}(\operatorname{Ref}B)$
has no primitive result, so only the first applies; a variable whose type is a
union of references does not meet the first rule's plain-reference premise, so
where an atom exists only the second does. Where both apply the second yields
strictly more, the evidence records which was used, and soundness does not depend
on the choice — only precision does.

**Writing** stores $y$'s value in the cell $x$ names. The result is `null`. It
establishes the new contents for $x$ and every variable recorded equal to it, and
destroys the rest of $\Sigma$ — including atoms about cells that may or may not
be this one:

$$
\frac{\Gamma\vdash_G\operatorname{write}(x,y):\mathsf{Null}
      \qquad(\Gamma;\Pi)(y)=R}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\operatorname{write}(x,y):\mathsf{Null}
  \dashv \Pi,\;r=\mathsf{null}\;;\;
   \{z\mapsto R\mid z\approx_\Pi x\}}
$$

**Every other expression**, calls included, empties the heap part and leaves the
equalities untouched:

$$
\frac{\Gamma\vdash_G t:A}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow t:A\dashv \Pi\;;\;\emptyset}
$$

$\Pi$ and $\Sigma$ are finite lists of atoms, read as their conjunction and
extended with a comma, exactly as $\Gamma$ is. $\emptyset$ is the empty heap
part: nothing is known about any cell. $\Pi$ carries over verbatim, because no
equality mentions the heap. There is no separating conjunction here — these
facts are duplicable, and carry no ownership or disjointness.

The shape a type theorist will look for is missing on purpose: **there is no
frame rule.** A write through $x$ discards what is known about $z$ even when $z$
is a different name, because distinct names need not be distinct locations — the
assertion language can witness that two names are equal, never that they are
not. So
the positive direction is proof-driven and the negative direction is total: the
new contents propagate exactly to the witnessed aliases $z\approx_\Pi x$, while
everything else is dropped rather than framed around. `write_frame` in the
semantic layer does preserve a fact at another location, but only from a proved
runtime inequality, and $\Pi$ cannot state one: it carries equalities and no
disequalities. Preservation for proved-distinct cells is
therefore not implemented. That is a gap in the assertion language, not a limit
of the model.

The practical shape of the gap is worth stating. Facts about several cells
coexist freely: allocation and reads preserve every one of them, so a program
that allocates three cells knows the contents of all three. The first write
collapses that set to the written cell and its aliases, and a call empties it.
So a program that mutates carries current-content knowledge for essentially one
cell at a time, the one written most recently. $\Pi$ is not subject to this at
all, which is why a value read out of a cell before a callback
remains usable after the callback has overwritten that cell.

Two consequences worth naming. Immutable value facts and slot equalities survive
every operation, because no write or call can falsify $\rho(i)\in R$ or
$\rho(i)=\rho(j)$ — those are statements about the environment, not the heap.
And a read link is what later lets an observation of the result refine the cell
it came from: that is how a guard on `cell.value` refines `cell` itself, and why
a call, which drops read links, ends such a refinement.

The implementation keeps $\Pi$ and $\Sigma$ in one `HeapKnowledge.Knowledge`;
write $K$ for that pair and $K(\rho,h)$ for the conjunction of everything in it.
A successful `checkStep` is a derivation of this judgment, and `checkStep_sound`
is its soundness:

$$
\frac{\operatorname{checkStep}(G,(\Gamma,t,A),K,e)=\operatorname{some}(K')
\quad\operatorname{EnvOk}_G(\Gamma,\rho,n,W)\quad K(\rho,h)}
{\operatorname{SafePost}(\llbracket A\rrbracket,
  \lambda(h',v).\,K'(v::\rho,h'),n,W,h,\operatorname{close}_{\rho}(t))}.
$$

As above, the initial world must be admissible and the heap must satisfy it.
The checker binds evidence to the requested expression and type and checks scope.
It computes a guaranteed output, not an assumed postcondition:

| Evidence | Guaranteed output in the result-pushed frame |
| --- | --- |
| Pure value or variable copy | Preserve facts and links; copies establish slot equality and duplicate existing facts. Literals establish their exact result even when their supplied type is wider. Lambda bodies require ordinary typing, without captured heap facts. |
| Pure test or conditional | Preserve existing facts and links, shifted past the result slot. Every evaluated subexpression must be syntactically pure; no new result-to-cell link is invented. |
| Ordinary typed read | Preserve facts and record read links to the receiver and witnessed aliases; no prior current-content fact is needed. Its result has the supplied type. |
| Observed read | Preserve facts and links; record the result's literal set and its current read relationship. That set must fit the requested ordinary result type. |
| Known immutable value | Check the requested primitive type against a proved slot fact or the slot's ordinary primitive type. |
| Allocation | Check ordinary allocation evidence, preserve old facts, and add the fresh cell's initial contents. |
| Write | Check ordinary write evidence (no old-content premise), discard all old cell facts, record new contents for the receiver and its witnessed aliases, and preserve immutable facts and slot equalities. Read links are discarded. |
| Ordinary expression, including calls | Check ordinary evidence, discard cell facts and read links, preserving immutable facts and slot equalities. |

`typedRead_sound`, `read_sound`, `alloc_sound` and `write_sound` prove the four
rules above. None of them takes a premise about a cell's old contents, and the
checker's write evidence carries none either. These are operation rules within a
local segment: at the next statement entry, only the supplied interface
survives.

`pureTerm` includes values, variables, tests of pure terms, and conditionals
whose condition and both arms are pure. It excludes calls, reads, writes and
allocation. A lambda's body may have effects because forming the lambda does
not run it. `pure_step` and `pure_frame` prove:

$$
\frac{\operatorname{Pure}(t)\quad(h,t)\longrightarrow(h',t')}
 {h'=h\quad\land\quad\operatorname{Pure}(t')},
\qquad
\frac{\operatorname{Pure}(t)\quad\operatorname{Safe}(A,n,W,h,t)\quad\forall v.\,Q(h,v)}
 {\operatorname{SafePost}(A,Q,n,W,h,t)}.
$$

This extends the existing pure-effect evidence; it does not add another typing
rule or certificate constructor. It retains heap observations through null
predicates without treating an effectful operand as pure. A negated graph guard
checks its full expression claim separately and swaps the operand's successors;
it does not invent an equality between a Boolean and its negation.

Primitive result sets are finite
null/undefined/Boolean literal lists. `HeapKnowledge.check_sound` and `project_checked`
justify transfer and alias-preserving projection along executable slot maps.

[HeapExpressionTests.lean](lean/Verification/ExperimentState/HeapExpressionTests.lean)
uses the actual source type graph to check allocation, write, mapped transfer,
wide read and precise return, with negative tests for stale contents, invalid
storage writes, fabricated facts and changed expressions. The maintained graph checker carries the same postconditions in its state
invariant and checks every incoming edge, including back edges. External entry
requires empty knowledge; effect-only continuations drop result-slot facts.
[HeapGraphTests.lean](lean/Verification/ExperimentState/HeapGraphTests.lean) proves
a complete graph safe, checks its JSON evidence, and rejects fabricated entry
facts, stale write postconditions and altered maps. Source observations use the
same checked graph facts, through the checkpoints below.

Boolean guards use the following rule, proved by `observeBoolean_holds`:

$$
\frac{x\mapsto y\quad y=b}
 {x\mapsto\{b\}},\qquad b\in\{\mathsf{true},\mathsf{false}\}.
$$

The points-to atom must hold in the current heap. Note that
$\operatorname{read}(x)$ is the language's read expression; the assertion that
used to share its name is now $x\mapsto y$. `HeapGuardTests.lean` proves a
complete two-branch graph safe and checks that discarding the link prevents this
refinement. A slot equality $x=y$ permits a checked write through either alias to
establish the new contents for both, as the
[write rule](#the-reference-operations) above states; every other cell
observation is discarded. Read links are invalidated by writes and calls, while
slot equalities survive. Together these let source lowering discard a receiver
temporary without losing a write to its original cell.

[WriteRefinedRead.lean](lean/Verification/ExperimentState/WriteRefinedRead.lean)
assembles allocation, postcondition-aware composition and `write_then_read` to
prove an allocate-false/write-true/read body safe at true in every admissible
initial heap. A separate five-step execution establishes its returned value.
Its null-argument wrapper inhabits `null → true`; the source fixture itself has
no parameters. [The fixture notes](tests/skjs-incomplete/README.md) distinguish
this model proof from source verification, which needs an explicit current-true
claim at the return entry. The original broad entry claim is insufficient.

#### Source observation checkpoints

`SourceClaims.Function` retains ordinary types and separately indexed current
predicates. Both adapters populate this interface. **Every source statement entry
is a full local interface**, including entries with no current predicates. The
compiler reconstructs its ordinary context $\Gamma_l$ and knowledge
$K_l=(\Delta_l,\varnothing,\varnothing)$, where $\Delta_l$ contains exactly the
supplied current predicates. No immutable-value facts or alias/read links are
implicitly carried across this boundary. Ordinary reference contracts remain in
$\Gamma_l$; the calculus always assumes environment and heap well-formedness.

For certificate input $K_c$, source acceptance requires:

$$
K_c=K_l.
$$

`SourceExtraction.checkAssertions_cut` proves this equality from acceptance.
Each incoming edge separately establishes the supplied heap interface (ordinary
context coverage is checked alongside it):

$$
\frac{\operatorname{checkKnowledge}(K_{\mathrm{out}},K_l,m)=\mathsf{true}
\qquad K_{\mathrm{out}}(\rho,h)}{K_l(\operatorname{mapEnv}(m,\rho),h)}.
$$

The next statement is checked from $(\Gamma_l,K_l)$, independently of any
stronger facts proved by predecessors. Loop heads use the same interface on both
initial and back edges. Empty knowledge means forget all extra facts; an empty
*content predicate* remains an impossible observation, not an absent one.

**Expression claims are local obligations within a statement, not full-state
interfaces.** Their supplied result type must be justified at the expression;
a supplied current predicate is checked at a no-op result checkpoint, naming
slot zero before projection. Within the statement, the checked effect rules may
retain its entry assumptions and derive postconditions. Calls and writes forget
facts according to those rules. Administrative copies do not discard facts.
Thus a Boolean read claim is compatible with locally proving a true result from
an explicit entry observation; it does not license recovering an observation
forgotten at an earlier statement boundary.

At an expression checkpoint, required knowledge is checked by entailment,
$\operatorname{checkKnowledge}(K_c,K_r,\mathrm{id})=\mathsf{true}$.
`checkAssertions_sound` proves the implication. The independent source consumer
reconstructs both kinds of boundary and checks them alongside graph acceptance
and supplemental expression proofs; these are not producer-selected policies.

Ordinary compositional expression proofs, including lambda bodies, do not carry
heap contexts. For a point assertion $\operatorname{ObservedRef}(B,R)$ there,
the adapter conservatively requires the ordinary sequent:

$$
x:B\ \vdash\ x:R.
$$

Here $x$ is an arbitrary **stored value**, not the reference. This checks that
the invariant implies the observation uniformly. Its proof is a supplemental
`heap-observation` obligation at the source site. It never assumes the heap at
closure creation remains unchanged. Consequently a narrower temporary observation
inside a closure may remain unproved even when it is valid locally; exploiting
such facts requires graph-backed closure bodies. The checkpoint integration does
not claim that extra precision.

`tests/source-heap-claims.mts` exercises both source formats, wrong and empty
observations, write invalidation, Boolean read guards, both incoming merge edges,
loop backedges, and evidence reuse after changing assertions.

## Search and source forms

How evidence is produced for supplied claims, and how source constructs outside
the core reduce to the rules above.

### Producing evidence from supplied claims

The producer selects checked effects and propagates their postconditions along
single-predecessor administrative paths within a statement. A source entry is
seeded with exactly its supplied knowledge, without waiting for its predecessors;
every incoming edge must subsequently justify it. External entry starts empty.
There is no iteration to infer a loop invariant. The independent source consumer
enforces the reset, so supplying a graph-safe certificate with extra facts at a
statement entry still fails source verification.

`CertificateProducer.lean` accepts an actual graph, its declared result type and
start label, and one `PointClaim` per node. Each claim fixes both the entry
context and the expression result type. These are annotations in this Lean
interface, not SKJS wire types. The source adapter supplies them for the supported
slice; new source forms require the corresponding extraction obligations.

`produce` builds expression derivation trees and per-slot subtype evidence for
every actual edge. It does not infer or repair point invariants. Its inputs also
include an enumeration of type labels, a search-depth limit, and optional
intermediate type hints. The vocabulary includes singleton labels, their
reference/arrow operands, bottom, and the supplied context/result types. Omitting
labels or useful intermediate types can prevent success, but cannot make an
incorrect certificate pass.

Expression search covers the current ordinary rules: variables, constants,
overloaded lambdas, application, lets, allocation, reads, writes, known shape
answers and subsumption. Subtype search first tries union inclusion, then builds
a finite candidate cyclic relation and removes unsupported rows. It generates
arrow evidence for source selection, splitting union domains, and pairwise
compatible codomain combination. The existing subtype checker validates the
resulting table and all arrow evidence. This search is deliberately incomplete:
it does not enumerate arbitrary intermediate types, transitivity derivations,
or arbitrary nested arrow-combination proofs.

The final `accept` check binds the evidence to **all the requested point claims**
as well as calling `checkEntry` on the actual program and external input context. Thus a valid certificate
for different annotations is rejected. Lean proves:

$$
\begin{gathered}
\operatorname{produce}(G,I,f,R,P,Q,\ell,H,\Gamma_0)=\operatorname{ok}(C)
\\
\Longrightarrow\quad
\operatorname{accept}(G,R,P,Q,C,p,\Gamma_0)=\mathsf{true},
\\
\operatorname{accept}(G,R,P,Q,C,p,\Gamma_0)=\mathsf{true}
\\
\Longrightarrow\quad
\operatorname{claims}(C)=Q
\;\land\;
\operatorname{checkEntry}(G,R,P,C,p,\Gamma_0)=\mathsf{true}.
\end{gathered}
$$

Here $I$ enumerates labels, $f$ bounds expression search depth, $Q$ contains the
supplied point annotations, $\Sigma$ contains optional type hints, and $\Gamma_0$ is
the independent input contract. Search fuel is
not an execution budget and never occurs in the typing rules or certificates.
`produce_checked` proves the first implication; `accept_claims` proves claim
fidelity, and `accepted_from_inputs` obtains safety for arbitrary typed arguments
from the consumer alone. `accepted_safe` is its closed-entry counterpart.
The producer can be replaced without changing the soundness argument.

Failure reports a claim-count mismatch, an expression label, an edge's source
and destination, or final consumer rejection. Failure means unsupported or
unjustified within this search, not a proof that the program is untypable.
No evidence is returned as successful unless the consumer accepts it.

`CertificateProducerTests.lean` runs the full path without hand-built evidence:

- The stateful loop and shared union merge from `ControlFlowTests.lean`.
- A graph that duplicates a reference slot, inserts a local, reorders bindings,
  drops the interior local, writes through an alias, and calls the captured
  closure. A checked 16-step execution returns `false`; its safety follows from
  the automatically produced certificate.
- A diamond whose two branch edges use different slot maps.
- The nested-let overloaded program, union-domain arrow subsumption, and a
  generated cyclic subtype certificate for recursive references.
- Rejections for corrupted claims, invalid or wrong-length maps, changed code,
  missing or extra edge evidence, invalid starts and exhausted search fuel.

This establishes an in-memory program-plus-annotations-to-checked-evidence path.
The [serialized request protocol](REQUEST-PROTOCOL.md) now exposes this boundary
through the existing verifier binary. Source extraction correctness, producer
completeness and integration of extended source claims remain outside these
results.

### Derived source forms

`BooleanConditionalTests.lean` checks the ordinary conditional through serialized
requests and direct recipes. Its execution traces cover both outcomes after an
alias write and a condition that writes then reads a cell. Invalid condition
types, invalid arms, omitted premises and exchanged arms are rejected. This is
calculus coverage. Source closure blocks now support terminal branches with both
arms returning, including nested branches and checked entry refinements.
Source ternaries reuse these rules and the existing primitive-tag union elimination.
Their own expression claim supplies the result type; both arm claims are checked
under the corresponding refined context. This introduces no additional rule or
trusted proof-search step.
Null coalescing is likewise a derived form: a let saves the left value, and
`unionVar` with known nullish-tag conditionals selects the fallback or saved value.
No truthiness rule is involved; false remains a result of the left operand.
For Boolean left operands, logical AND and OR use the derived forms:

$$
a\mathbin{\&\&}b\;\equiv\;\mathsf{if}\ a\ \mathsf{then}\ b\ \mathsf{else}\ \mathsf{false},
\qquad
a\mathbin{\Vert}b\;\equiv\;\mathsf{if}\ a\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ b.
$$

They share the source conditional proof builder, including null refinement within
the right operand;
the synthetic constant arm requires a literal proof, not a source claim.
At statement guards the source compiler instead emits short-circuit graph paths,
whose Boolean/null observations justify the intermediate and successor contexts.
It also checks the complete expression claim using the derived expression form.
Thus graph decomposition cannot silently discard the producer's condition type.


Closure branches whose two arms fall through require no additional typing rule.
Their extracted shape is:

$$
\mathsf{let}\ z = (\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e)
\ \mathsf{in}\ k.
$$

Both $t$ and $e$ finish with an administrative null after their effects.
The existing conditional rules check them at $\mathsf{Null}$, and the let rule
checks $k$ under $\mathsf{Null}::\Gamma$. The new slot is anonymous; source names
refer to their original outer bindings. The source statement at $k$ supplies
an environment whose types must be justified from this context. Arm-local
bindings and singleton refinements cannot become assumptions at the join.
The continuation occurs once, so nested branching does not duplicate its term.
`shared_continuation_trace` ties the extracted graph to a 44-step execution in
which the selected arm writes true before the shared read returns true.

An early-return branch with one fully returning arm and one return-free arm
uses the same conditional rules. For example, `if (c) { return r; } else { s; } k`
has the extracted shape

$$
\mathsf{if}\ c\ \mathsf{then}\ r\ \mathsf{else}\quad
(\mathsf{let}\ z=s\ \mathsf{in}\ k).
$$

Here $s$ completes with administrative null, and its local bindings stay inside
$s$. Both $r$ and the surviving sequence check at the supplied function result
type. When $c$ tests an immutable Boolean variable, the surviving sequence uses
the justified false refinement; it does not have to discard this fact as a
shared join would. `early_return_trace` checks both outcomes of an extracted
closure: an early return skips the later write, while the other arm executes it.
General partially returning nested arms remain gated.


A local continuation shared by multiple paths is a derived construction:

$$
\frac{\Gamma,u:N\vdash_G k:R\qquad
      \Gamma,j:(N\to R)\vdash_G b:R}
     {\Gamma\vdash_G
       \mathsf{let}\ j=(\lambda u.k)\ \mathsf{in}\ b:R}.
$$

`ContinuationSharing.share_typed` proves this from lambda introduction and let.
The body $k$ occurs once; $b$ can call $j$ from multiple branches. There is no
new primitive jump, recursive binding or certificate rule. The binder notation
above is named; the Lean terms use slot zero for each newly introduced binder.
For a null argument the continuation uses captured immutable bindings and
stable reference contracts, and reads the current heap at each call. It does
not inherit a calling path's later refinements of captured bindings.
The checked example has two paths calling the same reader continuation and
one early-return path bypassing it. This is a calculus construction; source
lowering of general partially returning nested arms remains gated.


Later refinements can instead be passed as explicit continuation arguments:

$$
\frac{\Delta\vdash_G j:A\to R\qquad\Delta\vdash_G v:A}
     {\Delta\vdash_G j(v):R}.
$$

This is ordinary application. The continuation body is checked once under its
parameter contract $A$; each call must establish that contract in its own context
$\Delta$. `passed_refinement_paths` checks two surviving paths into one
`false → boolean` continuation, with explicit failures for an unrefined argument
or the wrong slot. Passing this one refined value is established; translating
arbitrary supplied entry environments into continuation parameters is not yet
implemented.
