# Program typing over positive recursive types

[ProgramTyping.lean](lean/Verification/ExperimentState/ProgramTyping.lean) gives
syntactic program-typing rules for the stateful language. Its fundamental theorem
connects those rules to the model in [SEMANTICS.md](SEMANTICS.md). Subsumption uses
the certificate checker specified in [POSITIVE-TYPES.md](POSITIVE-TYPES.md).
This development is independent of the production F0 verifier.

## Judgments and constructor views

Fix a normalized positive graph $G$. A type $A$ is a finite list of graph labels,
interpreted as their union. Write $A\equiv_G c$ when expanding those labels yields
exactly the singleton clause $[c]$. This is a finite syntactic equality, not a
semantic-equivalence oracle. Below, writing a constructor as a type abbreviates
such a view of its graph labels.

The judgment $\Gamma\vdash_G e:A$ is `HasTy`. The rules are:

$$
\frac{\Gamma(x)=A}{\Gamma\vdash_G x:A}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{null}:\mathsf{Null}}
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
\frac{\forall(A,B)\in L.\;\Gamma,x:A\vdash_G e:B}
     {\Gamma\vdash_G \lambda x.e:\bigwedge_{(A,B)\in L}(A\to B)}
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
\frac{\Gamma\vdash_G r:\mathsf{Ref}(A)}{\Gamma\vdash_G\mathsf{read}(r):A}
$$

$$
\frac{\Gamma\vdash_G r:\mathsf{Ref}(A)\quad\Gamma\vdash_G a:A}
     {\Gamma\vdash_G\mathsf{write}(r,a):\mathsf{Null}}
\qquad
\frac{\Gamma\vdash_G e:A\quad\operatorname{check}(G,A,B,p)=\mathsf{true}}
     {\Gamma\vdash_G e:B}
$$

For branching, $\operatorname{Answers}_G(A,k,q)$ checks that every expanded
clause of $A$ gives the same Boolean answer $q$ to shape test $k$:

$$
\frac{\Gamma(x)=A\quad\operatorname{Answers}_G(A,k,q)
      \quad(q=\mathsf{true}\Rightarrow\Gamma\vdash_G u:B)
      \quad(q=\mathsf{false}\Rightarrow\Gamma\vdash_G e:B)}
     {\Gamma\vdash_G\mathsf{if}\ k(x)\ \mathsf{then}\ u\ \mathsf{else}\ e:B}.
$$

The shape-test rule checks each overload body under its own argument type. It
handles shape dispatch between overloads.

Ordinary Boolean conditionals use a separate rule. Define
$\operatorname{Boolean}_G(C)$ as
$\operatorname{Answers}_G(C,\mathsf{isBool},\mathsf{true})$; this accepts Boolean
singleton unions as well as the Boolean clause.

$$
\frac{\Gamma\vdash_G c:C\quad\operatorname{Boolean}_G(C)
      \quad\Gamma\vdash_G t:A\quad\Gamma\vdash_G e:A}
     {\Gamma\vdash_G\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e:A}.
$$

The condition is evaluated once. It may read or mutate the heap; its effects
precede the selected branch. Both branches must check against the supplied result
type $A$. No least-upper-bound is computed. Both use the same context: this rule
does not justify narrowed branch environments. A second rule handles a directly
tested immutable variable. Write $\Gamma[i:=T]$ for replacing slot $i$'s type:

$$
\frac{\Gamma(i)=C\quad\operatorname{Boolean}_G(C)
      \quad\Gamma[i:=\mathsf{True}]\vdash_G t:A
      \quad\Gamma[i:=\mathsf{False}]\vdash_G e:A}
     {\Gamma\vdash_G\mathsf{if}\ x_i\ \mathsf{then}\ t\ \mathsf{else}\ e:A}.
$$

Here $\mathsf{True}$ and $\mathsf{False}$ must expand to the corresponding singleton
clauses. `HasTy.ifBoolVar` proves this rule sound: the selected branch's actual
value justifies the changed slot, and all other slots retain their meanings.
It neither refines mutable heap contents nor supplies general union splitting.
Graph edges also have their own checked Boolean refinement rule.

Reference rules use a single invariant operand; eliminating a conjunction to such a reference view
can be justified by subsumption. No direct multi-contract program rule is assumed.

## Binding and soundness

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
\Gamma\vdash_G e:A\ \land\ \rho\models_{n,W}\Gamma\ \land\
\operatorname{WorldAdm}(W)\ \land\ \operatorname{HeapOk}(n,W,h)
\ \Longrightarrow\
\operatorname{Safe}(\llbracket A\rrbracket_G,n,W,h,\operatorname{close}_{\rho}(e)).
$$

`HasTy.closed_safe` specializes this to a closed program with an empty typing
environment. It explicitly requires `Scoped 0 e`: the total semantic environment
must not silently supply meanings for unbound source variables. Safety is partial
correctness and absence of stuck execution, not termination.

The general evaluation-context lemma `bind` composes computations across heap
changes and future worlds. The typing theorem is an induction on derivations;
none of its constructor rules has a semantic safety premise.

## Integration test and remaining work

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

## Executable program evidence

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

## Supplied point claims and incoming edges

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
(\rho\circ m)(i)=\rho(m_i).
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

## Checked control-flow graphs

`ControlFlow.lean` adds a finite control-flow graph over the existing expression
language. Each node contains an expression and one continuation:

| Continuation | Action after evaluating the expression |
| --- | --- |
| Return | Return its value as the graph's declared result type. |
| Bind to a target | Push the value, apply the target slot map, and enter its label. |
| Effect, then a target | Discard the value, apply the target slot map, and enter its label. |
| Boolean branch | Select a target according to the Boolean value and apply its slot map. |
| Result-binding Boolean branch | Select a target, push the tested Boolean, and apply its slot map with a singleton refinement. |

A target contains its label and an optional slot map. These are executable
program data, shared by the machine and checker; evidence cannot supply a
different binding transfer. Numeric targets abbreviate an identity map. A bind
or `branchBind` map indexes the environment **after** pushing the result; effect
and ordinary branch maps index the unchanged incoming environment.

Node evidence supplies its entry environment, expression type and program
evidence, and exactly the edge certificates required by its continuation.
`checkGraph` enumerates **every node in the actual program**. It requires one
certificate per node, binds expression evidence to that node's actual code,
checks scope, and obtains successor labels directly from the continuation.
Every target must exist in both the program and the certificate. Both branch
edges are checked even when the condition is a literal, and unreachable nodes
are checked too. Omitting a predecessor list cannot bypass these obligations.

`checkEntry` checks the graph and requires the start claim to equal a separately
supplied input context $\Gamma_0$. `accepted_inputs_safe` proves:

$$
\begin{gathered}
\operatorname{checkEntry}(G,R,P,C,\ell,\Gamma_0)=\mathsf{true}
\\
\land\;\operatorname{EnvOk}_G(\Gamma_0,\rho,n,W)
\land\;\operatorname{WorldAdm}(W)
\land\;\operatorname{HeapOk}(n,W,h)
\\
\Longrightarrow\quad
\operatorname{SafeGraph}_P(\llbracket R\rrbracket_G,n,W,h,\operatorname{at}(\ell,\rho)).
\end{gathered}
$$

The arguments, world, heap and budget are arbitrary subject to these premises.
`checkClosed` is exactly `checkEntry` with an empty input context;
`accepted_closed_safe` retains the empty-world, empty-heap corollary.
`accepted_entry_safe` is the underlying theorem for a checked point and its
claimed environment.
The proof inducts on execution budget, so it covers cycles without unrolling
the graph or computing invariants. Expressions use the existing small-step
relation and safety theorem. Node dispatch and control transfer each consume
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


### Boolean result refinement

[BranchRefinement.lean](lean/Verification/ExperimentState/BranchRefinement.lean)
justifies the `branchBind` continuation. Let $B_q$ denote the singleton family
containing the Boolean $q$. Its schematic node rule is:

$$
\frac{
  \Gamma\vdash_G e:A
  \quad \operatorname{OnlyBoolean}(G,A)
  \quad B_{\mathsf{true}}::\Gamma\Rightarrow_{m_y}\Delta_y
  \quad B_{\mathsf{false}}::\Gamma\Rightarrow_{m_n}\Delta_n
}{
  \operatorname{NodeOk}_G(\Gamma,e,\operatorname{branchBind}(y,m_y;n,m_n))
}.
$$

The edge relation checks each target slot. Selecting the pushed slot requires
that its target type contain $q$; selecting an older slot requires an ordinary
subtype derivation from that slot's incoming type. `booleanMember` checks the
first obligation directly against expanded Boolean clauses, so no synthetic
type-graph node is needed for $B_q$. Maps, bounds and target existence are checked
as usual. The wire evidence uses `subset` as the canonical marker for a slot
justified by this branch observation; in that position it invokes the singleton
membership check, not ordinary subset subtyping.

The load-bearing theorem is environment preservation under the observation:

$$
\frac{
 \operatorname{EnvOk}_G(\Gamma,\rho,n,W)
 \quad \rho(i)=q
 \quad \operatorname{RefinedCovers}_G(\Gamma,\Delta,i,q,m)
}{
 \operatorname{EnvOk}_G(\Delta,\operatorname{mapEnv}(m,\rho),n,W)
}.
$$

`state_safe` applies this after pushing the actual tested value, with $i=0$.
This retains the graph's all-budget safety and deterministic execution proofs,
including cyclic graphs. Both edges are checked. Heap contents are not refined.

For `if (x)`, the source compiler maps the target binding for `x` to the newly
pushed result of evaluating `x`: the same immutable value, now justified as true
or false. Other bindings retain their old slots. This supports direct Boolean
variable tests, including joins after the refined arms; it does not establish
refinements for related aliases, property reads, or general predicates.

## Producing evidence from supplied claims

`CertificateProducer.lean` accepts an actual graph, its declared result type and
start label, and one `PointClaim` per node. Each claim fixes both the entry
context and the expression result type. These are annotations in this Lean
interface, not a change to SKJS's exported claim format. Relating source claims
to these annotations is still extraction work.

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
\operatorname{accept}(G,R,P,Q,C,\ell,\Gamma_0)=\mathsf{true},
\\
\operatorname{accept}(G,R,P,Q,C,\ell,\Gamma_0)=\mathsf{true}
\\
\Longrightarrow\quad
\operatorname{claims}(C)=Q
\;\land\;
\operatorname{checkEntry}(G,R,P,C,\ell,\Gamma_0)=\mathsf{true}.
\end{gathered}
$$

Here $I$ enumerates labels, $f$ bounds expression search depth, $Q$ contains the
supplied point annotations, $H$ contains optional type hints, and $\Gamma_0$ is
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

`BooleanConditionalTests.lean` checks the ordinary conditional through serialized
requests and direct recipes. Its execution traces cover both outcomes after an
alias write and a condition that writes then reads a cell. Invalid condition
types, invalid arms, omitted premises and exchanged arms are rejected. This is
calculus coverage. Source closure blocks now support terminal branches with both
arms returning, including nested branches and checked entry refinements.


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
Mixed return/fall-through branches still need a broader control-flow interface.
