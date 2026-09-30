# Program typing over positive recursive types

[ProgramTyping.lean](lean/Verification/Model/Programs/ProgramTyping.lean) gives syntactic program-typing rules for the stateful language.
Its fundamental theorem
connects those rules to the model in [SEMANTICS.md](SEMANTICS.md). Subsumption uses
the certificate checker specified in [POSITIVE-TYPES.md](POSITIVE-TYPES.md).
The ordinary and graph rules below are used by the current verifier, as are the
[current-content rules](#current-content-rules-semantic-layer): supplied source
observations reach checked obligations, specified under
[source observation checkpoints](#source-observation-checkpoints). This document owns
rule statements, side conditions, soundness scope and evidence construction;
[Design](DESIGN.md) owns the decisions, the trust surface and the next steps.

## Notation

|                          | Ranges over                                                                                           |
| ------------------------ | ----------------------------------------------------------------------------------------------------- |
| $t$, $u$                 | [terms](SEMANTICS.md#operational-language)                                                            |
| $t_1$, $t_2$             | a branch's two arms, in that order                                                                    |
| $a$, $a'$                | terms, where a rule admits an arbitrary one rather than a variable                                    |
| $x$, $y$, $z$            | variables, which are terms                                                                            |
| $c$                      | a term in condition position                                                                          |
| $\gamma$                 | a [clause](POSITIVE-TYPES.md#types-and-clauses)                                                       |
| $r$                      | the binding a rule gives its result                                                                   |
| $k$                      | one of the tests in [the operational language](SEMANTICS.md#operational-language)                     |
| $A$, $B$, $C$            | types, each a finite list of graph labels read as their union                                         |
| $R$                      | a finite disjunction of primitive predicates                                                          |
| $\mathrm{pred}(A)$ | the predicate disjunction $A$ denotes, defined for supported primitives (`HeapKnowledge.atoms`)       |
| $G$                      | the normalized positive graph                                                                         |
| $\Gamma$                 | a typing context, one type per variable                                                               |
| $\Pi$, $\Sigma$          | the [equality and heap parts](#checked-expression-postconditions) of the assertion state              |
| $\rho$, $h$, $W$, $n$    | an environment, heap, world and budget, from [the model](SEMANTICS.md#computations-and-recursive-types)         |
| $\Delta$                 | a target claim environment, and in [POSITIVE-TYPES](POSITIVE-TYPES.md) a table of subtype obligations |

$r$ never names an operand, and a premise can never mention it: it is bound by
the rule's conclusion and scoped to the postcondition.

## Expressions

Typing a term against the positive graph, with no notion of state. Everything
later rests on this layer and none of it changes these rules.

### Judgments and constructor views

Fix a normalized positive graph $G$. A type $A$ is a finite list of graph labels,
interpreted as their union. Write $A\equiv_G\gamma$ when every label of $A$ is a
[clause row](POSITIVE-TYPES.md#parameter-and-scheme-rows) and expanding those
labels yields exactly the singleton clause $[\gamma]$ (`Represents`). A type
holding a parameter or scheme row has no expansion, so no constructor view of
it exists. This is a finite syntactic equality, not a
semantic-equivalence oracle. Below, writing a constructor as a type abbreviates
such a view of its graph labels.

The judgment $\Gamma\vdash_G t:A$ is `HasTyUsing G images`. Its rules are
stated once, for every proved image checker `images` (an
[`InstanceImageCheck`](RECURSIVE-EQUATIONS.md#3-metatheory)): the checker
decides whether an instance table's named images are substitution images (over
equations, or types proved equal to them), and it carries the proof

```math
\mathrm{check}(\vec b,c)=\mathsf{true}\ \land\ \mathrm{kinds}(\vec b,c)
\ \Longrightarrow\ \forall\eta.\ \mathrm{InstanceImages}_G(\eta,\vec b,c).
```

Subtype certificates in `sub` and in member coverage are checked by
`PositiveCertificates.checkUsing` with that checker, and every rule's soundness
depends on it only through this implication. Over equations the checker also
carries the renaming and the computed variances, with which `subset` and `fallback`
steps apply `Var` ([RECURSIVE-EQUATIONS §4.3](RECURSIVE-EQUATIONS.md#43-variance)),
each proved sound. The proof is Lean code, never certificate data. `HasTy G` is `HasTyUsing G (finiteInstanceImages G)`, the
finite closed-table checker; source requests use it. Constructor names below are
`HasTyUsing`'s. The rules are:

```math
\frac{\Gamma(x)=A}{\Gamma\vdash_G x:A}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{null}:\mathsf{Null}}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{undefined}:\mathsf{Undefined}}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{true},\mathsf{false}:\mathsf{Bool}}
```

Singleton introduction is also available, retaining the ordinary Boolean rules:

```math
\frac{}{\Gamma\vdash_G \mathsf{true}:\mathsf{boolLit}(\mathsf{true})}
\qquad
\frac{}{\Gamma\vdash_G \mathsf{false}:\mathsf{boolLit}(\mathsf{false})}.
```

A numeric literal has the same pair and only that pair: `numLit` gives it its
own singleton, and `num` gives it the family. Neither reaches a union above
either one; that is the subsumption rule's work, exactly as for a Boolean. A
literal claimed at $\mathsf{Number}$ need not have a singleton label in the graph to be coerced from,
which is why the family rule is separate rather than derived.

```math
\frac{}{\Gamma\vdash_G n:\mathsf{numLit}(n)}
\qquad
\frac{}{\Gamma\vdash_G n:\mathsf{Number}}.
```

A literal's $n$ is the double its decimal lexeme rounds to: TypeScript's
decimal spelling of a hexadecimal, octal or binary literal or of one with
separators, and the source's decimal text of one past the largest double
(`1e309`, which TypeScript spells `Infinity`), so a literal type and a value
of it name the infinity alike (`numericLexeme`).

A bigint literal has the same pair, `bigintLit` and `bigint`:

```math
\frac{}{\Gamma\vdash_G i\mathtt{n}:\mathsf{bigintLit}(i)}
\qquad
\frac{}{\Gamma\vdash_G i\mathtt{n}:\mathsf{BigInt}}.
```

Functions take ordered parameter lists and a receiver. Write $\vec A$ for a
signature's parameter types, $|\vec A|$ for its length and $R$ for its
receiver: the `this` a call passes, which is not a parameter. In the
closure creation rules below, every signature offers at least the code's
arity, and the code runs from that signature's receiver, then its first
$\mathit{arity}$ parameters, then the captured bindings (`bodyFrame`). A
signature may offer more: the call binds the first $\mathit{arity}$ actuals
and discards the rest, as JavaScript does. Code with a rest keeps exact fixed
parameters: its extra actuals go to the rest, not away.
This holds of the code, not of any value at a shorter signature: code with a
rest collects extra actuals and a bound function forwards them, so no
subtyping rule widens an arrow's parameters. For the same reason code without
a rest also meets a variadic signature $(R;\vec A,\ldots E\to B)$ whose fixed
parameters cover its arity: a call through it writes any number of actuals,
the code binds its first $\mathit{arity}$, all at fixed positions, and
discards the rest (`restsT_of_graph`). Its code is checked at that
signature's fixed row $(R,\vec A,B)$, with the fixed signatures
(`offerRows`); a closure binding a position of the rest, which a call may
leave unwritten, is not created at it. A call passes its receiver $r$ and
types it at the selected signature's receiver:

```math
\frac{\Gamma\vdash_G f:\bigwedge_{(Q,\vec C,D)\in L}(Q;\vec C\to D)
      \quad(R,\vec A\,\vec U,B)\in L\quad\Gamma\vdash_G r:R\quad\forall i.\;\Gamma\vdash_G a_i:A_i
      \quad\forall U\in\vec U.\;\Gamma\vdash_G \mathsf{undefined}:U}
     {\Gamma\vdash_G \mathsf{invoke}(f,r,\vec a):B}
```

with $S^\flat=\{(R,\vec A,B)\mid(R,\vec A,E,B)\in S\}$. A plain call $f(\vec a)$ is $\mathsf{invoke}(f,\mathsf{undefined},\vec a)$,
and `.call` and `.apply` of a function (the standard intrinsics) pass their
first argument as the receiver, so it meets the selected signature's
receiver, the function's `this` parameter:

```math
f.\mathtt{call}(r,\vec a)\;\equiv\;\mathsf{invoke}(f,r,\vec a)
\qquad
f.\mathtt{apply}(r,[\vec a])\;\equiv\;\mathsf{invoke}(f,r,\vec a)
```

In
de Bruijn form the receiver's slot precedes the parameters, $\mathit{this}$
then $\vec x$, before the captures; an arrow's code has that slot too and
never reads it, and a source `this` in an arrow resolves to an enclosing
ordinary function's slot as a capture. The rule's receiver premise is
contravariant under subsumption like each domain
([`CallArrow`](POSITIVE-TYPES.md#function-and-class-coverage)), so a
function indifferent to its receiver, typed at $\top$, meets any receiver
requirement, and one that reads its receiver cannot be widened to arbitrary ones.

Every closure's body is a graph ([graph code](SEMANTICS.md#graph-code)),
checked where its code is, not where it is created. Code $\kappa$ of arity
$m$ with captures at $\vec C$ meets a signature, written
$\vec C\vdash_G\kappa:(R;\vec A\to B)$ (`GraphCodeSpec`), when $m\le|\vec A|$
and every run of it entered from an environment meeting
$R,\vec A_{<m},\vec C$ is safe at $B$. Code with a rest is entered with the
store of the further actuals first: $\vec C\vdash_G\kappa:(Q;R;\vec A\to B)$
when every run entered from $Q,R,\vec A_{<m},\vec C$ is safe at $B$
(`codeFrame`). The [graph checker](#checked-control-flow-graphs) establishes
either from the code's own certificate at that entry and the result $B$
(`GraphCode.codeChecked_sound`). What code offers depends on whether it
collects a rest (`CodeOffers`): code without one meets each fixed signature
and each variadic one's fixed row; code with one offers only variadic
signatures, each taking exactly its fixed parameters, from a frame whose
store $Q$ is one its rest's pack describes
($\mathrm{Store}_G$, below):

```math
\mathrm{Offers}_G(\kappa,\vec C,L,S)\iff
\begin{cases}
\forall(R,\vec A,B)\in L\cup S^\flat.\;\vec C\vdash_G\kappa:(R;\vec A\to B) & \kappa\ \text{collects no rest}\\
L=\varnothing\ \land\ \forall\sigma=(R,\vec A,P,B)\in S.\;|\vec A|=m\land\mathrm{Store}_G(Q_\sigma,P)\land\vec C\vdash_G\kappa:(Q_\sigma;R;\vec A\to B) & \kappa\ \text{collects a rest}
\end{cases}
```

Soundness is `offers_sem`: code without a rest meets its signatures by
`callsT_of_graph` and `restsT_of_graph`, code with one its variadic
signatures by `restsT_of_graphRest`, whose invocation allocates the store
before the run starts (`graphRest_invoke`). Creation then reads the captures
only:

```math
\frac{\mathrm{Offers}_G(\kappa,\vec C,L,S)
      \quad\forall i.\;\Gamma\vdash_G x_i:C_i}
     {\Gamma\vdash_G \mathsf{make}(\kappa[\vec x],\mathsf{null}):\bigwedge_{(R,\vec A,B)\in L}(R;\vec A\to B)
       \land\bigwedge_{(R,\vec A,E,B)\in S}(R;\vec A,\ldots E\to B)}\ (\texttt{funGraph})
```

where $\kappa[\vec x]$ is $\kappa$ capturing the slots $\vec x$. Its evidence
(`Rule.funGraph`) names each signature as an entry of the unit's code table:
the codes a request carries, each checked in order against the table of those
before it (`GraphCode.checkCodes`), so that every entry meets its signature
(`CodesSound`, `checkCodes_sound`); code created inside code is checked first.
No code check reads the graph's assignment (`Parametricity.checkEntry_reassign`),
so an entry meets its signature in the graph reassigned at every assignment
$\eta$ of its parameter rows, $\vec C\vdash_{G[\eta]}\kappa:\sigma$, which is
what `CodesSound` states. For code with a rest the evidence also lists the
store types $Q_\sigma$, in the signatures' order (`Rule.funGraph arrays`), and
each table entry the store its frame starts with (`CodeEntry.store`).

A generic closure is graph code at a scheme row $j$, $G(j)=\forall\vec p.\,(L,S)$
with binders $\vec p$ (parameter rows) and signatures $L$ and $S$ over them
(`HasTyUsing.funScheme`). Its code is checked once, at the scheme's own signatures:
a table entry holds at every assignment, so at every instantiation of $\vec p$.
Its captures' types read none of $\vec p$ (`capturesFree`: their free parameter
rows, computed and checked by `FreeOk`,
exclude the binders), so a capture means at every instantiation what it means
here (`meaning_assign_free`):

```math
\frac{G(j)=\forall\vec p.\,(L,S)
      \quad\forall\eta.\;\mathrm{Offers}_{G[\eta]}(\kappa,\vec C,L,S)
      \quad\mathrm{fv}(\vec C)\cap\vec p=\emptyset
      \quad\forall i.\;\Gamma\vdash_G x_i:C_i}
     {\Gamma\vdash_G \mathsf{make}(\kappa[\vec x],\mathsf{null}):j}\ (\texttt{funScheme})
```

Soundness is **Call-Scheme-I** ([below](#overloads-polymorphism-and-binding))
with each instance's signatures read in the graph reassigned at that instance.
The evidence is `Rule.funGraph` at a scheme row: the checker reads the row's
signatures instead of an arrow clause's (`graphCodesChecked`, `schemeOf`). A
binder with a bound of clause rows is read, in the signatures and inside the
closure, as the meet row $p\sqcap B$, as a generic unit's is: at every
instantiation within the bound the meet is the binder. A binder bounded by
another of the closure's binders, `U extends T`, is read as the meet of the two
parameter rows, $p_U\sqcap p_T$ within $T$'s clauses if it has any
(`dependentMeet`): its bound reads a binder, which a scheme row's bounds, read
outside its binders, cannot, so the meet alone states it. A call of a binding
at the scheme row names its instance: the callee is read at the instance's
signature, below the scheme by a checked instance (`InstArrs`), a meet row
mapped to the meet of its parameters' type arguments with its clauses
(`meetOk`).

A call writes a prefix of the positions the selected signature declares:
$|\vec a|=|\vec A|$, and $\vec U$ are the positions it omits. Omission is
admissible exactly when each omitted contract admits `undefined`: that is part
of what the signature promises (below), and closure code keeps the promise
because `CallArguments.parameters` pads a short actual list, so the body
dispatched for $f(\vec a)$ is the same term as for the call that writes those
`undefined`s out (`CallArguments.parameters_pad`, in `frame_envOk`, the
frame every code is entered with). With $\vec U$ empty this is the exact-arity rule.
No actual is invented: the call term keeps the arguments the source writes.

Optionality is therefore a property of a declared contract, not a separate
arity record: `x?: T` is carried as `T | undefined`, which is what the body
reads and what licenses the omission. Declared arity is not observable in this
fragment, so a call may also omit a trailing position a producer declared as
`T | undefined` without writing `?`, which TypeScript rejects; the verifier
proves such a call safe rather than enforcing that surface rule. An empty
parameter list is a zero-argument call, not an absent one. A tuple rest
parameter and a tuple spread are a fixed number of positions each, so they need
no rule of their own here: the signature carries the positions, and the array a
rest parameter binds is allocated by the ordinary store and allocation rules.
Into fixed parameters, each spread's positions are ordinary element reads of
its operand's store, made once every actual is evaluated, in position order,
and the call takes them as actuals where the spread is written; the lowering
admits no actual that runs code after the first spread, so the reads see what
JavaScript's spreads, each read where it is written, would.
That array is fresh, so a rest parameter's contract may also be `readonly`
(`readonly T[]`, a readonly tuple) or name one through a declared alias: the
body sees the fresh array through that view, which gives up only writes. A
generic alias is read through its equation at the reference's arguments,
$\mathit{Alias}\langle\vec A\rangle = E[\vec A/\vec X]$, in a definition, a
function type and a declared function alike, as TypeScript reads it:

```math
\frac{\mathsf{type}\ \mathit{Alias}\langle\vec X\rangle = E\quad E[\vec A/\vec X]\ \text{an array or a tuple of required positions}}
     {\ldots x : \mathit{Alias}\langle\vec A\rangle\ \text{collects into}\ E[\vec A/\vec X]}
```

A rest typed by anything else is refused by its form: by a type parameter
(a function definition has no allocation rule for an array only an instance
fixes; a function type's is a pack), by an intersection (its contract can be empty
at an instance TypeScript admits, [refused on principle](DESIGN.md#refused-on-principle)), by a tuple with
optional or rest elements (several lengths), or by what is no array.

A function type is a promise about the actual lists a caller may write, not
about the callee's code. A fixed signature $\vec A\to B$ admits the prefixes of
$\vec A$ whose omitted positions admit `undefined`. A variadic signature
$\vec A,\ldots P\to B$ has a rest type $P$, an [argument pack](POSITIVE-TYPES.md#argument-packs):
it admits the lists whose first actuals $\vec A$ admits, as a fixed signature
does, and whose actuals past them are, as one list, in $P$'s argument lists,
at the current level (`argMeaning`). An element rest `...xs: E[]` admits any
number of actuals in $E$, $\mathsf{Pack}([\,],[\,],E)$ (`restElem_args`); a
tuple rest `...xs: [A, B]` exactly those positions:

```math
\mathrm{Adm}(\vec A)=\{\vec v\mid |\vec v|\le|\vec A|,\ \forall i<|\vec v|.\,v_i\in A_i,\ \forall |\vec v|\le i<|\vec A|.\,\mathsf{undefined}\in A_i\}
```

```math
\mathrm{Adm}(\vec A;P)=\{\vec v\mid \vec v_{<|\vec A|}\in\mathrm{Adm}(\vec A),\ \mathsf{args}(\vec v_{\ge|\vec A|})\in P\}
\qquad(\texttt{ArgsRest}).
```

A list shorter than $\vec A$ passes the empty pack, which an element rest
admits and a tuple rest with required positions does not.

A value meets a signature when every admitted list of values invokes it safely
at $B$, at every later world and budget (`Safety.Promise`, `callsT`, `restsT`).
This instantiates the [common behavioral equation](SEMANTICS.md#one-meaning-for-callable-contracts),
which also explains overload conjunction, callable fields and quantification.
Code enters only where it is created: graph code pads a short list
(`graph_invoke`), and code with a rest collects the actuals past its $k$
fixed parameters into a fresh store, which its entry allocates with the
ordinary steps before the run starts (`graphRest_invoke`):

```math
\mathrm{invoke}(\kappa^{\ldots}[\vec c],r,\vec v)=
\mathsf{let}\ x=\mathsf{arr}(v_k,v_{k+1},\ldots)\ \mathsf{in}\ \mathsf{goto}(E,K,s,[x,r,\mathrm{pad}_k(\vec v),\vec c])
\qquad(\texttt{graphEntry})
```

A pack holds its actuals at their positions only below the current level. The
allocation is a step, after which the budget is one lower, so that is all the
fresh store's contracts need (`arr_alloc_rule_below`, `pack_alloc_safe`).

So one value may meet fixed and variadic signatures at once, and a graph call
clause carries both: `arrs L S`, `callable P Ps L S`. Write
$\mathrm{Store}_G(Q,P)$ when $Q$ is the store $P$'s one tuple contract
describes, writable since the store is fresh (`RestStore`), and $\mathrm{Spreads}_G(S,E)$ when $S$ is a
store contract every position of which is within $E$, and either it is
dense or $E$ includes `undefined` (`SpreadsInto`). A hole yields
$\mathsf{undefined}$ and must therefore be admitted by $E$. Creation checks the code once per variadic signature, from the
frame with the rest store in slot 0, the receiver in slot 1, then the fixed
parameters: the second case of $\mathrm{Offers}_G$ (`funGraph`;
`callableGraph` adds a field bag). The code's entry node wraps the store into
the array the rest parameter names, an ordinary allocation the extractor
emits.

[RestCalls.lean](lean/Verification/Model/Programs/RestCalls.lean) proves variadic calls: eliminating a variadic signature, allocating the rest store, spreading actuals.

A call writes the fixed actuals, or a prefix whose omitted positions admit
`undefined`, then parts that fit the rest; a call that omits a fixed position
writes no part (`callRest`). With a spread among the parts, the rest is an
element rest $\mathsf{Pack}([\,],[\,],E)$ ($\mathrm{elem}_G(P)=E$,
`restElem`), and each part is an actual in $E$ or a spread of a store whose
elements are. Without one, $P$ is one tuple contract $\tau$, and the parts are
at its positions within its length bounds (`RestParts`):

```math
\frac{\begin{array}{c}\Gamma\vdash_G f:F\quad(\vec A\,\vec U,P,B)\in\mathrm{restSigs}_G(F)
      \quad\forall i.\;\Gamma\vdash_G a_i:A_i\quad\forall U\in\vec U.\;\Gamma\vdash_G\mathsf{undefined}:U\\
      \vec U=\varepsilon\lor\vec p=\varepsilon\qquad\mathrm{Parts}_G(P,\vec p)\end{array}}
     {\Gamma\vdash_G f(\vec a,\vec p):B}
```

```math
\mathrm{Parts}_G(P,\vec p)\iff
\begin{cases}
\mathrm{elem}_G(P)=E\ \land\ \forall p\in\vec p.\;\Gamma\vdash_G p:E\ \lor\ (p={\ldots}s\land\Gamma\vdash_G s:S\land\mathrm{Spreads}_G(S,E)) & \text{a spread in }\vec p\\
P=\mathsf{Pack}(\tau)\ \land\ |\tau.R|\le|\vec p|\ \land\ (\tau.E=\varnothing\Rightarrow|\vec p|\le|\tau.R|+|\tau.O|)\ \land\ \forall i.\;\Gamma\vdash_G p_i:\mathsf{pos}_\tau(i) & \text{otherwise}
\end{cases}
```

The first case is `rest_call_safe`: the actuals collected at $E$ form a list
the element rest admits (`restElem_args`). The second is `pack_call_safe`: the
actuals at the positions form a list $\tau$ admits (`restParts_pack`). The
rest store is allocated from those actuals at the current level; the
allocation step consumes the level (`restStore_safe`,
`RestCalls.argument_alloc_safe`). `RestStore` checks identical element positions
and length bounds and requires a writable result. The fresh store may use any
presence mode: all collected positions exist. Pack metadata does not impose a
lifetime presence contract on this allocation.

A spread is read by the call once every earlier actual is a value, the store's
elements replacing it in order, `undefined` at a hole
(`Step.callSpread`, `spread_parts_safe`):

```math
(h,\ f(\vec v,\ {\ldots}\mathsf{arr}(\vec\ell),\ \vec p))\longrightarrow
(h,\ f(\vec v,\ h(\ell_1),\ldots,h(\ell_m),\ \vec p))
```

Into a rest, a spread followed by an actual that runs code is copied where it
is written, `[...s]`, a fresh store the call then spreads, so the later actual
cannot change what it passes (`Step.arrSpread`, `copy_safe`, `arrCopy`); into
fixed parameters the lowering admits no such actual (above):

```math
\frac{\Gamma\vdash_G s:S\quad\mathrm{Spreads}_G(S,E)}
     {\Gamma\vdash_G [{\ldots}s]:\mathsf{List}_{\pi,\mathrm{writable}}([\,],[\,],E)}
```

Here $\pi$ is any presence mode chosen for the fresh store's lifetime contract.
No existing location is retyped. A hole read from the source becomes a present
`undefined` value in the copy.

For a required tuple, source lowering instead reads its known positions in
order into an ordinary array literal before evaluating later actuals. The
existing element-read and array-literal rules preserve the tuple's exact
contract, including density. This avoids weakening a dense Boolean tuple to
an unbounded store that would require `undefined` when spread again.

Covering compares admitted lists. A variadic source with an element rest
covers a fixed target whose first positions are within its fixed parameters and
whose further positions are within its element (`RestFixed`, a `CallArrow`
case). A variadic source covers a variadic target whose parameters are within
its own, the target's further fixed positions taken into the source's rest,
which needs an element rest unless there are none (`IntoRest`), and whose rest
is within its own as a pack (`RestCovers`); results are covariant. A fixed
source never covers a variadic target with an element rest: it promises nothing past its positions. It covers
one whose rest is one exact tuple, of any positions, its parameters within the
source's first and the tuple's positions within the rest
(`FixedCallsPack`, as `FixedCoversPack` for construct signatures in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md#function-and-class-coverage));
at level zero the call exists and nothing past it is owed.

```math
\frac{k=|\vec P|\le|\vec A|\quad\forall i<k.\;A_i\le P_i\quad\mathrm{elem}_G(P')=E\quad\forall k\le i<|\vec A|.\;A_i\le E\quad B\le D}
     {(\vec P,\ldots P'\to B)\le(\vec A\to D)}
```

```math
\frac{k=|\vec P|\le|\vec Q|\quad\forall i<k.\;Q_i\le P_i\quad
      (k=|\vec Q|\ \lor\ \mathrm{elem}_G(P')=E\land\forall k\le i<|\vec Q|.\;Q_i\le E)\quad Q'\le P'\quad B\le D}
     {(\vec P,\ldots P'\to B)\le(\vec Q,\ldots Q'\to D)}
```

```math
\frac{Q'=\mathsf{Pack}(\vec E)\ \text{exact}\quad\forall E\in\vec E.\,\mathsf{stable}(E)\quad
      |\vec P|=|\vec Q\vec E|\quad\forall i.\;(\vec Q\vec E)_i\le P_i\quad B\le D}
     {(\vec P\to B)\le(\vec Q,\ldots Q'\to D)}
```

```math
\frac{\Gamma\vdash_G a:A\quad\Gamma,x:A\vdash_G b:B}
     {\Gamma\vdash_G \mathsf{let}\ x=a\ \mathsf{in}\ b:B}
```

A bound function (`bindE`) is allocated from saved slots: the target $f$, the
receiver $r$ and the prefix $\vec p$, whose types the rule reads from the
context. The target's selected signature starts with the prefix's types; the
result takes the rest, at any receiver, since invoking it drops the receiver it
is given (`CallCode.bound`, `callsT_bound`):

```math
\frac{\Gamma(f)=F\quad(R,\vec P\,\vec D,B)\in\mathrm{callSigs}_G(F)
      \quad\Gamma(r)=R\quad\Gamma(\vec p)=\vec P}
     {\Gamma\vdash_G\mathsf{bound}(f,r,\vec p):(Q;\vec D\to B)}
```

A method member is host-relative: its contract holds when it is invoked on
the object it is read from ([DESIGN.md](DESIGN.md#method-members-are-host-relative)).
A member bound to its host (`bindMember`) is read from the object in slot $i$
and bound to that same object in one term, so the member is read before any
actual runs, as JavaScript reads it, and the bound function meets the member's
signatures at any receiver, and every signature one of them covers: each
claimed parameter within the member's, for a variadic signature of as many
fixed parameters the claimed rest within the member's too, and the member's
result within the claimed one, by checked subtyping proofs the certificate
carries (`CoveredCall`, `CallProofs`, `CoveredRestUsing`, `RestProofsUsing`).
The host's type is within each type the member's host must meet, a `this`
parameter's ($m.\mathsf{this}$), by checked proofs the certificate carries
too. A claim may so name another label for the same type, as a producer's own row
for a declared `[number, number]`, or for a declared rest
`EagerCollection<K, V>[]` at its instance, which the declaration's literal
head applied to the instance's arguments names too. With
$\mathrm{member}_G(O,k)=m$ the method of key $k$ in $O$'s one object
clause (`memberOf`):

```math
\frac{\Gamma(i)=O\quad\mathrm{member}_G(O,k)=m
      \quad\forall(Q,\vec D,B)\in L.\;\exists(\vec C,B')\in m.\mathsf{calls}.\;
        G\vdash\vec D\le\vec C\land G\vdash B'\le B
      \quad\forall(Q,\vec D,P,B)\in S.\;\exists(\vec C,P',B')\in m.\mathsf{rests}.\;
        G\vdash\vec D\le\vec C\land G\vdash P\le P'\land G\vdash B'\le B
      \quad\forall T\in m.\mathsf{this}.\;G\vdash O\le T}
     {\Gamma\vdash_G\mathsf{let}\ f=i.k\ \mathsf{in}\ \mathsf{bound}(f,i,[]):\mathsf{arrs}(L;S)}
```

Both $\vec D$ and $\vec C$ are the fixed parameters, of equal length, and the
effects are covered as for a call. The rest premise is an inclusion of
argument lists: a checked proof relates the argument-list component of the
two types' meanings as it relates their values (`argsAcceptedUsing`), and a
variadic signature admits every list a narrower one does (`ArgsRest_mono`).

A generic method's member states its signatures as schemes, quantified
signatures the member bound to its host meets
([records](POSITIVE-TYPES.md#records)). The same term, bound to its host, is
then one of those schemes (`bindScheme`), and a call names its instance below
it ([`InstArrs`](POSITIVE-TYPES.md#instances-of-a-scheme-row)):

```math
\frac{\Gamma(i)=O\quad\mathrm{member}_G(O,k)=m\quad [j]\in m.\mathsf{schemes}}
     {\Gamma\vdash_G\mathsf{let}\ f=i.k\ \mathsf{in}\ \mathsf{bound}(f,i,[]):[j]}\ \textsf{bind-scheme}
```

The certificate is `bindMember` with no proofs, at a type of no clauses, the
scheme row. A scheme's own receivers are the forwarding function's, which
ignores them, so a member's scheme admits every receiver; an instance may
state a narrower one, the call's object (`instSig`).

The member read from $v=\rho(i)$ meets $m$'s signatures with receiver $\{v\}$
where $v$ is in each of $m.\mathsf{this}$ (`memberOf_at`,
`MethodMembers.onHost`), which $v\in O$ and the proofs of $O\le T$ give. The read finds the key on $v$, or, one
step later, on the object $v$'s prototype holds (`Step.readProto`,
`member_read_safe`), as the member's meaning says. The bound descriptor, which has
no fields and allocates nothing, forwards any call to it with receiver $v$
(`callsT_bound`, `restsT_bound`). The source form `o.m.bind(o)`, `o` one
immutable name and `m` a method member of its type, is this term: `bind`
of what `o.m` holds to `o` itself, a bound function whatever receiver it is
later called with (`closureExpr`); the iterator protocol reads `next` so.

A variadic target with an element rest (`bindRestE`, `restsT_bound`) gives
its first fixed positions to the prefix and, past them, its element $E$; the
result keeps the positions left and the rest $P$, which admits the prefix's
values past the fixed positions in front of any list it admits:

```math
\frac{\Gamma(f)=F\quad(R,\vec P,P',B)\in\mathrm{restSigs}_G(F)\quad\mathrm{elem}_G(P')=E
      \quad\Gamma(r)=R\quad\Gamma(\vec p)=\vec P_{<k}\,E^{\,k-|\vec P|}\quad k=|\vec p|}
     {\Gamma\vdash_G\mathsf{bound}(f,r,\vec p):(Q;\vec P_{\ge k},\ldots P'\to B)}
```

Here $\lambda\vec x.t$ denotes source function creation, graph code whose
body is $t$'s graph (`funGraph`): it allocates an object before any invocation. `let` has its own operational constructor, `letE a b`. It evaluates `a`,
then substitutes the resulting value into `b` in one nonallocating step.
Neither a function value nor a function-type graph label is needed. The
producer and consumer use this constructor directly. [ExecutionModelTests.lean](lean/Verification/Model/Tests/ExecutionModelTests.lean) shows the machine
taking no step of the body while the initializer is stuck.

A class value is construct-only code: JavaScript gives a function object
`[[Call]]` and `[[Construct]]` separately, and a class has only the second,
an arrow only the first. The calculus records which in the closure's code
(`kind`), a plain call dispatches only call code, and `new f(args)` is its own
term, which evaluates `f`, then the actuals, and runs only construct code, with
`undefined` for the receiver. A construct signature
$\mathsf{new}(A_1,\ldots,A_n)\Rightarrow B$ (the `ctors` clause) is met by a
class whose code, for actuals at the parameters, is safe at $B$. As for a
function, a signature may offer more parameters than the constructor binds:
the construct step binds its first $\mathit{arity}$ actuals and discards the
rest, so the code is checked at the signature's first $\mathit{arity}$
parameters, entered with `undefined` for the receiver. Its code $\kappa^{\mathsf{new}}$ is
construct-only graph code:

```math
\frac{L\equiv_G\mathsf{Ctors}(\ldots,(\vec A,B),\ldots)\quad
      U\equiv_G\mathsf{Undefined}\quad
      \vec C\vdash_G\kappa^{\mathsf{new}}:(U;\vec A\to B)\ \text{for each signature}\quad
      \forall i.\;\Gamma\vdash_G x_i:C_i}
     {\Gamma\vdash_G \mathsf{make}(\kappa^{\mathsf{new}}[\vec x],\mathsf{null}) : L}
\qquad
\frac{\Gamma\vdash_G f:L\quad L\equiv_G\mathsf{Ctors}(\ldots,(\vec A\,\vec U,B),\ldots)\quad
      \Gamma\vdash_G a_i:A_i\quad\Gamma\vdash_G\mathsf{undefined}:U_j}
     {\Gamma\vdash_G \mathsf{new}\ f(\vec a):B}
```

A plain call of a class throws in JavaScript: `ocaml-producer/test.mts` runs
`invalid-class-as-function` under Node beside the pipeline's refusal of it.
[ExecutionModelTests.lean](lean/Verification/Model/Tests/ExecutionModelTests.lean) shows the model's `new` running no call-only code, as JavaScript's `new`
of an arrow throws.

These are `ctorGraph` (`ctorsT_of_graph`) and `construct`. As a call may,
`new` may omit trailing positions $\vec U$ whose contracts admit `undefined`:
the construct step binds `undefined` there, so the run entered is the one the
padded list enters (`construction_pad`), and the source term keeps the actuals it writes. A
`new` with explicit type arguments, `new C<T>()`, names the instance of a
generic class it constructs: the producer proposes that instantiation, and it
is checked as an inferred one is ([explicit type arguments](#explicit-type-arguments)). No arrow meets a construct signature and no
class a call signature, so `new` on an arrow and a plain call of a class are
refused, as JavaScript throws. A construct signature is covered by one taking
as many parameters, each at least as wide, with a result at most as wide:
`new (params: Specific) => R` is a `new (params: never) => R`.

An object is a finite map from field names to heap locations, fixed at
allocation. Let $\varphi$ range over field maps $\overline{f{:}A}$ with distinct
names, and write $\mathsf{Ref}(\varphi)$ for the record clause carrying those
invariants. `alloc` allocates one fresh location per named field, and the names
being distinct is what makes the result a map from them. The object's own keys
are exactly those names, so its type may also bound them: each own-key bound
$b$ the type states must admit every name
([POSITIVE-TYPES.md](POSITIVE-TYPES.md#records)). An array is allocated this
way, its store and prototype as the two fields, own keys among those two, then
read as an array, owning none of `ArrayProto`'s keys, by subsumption. A record
type is of objects meeting the realm's
[array invariant](SEMANTICS.md#the-array-invariant), so an allocation owning
the store key $\sigma$ must be an array of the realm
($\mathsf{realm}\vDash\overline{f{:}A}$, `allocRealm`): its store field at a
store type (every clause a `list`, whose members are possibly sparse stores of values,
`storeTy_sound`), its prototype field at the realm's prototype type
$P_{\mathcal R}$, which reads no parameter row (`realmFree`, so it means the
same at the assignment the invariant reads it at, `realmFree_meaning`), and
none of its names a key that prototype provides ($N_{\mathcal R}$). An
allocation without $\sigma$, or in a graph stating no realm, meets it at once:

```math
\frac{\overline{f}\ \text{distinct}\qquad\forall i.\;\Gamma\vdash_G a_i:A_i
      \qquad\forall b\in\beta.\;\forall f\in\overline{f}.\;b\vDash f
      \qquad\mathsf{realm}\vDash\overline{f{:}A}}
     {\Gamma\vdash_G\{\overline{f=a}\}:\mathsf{Ref}(\overline{f{:}A};\beta)}
```

```math
\mathsf{realm}\vDash\overline{f{:}A}\iff
\sigma\notin\overline{f}\ \lor\ \bigl(\overline{f}\cap N_{\mathcal R}=\varnothing\land
  (\sigma{:}S)\in\overline{f{:}A}\ \text{with}\ S\ \text{a store type}\land(\mathsf{proto}{:}P_{\mathcal R})\in\overline{f{:}A}\bigr)
```

`read` and `write` name the field they act on and require it of the receiver's
contract. A contract constrains only the fields it names, so a receiver may
carry fields the rule never mentions — width subtyping is this openness, not a
separate rule. A read takes the field from the receiver's **named members**,
the invariant fields $\varphi$ and readonly views $\psi$ of a clause with one
record operand, a record's or a dictionary's, whose named members hold beside
its index views (`namedMembers`):

```math
\mathsf{named}(\mathsf{Ref}(\varphi;\psi;\ldots))=(\varphi;\psi)
\qquad
\mathsf{named}(\mathsf{Dict}(\varphi;\psi;\overline{D};\ldots))=(\varphi;\psi)
```

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c\quad\mathsf{named}(c)=(\varphi;\psi)\quad(f{:}A)\in\varphi}
     {\Gamma\vdash_G a.f:A}
\qquad
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi)
      \quad(f{:}A)\in\varphi\quad\Gamma\vdash_G a':A}
     {\Gamma\vdash_G a.f\leftarrow a':\mathsf{Null}}
```

Both rules read $\varphi$ off a single reference clause. Eliminating a
conjunction of record contracts to such a view can be justified by subsumption;
no direct multi-contract program rule is assumed, so a field supplied only by a
second operand of an intersection needs such a view before these rules apply.

An index view over a key class $\theta$ constrains every **present** field
under a key of $\theta$ at its element contract $A$ (every string key, the
canonical numeric ones, or every symbol key: [POSITIVE-TYPES](POSITIVE-TYPES.md#records));
it says nothing of any other. A computed index first evaluates the receiver,
then its key, which `ToPropertyKey` converts: a string is its key, a symbol
its identity, a number the key its `ToString` spells. The key's type is the
key clause of a class $\theta_k$ within the index's
($\mathsf{key}(\mathsf{strings})=\mathsf{String}$,
$\mathsf{key}(\mathsf{numeric})=\mathsf{Number}$,
$\mathsf{key}(\mathsf{symbols})=\mathsf{Symbol}$; $\theta_k\sqsubseteq\theta$),
so a number reads a number index or a string one. Because that key can be
absent, the proved `indexDict` rule includes `undefined` in the result:

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Dict}(\theta{:}A)\quad
      \Gamma\vdash_G k:K\quad K\equiv_G\mathsf{key}(\theta_k)\quad\theta_k\sqsubseteq\theta\quad
      U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a[k]:A\cup U}
```

The separate `readDict` rule covers a fixed key $\kappa$ with the same result
contract, through an index whose class surely admits it ($\theta\ni_!\kappa$,
`IndexKeys.surely`: any string key for $\mathsf{strings}$, a key a number
spells for $\mathsf{numeric}$, checked by that number, a symbol key for
$\mathsf{symbols}$); a symbol key is never read through a string index, nor
`"01"` through a number index. The `readOptional` rule reads an optional
field of a record, writable or readonly, at its type or `undefined`: where the
object has the key, its location's contract is that type, or implies it for a
readonly field (`optT`), and where it does not, the read is `undefined`
(`read_optional_rule`). With $\mathsf{Ref}(\varphi;\psi;\omega)$ a record's
invariant fields, readonly views and optional fields $\kappa{:}^{r}A$ of mode
$r$, and $\kappa$ a [property key](POSITIVE-TYPES.md#records):

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c\quad\mathsf{named}(c)=(\varphi;\psi)\quad(\kappa{:}A)\in\psi}
     {\Gamma\vdash_G a.\kappa:A}
\qquad
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi;\psi;\omega)\quad(\kappa{:}^{r}A)\in\omega
      \quad U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a.\kappa:A\cup U}
```

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Dict}(\varphi;\psi;\overline{D};\omega)\quad (\theta{:}A)\in\overline{D}
      \quad\theta\ni_!\kappa\quad U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a.\kappa:A\cup U}
```

A key one of the record's own-key bounds $b$ does not admit is not the
object's own, so its read continues at the prototype, which the record holds
under the reserved key at $P$ (`readProto`). For an array, $b$ excludes
`ArrayProto`'s keys, so every prototype member is read this way, whatever
further keys the array owns:

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi;\psi;\omega;\beta)\quad b\in\beta\quad b\nvDash\kappa\quad
      (\mathsf{proto}{:}P)\in\varphi\,\psi\quad P\equiv_G\mathsf{Ref}(\varphi';\psi';\ldots)\quad
      (\kappa{:}A)\in\varphi'\,\psi'}
     {\Gamma\vdash_G a.\kappa:A}
```

The delegation is one step (`Step.readProto`), and the prototype's field or
view is read one level down (`read_proto_rule`).

These are `readView`, `readOptional`, `readProto` and `readDict`; the
dictionary reads apply whatever writable index contracts the clause also
carries. The `read` and `write`
rules above take $(\kappa{:}A)\in\varphi$ from the invariant fields alone,
whatever the views and optional fields. A dictionary's named field or view is
read at its own contract by `read` or `readView`, since `dictViewT` sits beside
the named members' `recT` and `viewT` (`namedMembers_sem`); only a key it does
not name is read through the index, with `undefined`. An optional named field
($\omega$ above) holds beside the index as a named field does, so a key the
dictionary does not name is still read through the index: `process.env` is a
writable index beside the optional `TZ`. A write to a writable optional
field may add its key: it is a [key-adding write](#key-adding-writes), a copy
of a local's own object, refused on any other; a readonly one grants no write
in any case.

A fresh literal meets a readonly dictionary, or a record whose optional
fields it leaves out, with no rule of its own: `alloc` types it at the record
whose own keys are bounded by exactly its names, and that record is below the
target by coverage through the bound
([`CoversKeys`, `CoversOptional`](POSITIVE-TYPES.md#records)). No other key
exists and the prototype key is not among them, so the object has no
prototype, lacks every key it does not write, and each field's contract need
only be within each index view. The literal may be empty, `{}`, and may write
members the dictionary names:

```math
\frac{\vec k\ \text{distinct}\quad\Gamma\vdash_G e_i:A_i\quad
      G\vdash\mathsf{Ref}(\overline{k_i{:}A_i};\{\vec k\})\le D}
     {\Gamma\vdash_G\{\overline{k_i{:}e_i}\}:D}
```

which is `alloc` followed by subsumption; the producer states the bounded
record as the literal's claim wherever its contract has a readonly index or
an optional field. None of these rules grants a write capability to a
readonly dictionary.

A writable index is never met through an own-key bound (but at a contract no
value meets, where no key can be added): code holding the dictionary may add
a key of its class, which a bound listing keys, or one excluding such a key,
says is absent
([writable string index signatures](DESIGN.md#writable-string-index-signatures),
[covering](POSITIVE-TYPES.md#records)). So a literal meant for a writable
dictionary is allocated at the dictionary itself, `allocDict`: its fields are
the clause's named fields, none the prototype key or the store key, each whose key an index's
class may admit ($\theta\ni_?k$, `IndexKeys.may`) at exactly that index's
type, and the clause states no own-key bound. It may state optional fields
$\omega$ the literal leaves out, each, where a writable index's class may
admit its key, at exactly that index's type or beside an index no value meets
($\varnothing(V)$), so a key added there keeps it. The object owns no other
key, so every index, a view or writable, holds of it (`dictCellT_of_recT`),
it lacks every optional field (no prototype), and no bound is claimed that a
key added later would falsify. With $\overline{D}$ the index views and
$\overline{C}$ the writable indexes:

```math
\frac{\begin{array}{c}
      \vec k\ \text{distinct}\quad\mathsf{proto},\sigma\notin\vec k\quad
      \Gamma\vdash_G e_i:A_i\quad
      \forall i.\;\forall(\theta{:}V)\in\overline{D}\,\overline{C}.\;\theta\ni_?k_i\Rightarrow A_i=V\\
      \forall(\kappa{:}^{r}B)\in\omega.\;\kappa\notin\vec k\land
      \forall(\theta{:}V)\in\overline{C}.\;\theta\ni_?\kappa\Rightarrow B=V\lor\varnothing(V)
      \end{array}}
     {\Gamma\vdash_G\{\overline{k_i{:}e_i}\}:\mathsf{Dict}(\overline{k_i{:}A_i};\overline{D};\overline{C};\omega)}
```

Its evidence is `alloc` at a dictionary type. The producer claims the literal
so wherever its contract has a writable index.

```math
\frac{\Gamma\vdash_G t:A\quad\mathrm{check}(G,A,B,p)=\mathsf{true}}
     {\Gamma\vdash_G t:B}
```

One object can carry both a field map and invocation code; the graph clause
$\mathsf{Callable}(\varphi;L)$ combines them. Four rules give it the same four
operations, and they are implemented and proved, not proposed:
`callableGraph` allocates it, typing each field's initializer as `alloc` does
and offering its graph code's signatures as `funGraph` does,

```math
\frac{\vec k\ \text{distinct}\quad\forall i.\;\Gamma\vdash_G e_i:A_i
      \quad\mathrm{Offers}_G(\kappa,\vec C,L,S)
      \quad\forall j.\;\Gamma\vdash_G x_j:C_j}
     {\Gamma\vdash_G \mathsf{make}(\kappa[\vec x],\overline{k_i{=}e_i}):\mathsf{Callable}(\overline{k_i{:}A_i};L,S)}\ (\texttt{callableGraph})
```

one code-table entry per signature; `callCallable`, `readCallable` and
`writeCallable` then invoke, read and write it under the same premises as
`app`, `read` and `write`. Allocation and invocation remain distinct steps:
creation allocates the object, and its code, checked in the table, is not
run.

The clause `top` is semantic top: every closed value inhabits it, and
membership permits nothing, since no read, call, arithmetic or shape rule has
a premise it satisfies; a narrowing fact must be established separately. Every
clause is below it, its intersection with a clause is that clause, and a tag
test on it has no answer. The source type `unknown` denotes it. A `void`
result is a distinct source atom that forgets its guarantee about the value
into the same top: the callee still runs and its effects still happen, only
the result's contract says nothing. `undefined` remains a particular value,
which a body produces by completing, and there is no void value or tag.

A record clause also carries _views_: fields read through a capability. A
view names a location whose stored contract implies the stated family, so a
read through it, by `readView`, observes that family; nothing permits a write
through it, and the backing invariant, which may be stronger, is never
retyped. An invariant field is below a view of the same name whose contract it
implies, and a view is below a weaker view, so a mutable Boolean cell is
viewed as readonly Boolean without ever acquiring a persistent readonly-`true`
guarantee from its current contents; current-content observations stay
separate and subject to invalidation. `readonly` fields are these views.

An array is an object whose store field holds a _store_: the location of each
element in order, or a hole. Identity, aliasing and mutation are the object's;
the store is a value the object replaces when the array grows. A `list` clause
is one or more tuple contracts on a store: required positions, each a
location under its family; optional positions, a hole or such a location; and a
rest family under which any further location must be, without which there is
none. Presence is a separate three-way contract: dense forbids holes,
readable requires a hole's `undefined` to satisfy its position type, and sparse
constrains only present optional/rest entries. Required positions always exist.
Source `T[]` means readable, uniformly in `T`; see the
[array equations](POSITIVE-TYPES.md#arrays). A spread reads at its element type
from either a dense or readable store. A sparse store additionally needs an
explicit `undefined` alternative (`SpreadsInto`); `listT_spreads` proves all three cases. An index in bounds and an
arbitrary one differ, as do a mutable and a readonly array. A readonly store carries
element read capabilities: each location invariant implies the element type.
Writable stores require equality and are invariant; `setElem` requires a
writable store. The outer store field is also a view for a readonly array. `arrLit` allocates a store under the claimed tuple; `elem` reads a
required position named by a literal index, `elemOpt` an optional or rest
position, adding `undefined`, and `elemAny` any numeric index into a
homogeneous array, adding `undefined`; `setElem` writes a named position into
its location, or a fresh one the new store records, keeping the contract for
every alias; `len` reads the length. The source read `a.length` of an
array, in a statement and in a closed expression (an arrow's expression
body, a condition's operands) alike, is the length of its store:

```math
\frac{\Gamma\vdash_G a:A\quad \mathit{store}_G(A)=S\quad
      \Gamma\vdash_G a.\mathtt{[]}:S\quad S\equiv_G\mathsf{list}(\tau)\quad N\equiv_G\mathsf{num}}
     {\Gamma\vdash_G⟦a.\mathit{length}⟧=\mathsf{lenOf}\;(a.\mathtt{[]}):N}\ \textsf{len}
```

A write is typed only at an index no
greater than the required length, so it lands in bounds or appends and never
leaves a hole:

```math
\frac{\Gamma\vdash_G a:L\quad L\equiv_G\mathsf{list}(\tau)\quad
      \Gamma\vdash_G i:\mathsf{numLit}(k)\quad \tau(k)=A\quad
      k\le|\vec R_\tau|\quad \tau\ \text{writable}\quad \Gamma\vdash_G v:A}
     {\Gamma\vdash_G a[i]=v:L}\ \textsf{setElem}
```

Writes at a greater index, or at one no contract names, and reads by a
non-literal index into a tuple, have no rule; a program appends with `push`.
A read `xs[k]` of an array or a tuple at a key TypeScript types as `number`,
no literal, is the host's read of the property the number names, a call of
the intrinsic $\%\mathsf{ElementAt}\%$ (`intrinsics.mts`), which the parser
writes where TypeScript's types of the object and the key are these:

```math
\mathit{xs}[k]\;\equiv\;\%\mathsf{ElementAt}\%(\mathit{xs},\ k)
\qquad
\%\mathsf{ElementAt}\%:\forall T.\ (\mathtt{readonly}\ T[\,],\ \mathtt{number})\Rightarrow T\mid\mathtt{undefined}
```

The element at an index below the length, an own property at another
numeric key, which `Array<T>`'s `[n: number]: T` says holds a `T`, else
`undefined`: `Array.prototype` and `Object.prototype` own no numeric key
([trust surface](DESIGN.md#trust-surface)). `elemAny` would read the store
alone, which answers `undefined` where the array owns such a key.

A string owns its `length` and its code units ([semantics](SEMANTICS.md#operational-language),
"Strings"). `lenStr` reads the length of an operand whose every clause is a
string, and `elemStr` a code unit at any numeric index, a string or, past the
end or at a key that is not an index, `undefined`, whatever the literal:

```math
\frac{\Gamma\vdash_G a:S\quad\mathrm{Answers}_G(S,\mathsf{isStr},\mathsf{true})\quad N\equiv_G\mathsf{num}}
     {\Gamma\vdash_G\mathsf{lenOf}\;a:N}\ \textsf{lenStr}
\qquad
\frac{\Gamma\vdash_G a:S\quad\mathrm{Answers}_G(S,\mathsf{isStr},\mathsf{true})\quad
      \Gamma\vdash_G i:I\quad\mathrm{Answers}_G(I,\mathsf{isNum},\mathsf{true})}
     {\Gamma\vdash_G\mathsf{elemAt}\;a\;i:\mathsf{str}\cup\mathsf{undefined}}\ \textsf{elemStr}
```

Any other member of a primitive is read through its wrapper's prototype. The
source read `x.k`, with `x` saved in a slot, lowers to a test of each
primitive shape its type holds, selecting that shape's read, and the object
read last (`dispatchTerm`):

```math
\mathsf{if}\ \mathsf{isStr}(x)\ \mathsf{then}\ r_{\mathsf{str}}\ \mathsf{else}\
\mathsf{if}\ \mathsf{isNum}(x)\ \mathsf{then}\ r_{\mathsf{num}}\ \mathsf{else}\ \cdots\ \mathsf{readAt}\;k\;x,
\qquad
r_s=\mathsf{readAt}\;k\;(\mathsf{makeAt}\;\mathsf{absent}\;[\mathsf{proto}]\;[P_s])
```

with $P_s$ the slot holding the realm's prototype for shape $s$, and a
string's `length` read by `lenStr`. Every arm is JavaScript's read for values
of its shape, and a value of a shape no arm names reaches the object read,
where a primitive is stuck: the lowering is faithful for every value,
whatever the claim. It is typed by existing rules only: `unionVar` splits
$x$'s labels, `ifTag` selects the arm each label's shape answers, `alloc`
types the wrapper at a record holding `[[proto]]` at the prototype's contract
and owning no other key, and `readProto` reads the member there. A method call
`s.m(a)` reads the member so and invokes it with `s` as its receiver, which
the member's signature names (`this: string`).

Every binary operator has one rule, `arith`, for arithmetic on numbers and on
bigints, for string concatenation, relational comparison and strict equality alike ([its
meaning](SEMANTICS.md#operational-language), `binop`). A clause pair
classifies the operation, $\mathrm{op}(op,c,d)$ (`opResult`), where
$\mathsf{N}$ is `num` or `numLit`, $\mathsf{Z}$ is `bigint` or `bigintLit`,
$\mathsf{S}$ is `str` or `strLit`, and $\mathsf{P}$, the printable clauses
(`printableClause`), is $\mathsf N\cup\mathsf Z\cup\mathsf S$ with `bool`,
`boolLit`, `nul` and `undef`: every primitive but a symbol. $\mathsf{Pr}$
(`primitiveClause`) is $\mathsf P$ with `symbol`, and $\mathsf{O}$
(`identityClause`) the record clauses, `refs` or `dict`, with an invariant
field: their members are objects with a field location, whose identity
strict equality compares:

```math
\mathrm{op}(op,c,d)=\begin{cases}
\mathsf{bool} & op={\equiv},\ c\in\mathsf{Pr}\cup\mathsf O\ \text{or}\ d\in\mathsf{Pr}\cup\mathsf O\\
\mathsf{bool} & op\ \text{relational},\ c,d\in\mathsf N\cup\mathsf Z\ \text{or}\ c,d\in\mathsf S\\
\mathsf{str} & op={+},\ c\in\mathsf S,\ d\in\mathsf P\ \text{or}\ c\in\mathsf P,\ d\in\mathsf S\\
\mathsf{num} & op\ \text{arithmetic},\ c,d\in\mathsf N\\
\mathsf{bigint} & op\ \text{arithmetic},\ c,d\in\mathsf Z\\
\text{none} & \text{otherwise}
\end{cases}
```

A bigint divisor, of `/` or `%`, that may be zero, or an exponent that may be negative, is
admitted: the operation then throws a `RangeError`, an outcome safety admits
([Design](DESIGN.md#throws)). $\mathrm{Operands}_G(op,A,B,r)$
requires both types of clause rows and every clause pair of $A$ and $B$ to
classify as $r$, and the result type must hold every value of the kind
($\mathrm{covers}$): the number, bigint or string family exactly, or both
Boolean literals:

```math
\frac{\Gamma\vdash_G a:A\quad\Gamma\vdash_G b:B\quad
      \mathrm{Operands}_G(op,A,B,r)\quad\mathrm{covers}_G(N,r)}
     {\Gamma\vdash_G a\mathbin{op}b:N}\ \textsf{arith}
```

The result is never a singleton, since its value is not typed. `opResult_sound`
proves the classification: on members of the two clauses $\mathsf{binop}$
answers, with a value of the kind, or $\mathsf{binopThrows}$ holds, and the
term steps to a throw (`arith_throw_safe`). So a number never meets a bigint in
arithmetic (a `TypeError`), a string is compared only with a string and
concatenated only with a primitive whose `ToString` runs no code, and a
Boolean or object operand of arithmetic or comparison, and an object or symbol
concatenated, which JavaScript would convert through code or by throwing, has
no rule, though TypeScript admits comparing two Booleans and concatenating an
object. An operand whose clauses classify differently, a `string | number`
added to a number, has none either: its result is a string or a number by the
value. The certificate premise
(`OperatorTypes`) reads $r$ off the first clause pair and checks the rest.
Strict equality answers for any pair but two objects that may lack a field (a
function, a record of optional fields only, `unknown`): those carry no identity
in the model ([its meaning](SEMANTICS.md#operational-language)), and the source
lowering refuses the comparison with that reason.

The unary numeric operators are derived: the operand's claimed type fixes its
family, all numbers or all bigints, and the operator is the binary one with a
constant right operand of that family, $-a\equiv a*(-1)$, $+a\equiv a*1$ and
$\sim a\equiv a\mathbin{\hat{}}(-1)$, each exact on both families
([semantics](SEMANTICS.md#operational-language)). $+a$ on a bigint throws a
`TypeError`, and an operand of both families has no one constant: both are
refused. The constant is its own node, typed by its literal rule; the operand's
obligation establishes the family the lowering read. A compound assignment
`x op= e` and an increment use the same rule at the target contract's type,
an increment adding that family's one; `x += e` concatenates where the
contract or `e` is a string. An increment converts its operand to a number
where `+ 1` would concatenate, so it is this addition only on a target of one
numeric family, and is refused on any other. Inside a closed expression (an
operand of `&&`, `||` or `??`, an arrow's expression body) the target is a
local cell, and the steps are the same: its read at the contract, the right
side, the operation, the write back at the contract, and the old or the new
value.

A logical assignment evaluates its target's parts once and reads the target
at its storage contract $C$; the right side runs, and is written back at $C$,
only on the arm the operator writes on, and the other arm's value is the one
read. With $r$ the target's reference, $\mathsf{read}(r)$ its read and
$\mathsf{write}(r,e)$ the write of $e$'s value, which is the expression's
value there:

```math
\begin{aligned}
r\ \mathtt{??=}\ e&\equiv\mathsf{let}\ v=\mathsf{read}(r)\ \mathsf{in}\ \mathsf{if}\ (v\equiv\mathsf{null}\lor v\equiv\mathsf{undefined})\ \mathsf{then}\ \mathsf{write}(r,e)\ \mathsf{else}\ v\\
r\ \mathtt{||=}\ e&\equiv\mathsf{let}\ v=\mathsf{read}(r)\ \mathsf{in}\ \mathsf{if}\ v\ \mathsf{then}\ v\ \mathsf{else}\ \mathsf{write}(r,e)\\
r\ \mathtt{\&\&=}\ e&\equiv\mathsf{let}\ v=\mathsf{read}(r)\ \mathsf{in}\ \mathsf{if}\ v\ \mathsf{then}\ \mathsf{write}(r,e)\ \mathsf{else}\ v
\end{aligned}
```

so $e$ is checked at $C$, as any write of $r$ is. `||=` and `&&=` are
lowered on a Boolean target only ([model limits](DESIGN.md#model-limits)).
The encoding is in [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md#receivers).

A template literal is the concatenation of its parts, in order, starting from
its first string part: `` `h${a}m${b}t` `` is $(((h+a)+m)+b)+t$, one `arith`
node per `+`, so a substitution is converted by $\mathsf{str}$ exactly where
the template converts it, after the ones before it, and one of an object or a
symbol has no rule. A template without substitutions is its string.

The comma operator $a,b$ evaluates $a$, discards its value and yields $b$'s;
`void e` is $e,\mathtt{undefined}$. The lowering binds $a$'s value in an
unread slot, and the claim at the comma is proved from $b$'s value, as a
cast's is from its operand's: no rule of its own.

A tag test
whose answer the operand's type does not settle is typed by `test` as a Boolean
holding both literals, so `ifBool` can branch on it; a settled answer still
uses `ifTag`.

For branching, $\mathrm{Answers}_G(A,k,q)$ checks that every expanded
clause of $A$ gives the same known Boolean answer $q$ to test $k$, and that
$A$ is of clause rows, since a parameter row's members could be anything:

```math
\mathrm{Answers}_G(A,k,q)\iff
\forall i\in A.\;\mathsf{plain}_G(i)\ \land\
\forall\gamma\in\mathrm{expand}_G(A).\;\mathrm{tag}(k,\gamma)=q.
```

A shape test's answer on a clause is read off its shape: $\mathsf{isBigint}$
and $\mathsf{isSymbol}$ answer true exactly on the $\mathsf{bigint}$ and
$\mathsf{symbol}$ clauses, and $\mathsf{isFun}$ answers true on an arrow, a
callable and a construct-signature clause alike, since `typeof` reports a
class as a function. $\mathsf{truthy}$ answers false on the $\mathsf{null}$
and $\mathsf{undefined}$ clauses and true on every object, function, class,
symbol and store clause; on a Boolean, number, string or bigint singleton it
answers the singleton's `ToBoolean`, and on the broad $\mathsf{bool}$,
$\mathsf{num}$, $\mathsf{str}$ and $\mathsf{bigint}$ clauses it has no fixed
answer. $\mathsf{typeofObject}$, `typeof` answering `"object"`, answers true
on the $\mathsf{null}$ clause and on a plain-object clause (a record, a
dictionary, an array) and false on every other clause but $\mathsf{top}$: an
arrow, callable or construct-signature clause is a function to `typeof`. The
key test $\mathsf{hasKey}(\kappa)$, `in`, answers on a record or dictionary
clause by its keys (`keyAnswer`): true where the clause says its object owns
$\kappa$; false where a key bound excludes $\kappa$, as a fresh literal's does;
and nothing on an open record, which may own any other key. It has no answer
on the other object clauses (an arrow, a callable, a class value) and answers
false on a primitive one, which owns no key. $\mathsf{isArray}$,
`Array.isArray`, is the same answer for the store key $\sigma$ on a record or
dictionary clause (`arrayAnswer`), true where the clause says its object owns
$\sigma$, as every array type's does, and false on every other clause but
$\mathsf{top}$:

```math
\mathrm{keys}(\kappa,\gamma)=
\begin{cases}
\mathsf{true} & \kappa\in\mathrm{present}(\gamma)\\
\mathsf{false} & \kappa\notin\mathrm{present}(\gamma),\ \exists K\in\mathrm{bounds}(\gamma).\ \neg K\ \text{admits}\ \kappa\\
\text{none} & \text{otherwise}
\end{cases}
\qquad
\mathrm{tag}(\mathsf{isArray},\gamma)=
\begin{cases}
\mathrm{keys}(\sigma,\gamma) & \gamma\ \text{a record or dictionary clause}\\
\mathsf{false} & \text{otherwise},\ \gamma\neq\mathsf{top}
\end{cases}
```

```math
\mathrm{tag}(\mathsf{hasKey}(\kappa),\gamma)=
\begin{cases}
\mathrm{keys}(\kappa,\gamma) & \gamma\ \text{a record or dictionary clause}\\
\text{none} & \gamma\ \text{an arrow, callable or construct-signature clause}\\
\mathsf{false} & \text{otherwise},\ \gamma\neq\mathsf{top}
\end{cases}
```

`keyAnswer_sound` gives each answer from the clause's meaning: a present key
is owned (`semWithArgs_owns`), and a bound's excluded key is not
(`ownKeysT_lookup`).

Other shape
tests have an answer determined by the clause's shape; numeric singleton
equality also examines its bits. A broad number clause has no fixed answer
to that equality, so it establishes neither outcome:

```math
\frac{\Gamma(x)=A\quad\mathrm{Answers}_G(A,k,q)
      \quad(q=\mathsf{true}\Rightarrow\Gamma\vdash_G t_1:B)
      \quad(q=\mathsf{false}\Rightarrow\Gamma\vdash_G t_2:B)}
     {\Gamma\vdash_G\mathsf{if}\ k(x)\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:B}.
```

The shape-test rule checks each overload body under its own argument type. It
handles shape dispatch between overloads.

Ordinary Boolean conditionals use a separate rule. Define
$\mathrm{Boolean}_G(C)$ as
$\mathrm{Answers}_G(C,\mathsf{isBool},\mathsf{true})$; this accepts Boolean
singleton unions as well as the Boolean clause.

```math
\frac{\Gamma\vdash_G c:C\quad\mathrm{Boolean}_G(C)
      \quad\Gamma\vdash_G t_1:A\quad\Gamma\vdash_G t_2:A}
     {\Gamma\vdash_G\mathsf{if}\ c\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
```

A condition with a proved singleton type needs only its reachable arm. For
$q\in\{\mathsf{true},\mathsf{false}\}$, write $B_q$ for a type represented by
$\mathsf{boolLit}(q)$, and let $t_q$ select the arm that $q$ reaches:

```math
\frac{\Gamma\vdash_G c:B_q\qquad\Gamma\vdash_G t_q:A}
     {\Gamma\vdash_G\mathsf{if}\ c\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
```

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

```math
\frac{\Gamma(x)=C\quad\mathrm{Boolean}_G(C)
      \quad\Gamma[x:=\mathsf{True}]\vdash_G t_1:A
      \quad\Gamma[x:=\mathsf{False}]\vdash_G t_2:A}
     {\Gamma\vdash_G\mathsf{if}\ x\ \mathsf{then}\ t_1\ \mathsf{else}\ t_2:A}.
```

Here $\mathsf{True}$ and $\mathsf{False}$ must expand to the corresponding singleton
clauses. `HasTyUsing.ifBoolVar` proves this rule sound: the selected branch's actual
value justifies the changed binding, and all others retain their meanings.
It neither refines mutable heap contents nor supplies general union splitting.
Graph edges use the common [observation-based refinement contract](#refinement-under-an-observed-outcome)
below, currently connected to Boolean dispatch.

### Eliminating a variable's union type

A finite union can be split in one immutable binding. Write $[a]$ for
one graph label viewed as a type. Every member must establish the same term and
result; all other bindings retain their original types:

```math
\frac{\Gamma(x)=C\qquad
      \forall a\in C.\;\Gamma[x:=[a]]\vdash_G t:A}
     {\Gamma\vdash_G t:A}.
```

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

A method call on a union receiver whose alternatives read different members
is split on its receiver the same way. With the object $x$ and the actuals
$\vec y$ already in slots, the source call `x.k(y…)` lowers to one term that
reads the member and invokes it, dispatched as a member read is
(`dispatchCallTerm`, over `dispatchTerm`'s tests):

```math
\mathsf{if}\ \mathsf{isStr}(x)\ \mathsf{then}\ \mathsf{invoke}\;r_{\mathsf{str}}\;x\;\vec y\ \mathsf{else}\ \cdots\
\mathsf{invoke}\;o\;x\;\vec y,
\qquad
o=\begin{cases}
\mathsf{let}\ m=\mathsf{readAt}\;k\;x\ \mathsf{in}\ \mathsf{bound}(m,x) & \text{every object alternative holds $k$ as a member}\\
\mathsf{readAt}\;k\;x & \text{otherwise}
\end{cases}
```

with $r_s$ a primitive shape's read through its wrapper. `unionVar` splits
$x$, `ifTag` selects the arm, and each arm is an ordinary call (`app`, with
`bindMember` for an object's member): nothing but the existing rules. The
member is read after the actuals, where JavaScript reads it before them; the
lowering is used only where no actual runs code (each a name or a literal),
so no step can tell the orders apart.

### Binding and soundness

[Bindings.lean](lean/Verification/Model/Semantics/Bindings.lean) defines de Bruijn scope and simultaneous closing substitution, and proves
its application law:

```math
\mathsf{invoke}(\mathsf{obj}(\ell,\mathsf{closure}(1,\mathrm{close}^{2}_{\rho}(b))),r,[a])
\longrightarrow \mathrm{close}_{r::a::\rho}(b).
```

The formal statement is `instantiate_beta`; environment entries must be closed.
This is the invocation step for an already allocated function object;
creation is a separate step. The same substitution law applies to `letE`.
Arrow membership requires an object with closed callable code, so every value in a
positive graph type is both a value and closed (`meaning_value`). Semantic
environments retain these properties when extended, when their world grows,
and when their observation budget decreases.

`HasTyUsing.sound` proves, for every proved image checker:

```math
\Gamma\vdash_G t:A\ \land\ \mathrm{EnvOk}_G(\Gamma,\rho,n,W)\ \land\
\mathrm{WorldAdm}(W)\ \land\ \mathrm{HeapOk}(n,W,h)
\ \Longrightarrow\
\mathrm{Safe}(⟦A⟧_G,n,W,h,\mathrm{close}_{\rho}(t)).
```

`HasTyUsing.closed_safe` specializes this to a closed program with an empty typing
environment. It explicitly requires the term to be scoped: the total semantic environment
must not silently supply meanings for unbound source variables. Safety is partial
correctness and absence of stuck execution, not termination.

The general evaluation-context lemma `bind` composes computations across heap
changes and future worlds. The typing theorem is an induction on derivations;
none of its constructor rules has a semantic safety premise.

### Integration example

The rules type a program equivalent to:

```text
let r = alloc true;
let f = x => if isNull x then read r else null;
let alias = r;
write alias false;
f(true);
f(null)
```

One closure has both `Null → Bool` and `Bool → Null`. Before the final call,
subsumption widens that overload to `(Null | Bool) → (Null | Bool)` by
splitting the union domain.

### Executable program evidence

[ProgramCertificates.lean](lean/Verification/Model/Programs/ProgramCertificates.lean) checks finite evidence trees. Each node contains a
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

```math
\mathrm{Scoped}(0,t) \land ([] \vdash_G t : A)
\quad\Longleftrightarrow\quad
\exists p.\; \mathrm{check}(G,t,A,p)=\mathsf{true}.
```

In words: the program is closed and has a typing derivation exactly when some
finite evidence is accepted for that program and result type.

This is `derivable_iff_checked`: completeness for the declared typing rules,
including checked subsumption. It neither asserts completeness for semantic
membership nor supplies proof search. `accepted_safe` derives computation safety
directly from acceptance. Checker recursion follows the finite evidence tree;
there is no user-supplied fuel and no semantic level in the evidence.

The checker is `checkUsing G images`, stated once for every proved image
checker, and `check` is its specialization to the finite one. Both directions
hold at each checker: `derivableUsing_iff_checked` relates it to
`HasTyUsing G images`, and `acceptedUsing_safe` derives safety from its
acceptance. The image checker is chosen by Lean code; evidence cannot name one.

The explicit sequents keep this initial in-memory format easy to inspect, at the
cost of repeating terms and contexts. This is not a commitment to a serialized
format. The in-memory producer below uses this interface; a decoder or compact
representation can be developed against it.

## Control flow

A finite graph over those expressions: one term per node, an edge discipline
that transfers bindings, and a certificate that checks every node and edge.

Every checker in this section takes a proved image checker, as `checkUsing`
does: edges (`checkEdgeUsing`, `checkMappedUsing`), branch edges
(`checkObservedUsing`), node steps (`checkStepUsing`), graphs and entries
(`checkGraphUsing`, `checkEntryUsing`), graph-code tables (`checkCodesUsing`)
and acceptance (`CertificateProducer.acceptUsing`), as do the evidence
producers. Names without the suffix are the finite specializations source
acceptance uses. Coverage and point assertions are semantic, family inclusion
and `EnvOk`, so each soundness theorem, parametricity (`accept_reassign`,
`accepted_at`) included, holds for every proved image checker.

### Supplied point claims and incoming edges

[PointClaims.lean](lean/Verification/Model/Programs/PointClaims.lean) checks supplied type environments. Write $\Gamma \preceq_G \Delta$
when every slot in the target claim $\Delta$ has a source slot at the same
position in the incoming environment $\Gamma$, with a proved subtype relation:

```math
\Gamma \preceq_G \Delta
\quad\Longleftrightarrow\quad
|\Delta| \leq |\Gamma|
\;\land\;
\forall i < |\Delta|.\; \Gamma_i \leq_G \Delta_i.
```

`checkEdge` takes one subtype certificate per target slot. Lean proves that
acceptance implies coverage, as family inclusion per slot (`Covers`,
`checkEdge_sound`). Coverage also transfers semantic
environments: any concrete environment meeting $\Gamma$ meets $\Delta$, with
closed values preserved.

`checkEdge` is the position-preserving specialization: it can widen types and
forget a suffix. `checkMapped` additionally checks an explicit list of source
indices, with exactly one index and subtype certificate per target slot.
Repeated indices retain aliases, and an interior binding can be dropped.
Every selected source index must exist; no missing binding acquires a type from
the total environment's default value.

For a supplied map $m$, the rule and its semantic action are:

```math
\frac{
  |m|=|\Delta|
  \qquad
  \forall i<|\Delta|.\;m_i<|\Gamma|\;\land\;\Gamma_{m_i}\leq_G\Delta_i
}{
  \Gamma\preceq_G^{m}\Delta
}
\qquad
\mathrm{mapEnv}(m,\rho)(i)=\rho(m_i).
```

`checkMapped_sound` proves mapped coverage, and `MappedCovers.env` proves that
this simultaneous selection preserves the target semantic environment in the
same world. It does not copy or change heap contents. The absent map means
identity selection, retaining the earlier edge interface.

`checkIncoming` checks each supplied predecessor against the supplied target
claim independently. No join is computed. When a computation binds a new result,
`checked_bind_claim` proves composition through the edge
$A :: \Gamma \preceq_G \Delta$ into a continuation checked under $\Delta$:

```math
\frac{
  \Gamma \vdash_G a : A
  \qquad A :: \Gamma \preceq_G \Delta
  \qquad \Delta \vdash_G b : B
}{
  \mathrm{Safe}\!\left(
    ⟦B⟧_G,n,W,h,
    \mathrm{close}_{\rho}
      (\mathsf{let}\;x=a\;\mathsf{in}\;b)
  \right)
}.
```

The conclusion assumes that $\rho$ meets $\Gamma$ at budget $n$ and world $W$,
that $W$ is admissible, and that $h$ satisfies $W$. This is a semantic composition
theorem with checked evidence at both ends; its proof accommodates heap changes
and world extension.

These are local obligations. `checkIncoming` checks the edges it is given;
it does not establish that they enumerate a graph's actual predecessors.
The graph checker below discharges that enumeration obligation.

### Throwing

`throw a` has every type: it never produces a value, and a throw is an
outcome safety admits ([Design](DESIGN.md#throws)). Its operand is typed at a
type of its own, since it runs first:

```math
\frac{\Gamma\vdash_G a:A}{\Gamma\vdash_G\mathsf{throw}\ a:B}\ \textsf{throw}
```

The soundness case composes `a`'s safety with the throw's context rule
(`bind` over `Tm.throw`) and closes with `thrown_safe`: the value `a` produces
is closed, as every member of a type is (`meaning_value`). Evidence names the
rule `throw` with the operand's derivation as its one premise; the producer
types a slot operand at the slot's type.

### Allocation from parts

[ObjectMerge.lean](lean/Verification/Model/Programs/ObjectMerge.lean) states and proves what a merge's result holds, clause by clause.

$\mathsf{merge}_\delta(a,b)$ allocates the fields $a$'s object owns and, over
them, the own enumerable data properties $b$ has, less $\delta$
([SEMANTICS](SEMANTICS.md#operational-language)). Its type is a record every
pair of the operands' clauses gives ([Design](DESIGN.md#object-literals)):

```math
\frac{\Gamma\vdash_G a:A\quad\Gamma\vdash_G b:B\quad
      \mathrm{MergeOk}_G(\delta,A,B,R)}
     {\Gamma\vdash_G\mathsf{merge}_\delta(a,b):R}\ \textsf{merge}
```

$\mathrm{MergeOk}_G(\delta,A,B,R)$ holds where $A$ and $B$ are of clause
rows and, for each clause $c_a$ of $A$ and $c_b$ of $B$, some clause
$\mathsf{Ref}(\varphi;\omega;\beta)$ of $R$ is given by them
(`ObjectMerge.MergeClause`): $c_a$ a record or dictionary, $c_b$ one too, a
function clause (a function, or a callable object, whose own enumerable
properties are the fields its bag states and whatever else was assigned to
it, so it states no bound; `codeOf`), or a
clause of values owning no enumerable property (`null`, `undefined`,
Booleans, numbers, bigints, symbols); each field $(k{:}T)\in\varphi$ surely
given within $T$ by $c_b$, or by $c_a$ where whatever $c_b$ gives under $k$ is
within $T$; each optional field within its type on both sides, and then $c_a$
holding no prototype; each bound of $\beta$ admitting every key either side
may give (`FieldsOk`). "Within" is label inclusion, whose meaning is a
union's.

The result may instead be a dictionary
$\mathsf{Dict}(\varphi;\iota;\omega;\beta;\chi)$, of index views $\iota$ and
writable indexes $\chi$ beside the same fields, optional fields and bounds
(`DictOk`): every entry of $\iota\mathbin{+\!\!+}\chi$ is at one type $V$;
$c_a$ holds no prototype ($\neg\pi$ among its keys, by a bound or by an index
of its own, which `dictViewT` states); and for each class $K$ of an entry,
whatever either side gives under a key $K$ admits is within $V$:

```math
\mathrm{given}_K(c,V)\iff
  \forall (k{:}T)\in\varphi_c\cup\omega_c.\ K\ \text{may admit}\ k\Rightarrow T\subseteq V
  \ \land\ \big(\exists (K'{:}T')\in\iota_c.\ K\subseteq K'\land T'\subseteq V
  \ \lor\ \exists\,\mathsf{among}\,N\in\beta_c.\ \forall k\in N.\ K\ \text{may admit}\ k\Rightarrow k\in\mathrm{dom}(\varphi_c\cup\omega_c)\big)
```

($\mathrm{given}_K(c_a,V)$ is `classWithinA`). For the source it is
`classWithin`, over the keys a copy takes, less $\delta$, and also no array
store whose elements a copy would give under index keys: a bound excluding the
store key, or a string index at a type no member of which is a list
(`noStore`, since the store key `[]` is a string), unless $K$ is the symbol
class, which admits no key a copy gives. A field or optional field of the
result whose key a class may admit is within $V$, and exactly $V$ where a
writable index's class may admit it, whose locations hold exactly $V$; and
each bound of a result with a writable index keeps that index's class
($b\ \mathsf{keeps}\ K$, [covering](POSITIVE-TYPES.md#records)): none lists
keys or excludes one the class may admit, which the keys outside code may add
under the index would contradict. The
soundness case evaluates the operands with `bind`, as `arith` does, and
closes with `ObjectMerge.merge_values_safe`, which takes the merge's step,
then the allocation's by `make_fields_rule`, giving each location the
contract its result key states, $V$ for a key an index's class admits, or its
copied value for a key the result does not state. Evidence names the rule
`merge` with the two operands' derivations; the search types a slot operand
at the slot's type and tries the requested type, then the pool's, for the
result, coercing; extraction proposes the clauses (`ObjectMerge.mergeResult`:
where a side states an index, the dictionary over the sides' classes at the
union of their index types and the admitted fields' types, if the rule
admits it, else the record) and states them as hints. The last merge of an
object literal is at the literal's claim where the rule admits it: each pair
of clauses may give a record of the claim's own, so a field written after a
spread is allocated at the type of the arm each pair gives, as TypeScript
types the literal per arm of the contextual union.

For heap knowledge a merge is an allocation, as a literal is
(`HeapExpressionRules.merge_alloc_sound`): it reads the heap and writes no
old location, so every fact survives, and its fresh object's fields, under
whatever keys, are distinct from every field a record-typed slot names.

### Key-adding writes

A source write that adds a key is the copy of the object with the key,
rebound to the local that held it: the statement $x.k = e$ (or $x[\text{"}k\text{"}] = e$)
where some plain-object clause of $x$'s claimed type states $k$ neither as a
field, a view nor a method, nor as a readonly optional field (`mayLack`),
lowers, when $x$ **owns** its object at the statement, to

```math
x;\ e;\ o\leftarrow\mathsf{makeAt}(\{k\mapsto v\});\ x\leftarrow\mathsf{merge}_{[]}(x,o)
```

with the value of $e$ at the claim of the write expression $W$, the one-key
object at $\mathsf{Ref}(k{:}W;\ \mathsf{among}\,\{k\})$ and the merge at the
record or dictionary `mergeResult` proposes, checked by
[$\textsf{merge}$](#allocation-from-parts); the last node's slot map puts the
merge's value in $x$'s slot. The value of the assignment is discarded: only a
statement is lowered so. Ownership (`growSites`) is syntactic:

```math
\mathrm{Own}(x,s)\iff
  \begin{cases}
  x\ \text{is declared}\ \mathtt{const}\ x = o\ \text{with}\ o\ \text{an object literal, not at module level;}\\
  s\ \text{is at the loop depth of the declaration, in the same body;}\\
  \text{no statement from the declaration through}\ s\ \text{lets}\ x\ \text{escape.}
  \end{cases}
```

An expression lets $x$ escape (`escapesExpr`) when $x$ occurs in it other
than as the receiver of a member read, index read, write, index write, `in`
test, compound or logical assignment: in a call's arguments or as a method
call's receiver, in a binding's or field's value, a result, a spread, a
comparison, and anywhere in a closure, which holds the object. In textual
order every path from the declaration to $s$ passes only earlier statements,
since $s$ is in no loop the declaration is outside; a module constant is read
by the module's functions. With $\mathrm{Own}(x,s)$ no reference but
$x$'s slot holds the object, so JavaScript's write in place, which every
reference would see, and the copy, which only $x$ sees, agree. Any other
write adding a key is refused, located at the write, as is a write of
`__proto__` (a setter) or a symbol key (the copy takes string keys). A write
at a key known only at run time is refused on an object another reference
may hold; on an owned one, at a string, which may spell `[]` or `[[proto]]`,
keys the model keeps for itself; at a number or symbol it is not lowered.

`Object.assign(t, s_1, …, s_n)` copies each source onto its target as a
spread copies, one $\mathsf{merge}_{[]}$ per source as soon as it is
evaluated, checked by $\textsf{merge}$. Its target is a fresh literal, whose
result is the call's value; or, for the statement `Object.assign(x, …);`
with $\mathrm{Own}(x,s)$, the local, which holds the result from then
on, as for a key-adding write (a source letting $x$ escape defeats
ownership). Any other target is refused: the call's value is the target, one
more reference to it. JavaScript sets each key through the target's `[[Set]]`,
where a spread defines it: the two agree on a fresh plain object, but for
`__proto__`, whose setter replaces the prototype. So each source's claimed
type must give no `__proto__` (`ownsNoProto`: every clause owns no
enumerable property, or a key bound excludes the key); a record type, which
may own any key, is refused. As for a spread, the model's copy takes string
keys only ([DESIGN](DESIGN.md#object-literals)).

### Checked control-flow graphs

[ControlFlow.lean](lean/Verification/Model/Programs/ControlFlow.lean) adds a finite control-flow graph over the existing expression
language. A program is a finite list of nodes indexed by label; each node is one
[term](SEMANTICS.md#operational-language), one of these six continuations,
and an optional handler (below):

| Continuation            | Action after evaluating the expression                                                                                              |
| ----------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| `ret`                   | Return its value as the graph's declared result type.                                                                               |
| `bind` to a target      | Push the value, apply the target slot map, and enter its label.                                                                     |
| `effect`, then a target | Discard the value, apply the target slot map, and enter its label.                                                                  |
| `branch`                | Select a target according to the Boolean value and apply its slot map.                                                              |
| `branchBind`            | Select a target, push the tested Boolean, and apply its slot map with a singleton refinement.                                       |
| `tagBind`               | Test the returned value's shape, select a target, push that value, and apply its slot map with the refinement the answer justifies. |

Conditionals therefore exist at two levels: `if` inside a single node's term, and
these branch continuations between nodes. Source lowering uses the continuations
for statement control flow, in function and closure bodies alike, and the term
form inside direct proofs. It emits every continuation except plain `branch`, which remains
available to graphs written against the protocol directly.

A target contains its label and an optional slot map. These are executable
program data, shared by the machine and checker; evidence cannot supply a
different binding transfer. Numeric targets abbreviate an identity map. A bind
or `branchBind` map indexes the environment **after** pushing the result; effect
and ordinary branch maps index the unchanged incoming environment.

A node's **handler** is a target too: where a throw out of its expression
goes, the thrown value pushed as a `bind` pushes a value. A node without one
lets the throw end the run, in the state $\mathsf{raised}(v)$. The machine:

```math
\frac{h,t\ \text{raises}\ v}{h,\ \mathsf{eval}(t,\rho,k,\ell)\to h,\ \mathsf{at}(\ell,\mathsf{push}(v,\rho))}\ (\texttt{handle})
\qquad
\frac{h,t\ \text{raises}\ v}{h,\ \mathsf{eval}(t,\rho,k,\varnothing)\to h,\ \mathsf{raised}(v)}\ (\texttt{raise})
```

Node evidence for a node with a handler supplies the type $T$ the thrown value
is bound at and the handler edge's certificate. `checkHandler` requires $T$ to
admit every value, one of its clauses being top (`admitsAll`), and the edge to
check against the target's claims under the facts that hold wherever the
expression throws, which are those of the node's entry that do not mention the
heap (`handlerFacts`: immutable values, alias and distinct links, shifted past
the thrown value's slot):

```math
\frac{\mathsf{top}\in\mathrm{expand}_G(T)\quad
      \mathrm{TargetOk}_G(C,\ T{:}\Gamma,\ \ell,\ \mathrm{handlerFacts}(K))}
     {\mathrm{HandlerOk}_G(C,\Gamma,K,\ell)}\ \textsf{handler}
```

where $\Gamma$ and $K$ are the node's entry claims and facts. The machine
state after a throw is safe by that edge, `admitsAll_sound` giving the thrown
value its type, and `handlerFacts_holds` its facts at any heap.

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

```math
\begin{gathered}
\mathrm{checkEntry}(G,R,P,C,p,\Gamma_0)=\mathsf{true}
\\
\land\;\mathrm{EnvOk}_G(\Gamma_0,\rho,n,W)
\land\;\mathrm{WorldAdm}(W)
\land\;\mathrm{HeapOk}(n,W,h)
\\
\Longrightarrow\quad
\mathrm{SafeGraph}_P(⟦R⟧_G,n,W,h,\mathrm{at}(p,\rho)).
\end{gathered}
```

[`SafeGraph` and the machine state $\mathrm{at}(p,\rho)$](SEMANTICS.md#computations-and-recursive-types)
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

`Transition.det` proves determinism of this combined machine, a throw
included (`Raises_det`).
`accepted_no_stuck` proves that after any finite actual execution, the machine
has returned a typed value, ended by a throw of a closed value, or can take
another step. `accepted_result` proves
that any returned value meets the declared result type at every positive
remaining budget, in an admissible world satisfied by the final heap. These
are safety and partial-correctness theorems, not termination guarantees.

The graph layer does not change the type-family or expression semantics. A
closure body is a graph as a function body is, run by its own steps
([graph code](SEMANTICS.md#graph-code)) and typed by `funGraph`. Boolean result refinement is proved as described below. A primitive fragment with parameters
is connected; broader source extraction remains integration work. The next section supplies
an in-memory certificate producer; [REQUEST-PROTOCOL.md](REQUEST-PROTOCOL.md)
describes its serialized consumer boundary. No graph-level completeness theorem is claimed here; the
program-evidence and edge-evidence completeness results above retain their
stated scope.

#### Refinement under an observed outcome

[BranchRefinement.lean](lean/Verification/Model/Programs/BranchRefinement.lean) uses one contract for Boolean equality and tag observations.
An observation $o$
is either equality to a Boolean value or the result of a runtime tag test.
Define the semantic obligation:

```math
A\preceq_o B
\quad\Longleftrightarrow\quad
\forall n,W,v.\;
\bigl(v\in⟦A⟧_{n,W}\land o(v)\bigr)
\Longrightarrow v\in⟦B⟧_{n,W}.
```

This is `ObservedSub`. The destination type $B$ is supplied. The contract does
not require computing a canonical intersection, difference, or filtered type.
It is a semantic specification; the executable checker uses sufficient finite
checks, not a semantic oracle. No completeness of these checks is claimed.

`ObservedCovers` checks each destination slot selected by a map $m$. For the
tested slot $i$, it requires $\Gamma(i)\preceq_o\Delta(j)$; other selected slots
require ordinary subtyping, or, for a slot $k$ holding an object the tested
value was read from through field $f$ (a current read link at the dispatch,
`readFields`, or an optional one, `optionalFields`), subtyping from its field
slice $F^{f}_{t,q}(\Gamma(k))$
(`fieldSlice`): the labels of $\Gamma(k)$ but those every clause of which is a
record fixing $f$, as an invariant field or a readonly view, at a type that
answers the tag $t$ with $\lnot q$. The common environment theorem is:

```math
\frac{
 \mathrm{EnvOk}_G(\Gamma,\rho,n{+}1,W)
 \quad \mathrm{HeapOk}(n{+}1,W,h)
 \quad o(\rho(i))
 \quad \forall (k,f)\in\mathit{fs}.\ h(\rho(k).f)=\rho(i)
 \quad \mathrm{ObservedCovers}_G(\Gamma,\Delta,i,o,m,\mathit{fs})
}{
 \mathrm{EnvOk}_G(\Delta,\mathrm{mapEnv}(m,\rho),n{+}1,W)
}.
```

The field slice is sound one level up (`fieldSlice_sound`): the field's
location holds the read value, and a heap meeting the world holds at that
location a value of the field's type one level down (`field_value`), whose tag
answer is budget-independent. Through an optional link the slice is sound
too: where the object has the key the link is a read link, and an object
lacking it is of no label the slice drops, every clause of which names the
field as a field or a view, a key the object has (`fieldSlice_absent`). What
it establishes is the object's label,
which its allocation fixes; it is not a claim about what the field holds
later, so writes and calls after the test do not undo it. A discriminated
union is this: `s.kind === "circle"` keeps the arms whose `kind` admits
`"circle"`.

A slot $k$ the tested value was read from through a key $f$ it may lack (an
optional read link, `optionalFields`) is covered by a promotion instead, where
the observation rules `undefined` out (`excludesUndef`): the read then found
the key, which the object keeps from its allocation on, so its type is its
records with $f$ present (`promotes`, below). The environment theorem takes the
optional links' meaning as one more premise, $\forall(k,f)\in\mathit{os}.\
f\notin\mathrm{keys}\rho(k)\Rightarrow\rho(i)=\mathsf{undefined}$
(`ObservedCovers.env`).

An observation the tested slot's type rules out (`impossible`: a tag answer
every label of it contradicts, or a Boolean it does not hold) covers any
destination: no environment meets both, so the edge is never taken.
`checkObserved` checks slot existence, map and evidence lengths, and each of
these obligations. `checkObserved_sound` and `ObservedCovers.env` prove the
common path. The observation is established by execution, never accepted as a
producer assertion. Heap contents are not refined.

Four implementations discharge the tested-slot obligation:

- **Boolean equality:** `booleanMember` checks that the supplied destination
  contains the observed Boolean. `subset` is the canonical evidence marker for
  this check, not an ordinary subset derivation. No synthetic singleton label
  is needed.
- **Tag outcome:** `tagSlice` discards a label only if every clause contradicts
  the observation, then checks an ordinary subtype certificate from the remaining
  labels to the supplied destination. Mixed-shape labels are retained intact.
  Filtering is a conservative algorithm, not the definition of `ObservedSub`.
  Alternatively, a passed test naming one primitive family is covered by that
  family's clause in the destination, whatever the tested type, `unknown`
  included (`tagMember`, with the marker `subset`): every value `typeof`
  answers `"string"` for is a string. So is equality with one number other
  than a zero, which holds of that number alone, or with one string:
  $x\equiv 1$ with $x:\mathsf{number}$ gives $x:1$. A type parameter's
  value is covered so too: where `typeof x === "number"` holds of `x: T`,
  `x` is a `number`, which is what TypeScript's `T & number` holds, though
  no longer read as a `T`; where the test fails, `x` keeps its row, whose
  values the tag slice cannot divide. A more precise algorithm can implement
  the same contract without changing the edge or environment rule.
- **Array of the realm:** a passed `Array.isArray` finds an object owning
  the store key. A member of a record or dictionary clause meets the realm's
  [array invariant](SEMANTICS.md#the-array-invariant), so such a member is a
  member of the realm's `sparse ReadonlyArray<unknown>`: a clause row $L$ holding the
  array shape over a store of values, $P_{\mathcal R}$ and $N_{\mathcal R}$
  (`realmArrayLabel`, `realmArray_of_record`). Each label the tag slice
  keeps is kept in the destination, or is a clause row each clause of which
  answers `false` or is a record's; and the destination holds $L$
  (`arraySlice`, `arraySlice_sound`, with the marker `subset`). A label with
  `top`, and a parameter row, is no record's: `unknown` and a type parameter
  are not narrowed so:

```math
\frac{\forall a\in T_{\mathsf{isArray}}(A).\;a\in B\ \lor\ \forall c\in G(a).\;
         \mathsf{tag}(\mathsf{isArray},c)=\mathsf{false}\lor c\ \text{a record's}
       \qquad L\in B\qquad G(L)=[\mathsf{Ref}(;\sigma{:}S,\mathsf{proto}{:}P_{\mathcal R};\langle\mathsf{outside}\,N_{\mathcal R}\rangle)]}
      {A\preceq_{\mathsf{isArray}=\mathsf{true}}B}\ \textsf{tag-array}
```

  with $S$ a readonly store at a type holding `top`.

- **Present key:** a passed `in` test finds its key on the object's chain:
  its own, or, where it lacks it, one a prototype holds (`KeyFound`). An
  object of a record lacking one of its optional keys holds no prototype
  (`optT`), so there the key is its own, and an object's keys are fixed at its
  allocation: each record clause $c$ of the tested type holds with its
  optional key $k$ taken as present, $c^{+k}$ (`promote`: a writable optional
  key becomes an invariant field, a readonly one a view, as `optT` states of a
  present key). The destination needs a clause asking
  no more than that, $d\sqsubseteq c^{+k}$ (`weaker`: each operand of $d$ is
  one of $c^{+k}$'s; every part of a record clause's meaning is a statement
  about each operand) (`promotes_sound`, with the marker `subset`):

```math
\frac{\mathsf{tagHolds}(t,v)=\mathsf{true}\ \Rightarrow\ v\in⟦c⟧\quad c\in\mathrm{expand}_G(B)}
     {A\preceq_{t=\mathsf{true}}B}\ \textsf{tag-member}
\qquad t\in\{\mathsf{isStr},\mathsf{isNum},\mathsf{isBigint},\mathsf{isSymbol},\mathsf{isUndef},\mathsf{isNul},\mathsf{isBool},\mathsf{numEq}(b)_{b\neq\pm0},\mathsf{strEq}(s)\}
```

```math
\frac{v\in⟦c⟧\quad k\notin\mathrm{keys}(v)\Rightarrow v\ \text{holds a prototype}}
     {v\in⟦c^{+k}⟧}
\qquad
\frac{G\vdash A\ \text{plain}\quad
      \forall c\in\mathrm{expand}_G(F_{\mathsf{hasKey}(k),\mathsf{true}}(A)).\
      \exists d\in\mathrm{expand}_G(B).\ d\sqsubseteq c^{+k}}
     {A\preceq_{\mathsf{hasKey}(k)=\mathsf{true}}B}\ \textsf{present-key}
```

For the current primitive profile, null filtering gives:

```math
F_{\mathrm{null},\mathrm{true}}(\mathrm{null}\lor\mathrm{bool})=\mathrm{null},
\qquad
F_{\mathrm{null},\mathrm{false}}(\mathrm{null}\lor\mathrm{bool})=\mathrm{bool}.
```

A regression also proves a semantic refinement of a mixed label that the current
filtering checker cannot establish. This records the precision boundary explicitly.
A Boolean shape test does not establish equality to `true`; these observations
have separate tests to prevent conflation.

A graph point whose entry claims a binding of the empty type is unreachable:
every incoming edge establishes that claim, which no value meets. Proof search
derives any sequent there by `unionVar` on the empty slot, which has no
premise, and a jump whose entry is so claimed completes the function rather
than continuing (the exhaustive `switch` below falls off no end).

The existing `branchBind` dispatch now uses this common checker and environment
theorem with a Boolean observation of the actual pushed value. Its all-budget
safety and deterministic execution proofs still apply, including cyclic graphs.
The source compiler maps a tested immutable Boolean variable to that pushed
value and preserves the other slot identities. Negations swap branch polarity.

The `tagBind` continuation tests the actual returned value, pushes that value,
and selects the matching edge. Its schematic rule is:

```math
\frac{\Gamma\vdash_G t:A
\quad\mathrm{ObservedCovers}_G(A::\Gamma,\Delta_y,0,\mathrm{tag}(k,\mathsf{true}),m_y)
\quad\mathrm{ObservedCovers}_G(A::\Gamma,\Delta_n,0,\mathrm{tag}(k,\mathsf{false}),m_n)}
{\mathrm{NodeOk}_G(\Gamma,t,\mathrm{tagBind}(k;y,m_y;n,m_n))}.
```

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

[ExecutionModelTests.lean](lean/Verification/Model/Tests/ExecutionModelTests.lean) shows the model's `in` finding a key on the prototype chain, which an
instance does not own.

#### Statement forms as graphs

The [statement forms](#statement-forms) add no node
kind, continuation or rule; each is a shape of ordinary nodes and edges.

- A loop with an update: the body's end and each `continue` edge go to the
  update's first node, whose edge goes to the head. Every edge into the head is
  checked against its cut as before; the update is checked once, from its own
  statement claim.
- A labeled block: `break ℓ` is an administrative null node whose mapped edge
  goes to the statement after the block labeled $\ell$, dropping the slots
  the block introduced, exactly as a loop's `break` goes to its exit. A block
  adds no node of its own.
- `throw e`: `e`'s nodes, then one node `throw x` returning, at the result
  type, which the `throw` rule gives it.
- `try`: every node of the body that may throw (not a slot or a value) names
  the handler's entry as its handler, the thrown value landing in the catch
  binding's slot and the `try`'s scope kept; the handler's nodes name the
  `finally` block's throw-path entry, or the enclosing handler. The `finally`
  block is compiled once per way out ([statement forms](#statement-forms)): after a
  normal completion, before each `return` in the body or handler with the
  value held in a slot of its own, before each `break` or `continue` that
  leaves the `try` (every `finally` the jump passes, innermost first, the
  outermost completing into the jump's target), and after a throw with the thrown value
  held, ending in a node that throws it again. Where neither the body nor the
  handler can complete, the normal way leads to an unreachable node that
  loops on itself and states nothing.
- A closing region (the [iterator protocol](#the-iterator-protocol)'s
  IteratorClose): the body's nodes name, as their handler, the close's entry
  under a handler that drops the close's own throws, followed by a node that
  throws the held value again; the loop's `break` goes to the close's entry
  followed by the loop's exit, and each `return` passes it as a `finally`.
- A declaration hiding an outer binding of its name adds no node: the parser
  has given it a name of its own ([shadowing](#derived-source-forms)), so
  the lowering never meets two bindings of one name.

[LoweringTraceTests.lean](lean/Verification/Model/Tests/LoweringTraceTests.lean) runs lowered loops: a `while` loop's back edge drops the alias local
and keeps the closure and cell in place, `break` reaches the nearest loop's
exit, and `continue` retests the condition after the body's write.

## State

What is known about the heap and the environment as execution proceeds, layered
over both of the above: expression typing decides whether an operation is
admitted, the graph decides where its knowledge travels, and these rules decide
what it establishes.

### Current-content rules (semantic layer)

The finite [type and assertion syntax](POSITIVE-TYPES.md#state-assertion-grammar)
is defined alongside the ordinary type grammar. This section owns its rules.

These rules are proved in [HeapObservations.lean](lean/Verification/Model/Semantics/HeapObservations.lean)
and, for finite current-content assertions, in [HeapFacts.lean](lean/Verification/Model/Semantics/HeapFacts.lean).
[HeapExpressionRules.lean](lean/Verification/Model/Programs/HeapExpressionRules.lean) checks finite expression evidence against them.
They are not additional `HasTy`
constructors. The maintained graph checker now accepts the checked effect forms;
the source adapter binds supplied observations to checked graph checkpoints.
The producer can also derive facts through supported operations.
The [semantic reference](SEMANTICS.md#current-content-assertions-and-postconditions)
defines `Obs`, `ObservedRef`, and `SafePost`; ordinary immutable-value branch
observations above must not be confused with these mutable-heap assertions.

All rules below assume an admissible world and satisfying initial heap. Write
$\widehat R(n,W,v)=R(v)$ for a heap-independent content predicate, and require
$R(v)$ to imply that $v$ is a value. The observed-read rule is:

```math
\frac{\mathrm{Obs}(h,\ell,R)}
 {\mathrm{SafePost}(\widehat R,Q,n,W,h,\mathsf{read}(\ell))},
\qquad Q(h',v)\equiv h'=h\land h'(\ell)=v.
```

`read_contents` proves this: its result type gives $R(v)$, and its postcondition
preserves the entire heap, hence other observations. For a value $v$ permitted by
the invariant $B$, the write rule is:

```math
\frac{\mathrm{Ref}(B)(n,W,\ell)\quad B(n,W,v)\quad\mathrm{isVal}(v)}
 {\mathrm{SafePost}(\mathsf{Null},Q,n,W,h,\mathsf{write}(\ell,v))},
\qquad Q(h',u)\equiv h'=h[\ell:=v]\land u=\mathsf{null}.
```

`write_observed` requires `Adm B`. It needs no old-content premise. `write_new`
establishes the new observation; `write_frame` preserves a fact at another
location only with proved runtime inequality. A write through an alias has the
same effect. Allocation uses `alloc_observed` to return an invariant reference
and the exact appended heap; `alloc_new` and `alloc_frame` give the fresh fact and
preservation of existing facts.

| Rule              | Premise and consequence                                                                                                                                                          |
| ----------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `test_refines`    | A current lookup links the tested value to the cell; a predicate on that value then refines current contents. An old snapshot alone does not suffice.                            |
| `call_forget`     | Ordinary arrow membership supplies result safety and heap-invariant preservation, with postcondition `True`. It supplies no retained observation.                                |
| `bind`            | For an evaluation context that lifts steps, its continuation receives the actual resulting heap, value membership and postcondition in the future world at the remaining budget. |
| `consequence`     | Implication weakens the result family and postcondition.                                                                                                                         |
| `write_then_read` | Composing write, bind, beta and read proves that the immediate subsequent read returns the written value; there is no ownership or non-escape premise.                           |

The finite assertion layer represents a fact as a slot $i$, a field name and
an $R$ from the [primitive predicate grammar](POSITIVE-TYPES.md#state-assertion-grammar).
Write $v\in R$ for satisfying one of those predicates. In the one-field
abbreviation its meaning is:

```math
\mathrm{Holds}(\Delta,\rho,h)
\equiv \forall(i,R)\in\Delta.\;
\exists\ell,v.\ \rho(i)=\ell\land h(\ell)=v\land v\in R.
```

For a slot map $m$, the executable entailment check uses this sufficient rule:

```math
\frac{\forall(i,R)\in\Sigma'.\;\exists(j,S)\in\Sigma.\ j=m(i)\land S\subseteq R}
 {\mathrm{Holds}(\Sigma,\rho,h)\Longrightarrow
  \mathrm{Holds}(\Sigma',\mathrm{mapEnv}(m,\rho),h)}.
```

`HeapFacts.check_sound` proves it. Repeated slot mappings retain aliases; different
slots do not prove disjoint locations. `shift_holds` transports facts when a bind
pushes a result. The finite `read` rule preserves facts. `write` conservatively
drops all old facts and establishes the written value's predicate. `alloc` preserves shifted
old facts and adds the fresh cell at the result slot. These are semantic rules;
source compilation must still supply and check their graph-level use.

#### Checked expression postconditions

`Knowledge` in [HeapKnowledge.lean](lean/Verification/Model/Semantics/HeapKnowledge.lean) pairs the cell facts above with immutable slot facts
$V$, interpreted as $\forall(i,R)\in V.\;\rho(i)\in R$. This distinction is
necessary when the producer claims a wide type for a read: the ordinary type
remains unchanged, while a proved fact about the returned value can justify a
narrower subsequent return contract. Mutation invalidates cell contents and read-to-cell relationships, not
values already read into immutable slots or equalities between copied values.

The [assertion layer](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch)
splits in two. $\Pi$ is a conjunction of **value predicates** $x\in R$ and
**equalities** $x=y$ between two variables. It mentions
only the environment. $\Sigma$ is a list of points-to atoms $x.f\mapsto R$ and
$x.f\mapsto y$: the field $f$ of the object $x$ names currently satisfies
$R$, or holds the value of $y$. These facts mention the heap. Neither
relation carries ownership: $\mapsto$ here is duplicable and says nothing about
what else the heap holds.

Every atom names a field: `HeapFacts.Fact` and `HeapLinks.Link` each carry one,
and `HeapExpressionRules` reads it off the term rather than taking it from
evidence, so a certificate cannot assert a fact about a field the program never
touched. The `allocated` rule establishes one primitive-content atom per named
field whose initializer slot has a known supported predicate, and none for a
field whose initializer has none; an ordinary allocation alone makes no such
assertion. The rules below are
written in the one-field spelling, $x\mapsto R$, which is the general rule at
whichever field its term names; nothing in them is specific to a field name.

Checking an expression is then a **Hoare typing**: an ordinary typing carrying a
precondition and a postcondition. Write

```math
\Gamma;\Pi;\Sigma\vdash_G r\leftarrow t:A\dashv \Pi';\Sigma'
```

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
graph type, and $\Pi$'s primitive predicates refine that for primitives — `valuesAt`
reads a value fact when there is one and falls back to the variable's type when
there is not. What $\Pi$ adds beyond $\Gamma$ is equalities _between_ variables,
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
first: it is the primitive predicate recorded for $x$ there, or
failing that the one $\Gamma(x)$ denotes when it is a supported primitive
union, or `defined` when no member of $\Gamma(x)$ is `undefined`. It extends the $\Gamma(x)$ of the ordinary rules to the pair, is partial
in the same way, and is a lookup rather than a search — `valuesAt` computes it in
that order and `valuesAt_sound` proves the membership it yields.

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
these rules say what it then establishes. $\mathrm{Ref}A$ and
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

```math
\frac{\Gamma\vdash_G\mathrm{alloc}(x):\mathrm{Ref}A
      \qquad(\Gamma;\Pi)(x)=R}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{alloc}(x):\mathrm{Ref}A
  \dashv \Pi\;;\;\Sigma,\;r\mapsto R}
\qquad
\frac{\Gamma\vdash_G\mathrm{alloc}(x):\mathrm{Ref}A
      \qquad(\Gamma;\Pi)(x)\ \text{undefined}\qquad x\in\mathrm{dom}\Gamma}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{alloc}(x):\mathrm{Ref}A
  \dashv \Pi\;;\;\Sigma}
```

Either way the fresh cell's field is a location distinct from every contract
field of every record-typed slot (the distinct links of `allocOutput`), whether
or not its contents are known: a cell holding an object keeps what is known of
the others, and a later write to either keeps what is known of the other.

**Reading** has two rules for the same term, and neither subsumes the other.

The first applies whenever the read types and $x$'s type is a plain reference. It
claims nothing about the contents; what it records is where the result came from,
$r$ now holding what the cell $x$ names holds — which is what a later test of $r$
needs in order to refine $x$ itself.

The second applies when $\Sigma$ already holds an atom for $x$ and the result type
is primitive. It consumes that atom and returns it as an equality on the result.
It needs no typing derivation: the atom and its premise establish the result type
between them, which is why its first premise is a membership in $\Sigma$ rather
than a judgment. Writing $\mathrm{pred}(A)$ for the primitive predicates a type
denotes — defined only when $A$ is primitive, so the premise also fails for a
reference or an arrow result:

```math
\frac{\Gamma\vdash_G\mathrm{read}(x):A\qquad\Gamma(x)=\mathrm{Ref}B}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{read}(x):A
  \dashv \Pi\;;\;\Sigma,\{y\mapsto r\mid y\approx_\Pi x\}}
```

```math
\frac{(x\mapsto R)\in\Sigma\qquad R\subseteq\mathrm{pred}(A)}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{read}(x):A
  \dashv \Pi,\;r=R\;;\;
   \Sigma,\{y\mapsto r\mid y\approx_\Pi x\}}
```

A read of a key some record of $x$'s type names only as optional has no
location to link where the object lacks the key; there the read gave
`undefined`, since such an object has no prototype (`optT`). Its link is the
optional one, $x.f\mapsto^{?}r$ ([its meaning](SEMANTICS.md#what-is-asserted-and-what-a-heap-change-can-touch)),
written for every record of $\Gamma(x)$ naming $f$, as a field or an optional
key (`optionalOperand`, `optionalRead_sound`):

```math
\frac{\Gamma\vdash_G\mathrm{read}_f(x):A\qquad
      \forall c\in\mathrm{expand}_G(\Gamma(x)).\ f\in\mathrm{fields}(c)\cup\mathrm{optional}(c)}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{read}_f(x):A
  \dashv \Pi\;;\;\Sigma,\{y.f\mapsto^{?} r\mid y\approx_\Pi x\}}
```

Two programs show the difference. In the first,

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

In the second the same read follows a call:

```ts
const done: null = reset(false);
return cell.value;
```

The call empties $\Sigma$, so no atom for `cell` remains and only the first rule
applies: the read is well typed and records where its value came from, but
establishes nothing about the contents. Nothing about what `cell` holds is
provable at that point, whatever the claimed type says.

Each covers cases the other does not. Reading a $\mathrm{Ref}(\mathrm{Ref}B)$
has no primitive result, so only the first applies; a variable whose type is a
union of references does not meet the first rule's plain-reference premise, so
where an atom exists only the second does. Where both apply the second yields
strictly more, the evidence records which was used, and soundness does not depend
on the choice — only precision does.

**Writing** stores $y$'s value in the field $f$ of the object $x$ names. The
result is `null`. Where $y$'s value is a known primitive it establishes the new
contents for $x$ and every variable recorded equal to it; it keeps the atoms
about locations a distinct link $z.g\neq x.f$ separates from the written one;
it destroys the rest of $\Sigma$ — including atoms about cells that may or may
not be this one. Writing a value that is not a known primitive, an object say,
establishes no new contents and keeps the separated atoms all the same:

```math
\frac{\Gamma\vdash_G\mathrm{write}_f(x,y):\mathsf{Null}
      \qquad(\Gamma;\Pi)(y)=R}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{write}_f(x,y):\mathsf{Null}
  \dashv \Pi,\;r=\mathsf{null}\;;\;
   \{z.f\mapsto R\mid z\approx_\Pi x\},\;\Sigma_{\neq x.f}}
\qquad
\frac{\Gamma\vdash_G\mathrm{write}_f(x,y):\mathsf{Null}
      \qquad(\Gamma;\Pi)(y)\ \text{undefined}}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\mathrm{write}_f(x,y):\mathsf{Null}
  \dashv \Pi,\;r=\mathsf{null}\;;\;\Sigma_{\neq x.f}}
```

where $\Sigma_{\neq x.f}=\{z.g\mapsto S\in\Sigma\mid z.g\neq x.f\}$ (`writeOutput`,
`write_sound`).

**Every other expression**, calls included, empties the heap part and leaves the
equalities untouched:

```math
\frac{\Gamma\vdash_G t:A}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow t:A\dashv \Pi\;;\;\emptyset}
```

$\Pi$ and $\Sigma$ are finite lists of atoms, read as their conjunction and
extended with a comma, exactly as $\Gamma$ is. $\emptyset$ is the empty heap
part: nothing is known about any cell. $\Pi$ carries over verbatim, because no
equality mentions the heap. There is no separating conjunction here — these
facts are duplicable, and carry no ownership or disjointness.

The shape a type theorist will look for is missing on purpose: **there is no
general frame rule.** A write through $x$ discards what is known about $z$ even
when $z$ is a different name, because distinct names need not be distinct
locations — $\Pi$ can witness that two names are equal, never that they are
not. So the positive direction is proof-driven and the negative direction is
total but for one timeless fact, the distinct link $z.g\neq x.f$: two field
locations that differ whatever they hold (`HeapLinks.distinctFrom`, from
`write_frame`, which preserves a fact at another location from a proved
runtime inequality). Allocation states it: a fresh object's locations differ
from every field each record of a record-typed slot names (`contractFields`).
The lowering restates, at each statement entry, the links between a private
cell and the slots whose records' fields it was allocated after, or that were
allocated after it ([DESIGN.md](DESIGN.md#current-content-assertions)).

The practical shape of the gap is worth stating. Facts about several cells
coexist freely: allocation and reads preserve every one of them, so a program
that allocates three cells knows the contents of all three. A write collapses
that set to the written cell, its aliases and the locations distinct links
separate from it, and a call empties it: a callee may write any location its
operands reach, and nothing states which locations those are. $\Pi$ is not subject to this at
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

```math
\frac{\mathrm{checkStep}(G,(\Gamma,t,A),K,e)=\mathrm{some}(K')
\quad\mathrm{EnvOk}_G(\Gamma,\rho,n,W)\quad K(\rho,h)}
{\mathrm{SafePost}(⟦A⟧,
  \lambda(h',v).\,K'(v::\rho,h'),n,W,h,\mathrm{close}_{\rho}(t))}.
```

As above, the initial world must be admissible and the heap must satisfy it.
The checker binds evidence to the requested expression and type and checks scope.
It computes a guaranteed output, not an assumed postcondition:

| Evidence                             | Guaranteed output in the result-pushed frame                                                                                                                                                                                             |
| ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Pure value or variable copy          | Preserve facts and links; copies establish slot equality and duplicate existing facts. Literals establish their exact result even when their supplied type is wider. Lambda bodies require ordinary typing, without captured heap facts. |
| Pure test or conditional             | Preserve existing facts and links, shifted past the result slot. Every evaluated subexpression must be syntactically pure (a length `lenOf` of a slot among them: an array's store is read by a field read of its own, then counted); no new result-to-cell link is invented.                                                                       |
| Ordinary typed read                  | Preserve facts and record read links to the receiver and witnessed aliases, retaining its plain or callable descriptor; through a key a record may lack, optional links. No prior current-content fact is needed. Its result has the supplied type. |
| Observed read                        | Preserve facts and links; record the result's primitive predicate and its current read relationship. That set must fit the requested ordinary result type.                                                                               |
| Sliced read (`slicedRead`)           | A read a cell fact says finds no `undefined` (every predicate other than it): ordinary read evidence at the location's contract $C$, whose slice $T_{\mathsf{false}}(C)$ by the `undefined` tag is below the requested type by a checked subtype proof. As an ordinary typed read otherwise. |
| Known immutable value                | Check the requested primitive type against a proved slot fact or the slot's ordinary primitive type.                                                                                                                                     |
| Allocation                           | Check ordinary creation evidence and scope for either descriptor, preserve old facts, add the fresh bag's initial contents where a checked value slot's are known, and its fields' distinctness from every record slot's. Closure code is not executed. A merge of two slots is an allocation too: old facts preserved, the fields its result type names distinct. So is an array literal's store of value slots, whose element locations lie past the heap's end: old facts preserved (`store_alloc_sound`); an element read (`elemAt`) is still an ordinary expression. |
| Write                                | Check ordinary write evidence (no old-content premise), discard old cell facts but those a distinct link separates from the written location, record new contents for the receiver and its witnessed aliases where the value is a known primitive, or `defined` where its type rules `undefined` out, and preserve immutable facts and slot equalities. Read links are discarded. |
| Ordinary expression, including calls | Check ordinary evidence, discard cell facts and read links, preserving immutable facts and slot equalities.                                                                                                                              |

`typedRead_sound`, `slicedRead_sound`, `read_sound`, `alloc_sound` (with
`merge_alloc_sound` and `store_alloc_sound`) and
`write_sound` prove the read, allocation and write rules above. The sliced
read is

```math
\frac{\Gamma\vdash_G \mathsf{readAt}\,f\,x : C\quad x.f\mapsto R\in\Sigma\quad
      \mathsf{undefined}\notin R\quad T_{\mathsf{false}}^{\mathsf{isUndef}}(C)\le A}
     {\Gamma;\Pi;\Sigma\vdash_G r\leftarrow \mathsf{readAt}\,f\,x : A\dashv\Pi;\Sigma}\ \textsf{read-sliced}
```

which is how `let x: T;` assigned an object on every path is read at $T$. None of them takes a premise about a cell's old contents, and the
checker's write evidence carries none either. These are operation rules within a
local segment: at the next statement entry, only the supplied interface
survives.

The `allocated` and `typedRead` evidence constructors serve both plain and
callable bags. `allocationSlot` selects a `make` whose initializer is an
existing value slot; it never treats an effectful initializer as a value.
`bagOperand` (for allocation) requires a nonempty expansion whose clauses are
all `refs` or `callable` with the same first invariant operand. It therefore
accepts a neutral bag view as well as a single shape, while rejecting a
nullable or mismatched alternative. Operand comparison is syntactic; it does
not search for an equivalent invariant. A typed read needs less
(`fieldOperand`): every clause of the receiver's nonempty expansion is a `refs`
or `callable` whose first invariant operand has the field read, at any type,
so the read is of a location of the object whichever arm it has, and its link
names that location.
The same allocation proof frames old facts and records the fresh bag, and the
read proof records links with the object's actual descriptor.
Nested invocation uses the existing closure, let-binding and heap rules, with
no separate reentry mechanism. [ExecutionModelTests.lean](lean/Verification/Model/Tests/ExecutionModelTests.lean) runs the machine on these calls, for a
plain and a callable bag: a closure writes `true` into a captured bag after a
`false` read was saved, and the saved value stays `false` while a fresh read
gives `true`; an active function's callback mutates its bag and reenters it,
and the outer frame keeps its saved read; an initializer's write and
allocation precede the callable's allocation, and the argument's write
precedes the body's read, a stuck initializer blocking the argument and a
stuck argument the body. Under Node, `invalid-closure-graph-captured-cell`
returns the `null` its closure wrote, where the pipeline refuses its number
claim.

`pureTerm` includes values, variables, tests of pure terms, and conditionals
whose condition and both arms are pure. It excludes calls, reads, writes and
allocation, including function creation. A checked creation effect separately
preserves old facts while allocating the function's bag; the body may have
effects because creation does not run it. `pure_step` and `pure_frame` prove:

```math
\frac{\mathrm{Pure}(t)\quad(h,t)\longrightarrow(h',t')}
 {h'=h\quad\land\quad\mathrm{Pure}(t')},
\qquad
\frac{\mathrm{Pure}(t)\quad\mathrm{Safe}(A,n,W,h,t)\quad\forall v.\,Q(h,v)}
 {\mathrm{SafePost}(A,Q,n,W,h,t)}.
```

This extends the existing pure-effect evidence; it does not add another typing
rule or certificate constructor. It retains heap observations through null
predicates without treating an effectful operand as pure. A negated graph guard
checks its full expression claim separately and swaps the operand's successors;
it does not invent an equality between a Boolean and its negation.

Primitive result predicates are finite lists of null/undefined/Boolean
singletons, numeric singletons and the number family. `HeapKnowledge.check_sound` and `project_checked`
justify transfer and alias-preserving projection along executable slot maps.

The maintained graph checker carries the same postconditions in its state
invariant and checks every incoming edge, including back edges. External entry
requires empty knowledge; effect-only continuations drop result-slot facts.
Source observations use the
same checked graph facts, through the checkpoints below.

Boolean guards use the following rule, proved by `observeBoolean_holds`:

```math
\frac{x\mapsto y\quad y=b}
 {x\mapsto\{b\}},\qquad b\in\{\mathsf{true},\mathsf{false}\}.
```

The points-to atom must hold in the current heap. Note that
$\mathrm{read}(x)$ is the language's read expression; the assertion that
used to share its name is now $x\mapsto y$. A tag observation does the same with
what it leaves of $y$'s predicate (`observeTag_holds`): each atom whose clause
answers the other way is dropped, and a family found equal to one of its
values is that value (`observeAtom`: `number` equal to a number other than a
zero is that number, `string` equal to a string is that string; equal to a
zero it stays `number`, the zeros being two values). An optional read link
gives the fact only where what remains rules `undefined` out, which then says
the key is present (`linkFacts_holds`):

```math
\frac{x.f\mapsto y\quad y=R}{x.f\mapsto R}
\qquad
\frac{x.f\mapsto^{?}y\quad y=R\quad \mathsf{undefined}\notin R}{x.f\mapsto R}
\qquad
\frac{y=\mathsf{number}\quad y\equiv b\quad b\neq\pm0}{y=\{b\}}
\qquad
\frac{y=\mathsf{string}\quad y\equiv s}{y=\{s\}}.
```
[ExecutionModelTests.lean](lean/Verification/Model/Tests/ExecutionModelTests.lean) compares `numberEqual` with IEEE equality on NaN, infinities and adjacent doubles.
A slot equality $x=y$ permits a checked write through either alias to
establish the new contents for both, as the
[write rule](#the-reference-operations) above states; every other cell
observation is discarded. Read links are invalidated by writes and calls, while
slot equalities survive. Together these let source lowering discard a receiver
temporary without losing a write to its original cell.

An allocate-false/write-true/read program verifies with an explicit
current-true claim at the return entry; a broad entry claim naming only the
storage contract is insufficient.

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

```math
K_c=K_l.
```

`SourceExtraction.checkAssertions_cut` proves this equality from acceptance.
Each incoming edge separately establishes the supplied heap interface (ordinary
context coverage is checked alongside it):

```math
\frac{\mathrm{checkKnowledge}(K_{\mathrm{out}},K_l,m)=\mathsf{true}
\qquad K_{\mathrm{out}}(\rho,h)}{K_l(\mathrm{mapEnv}(m,\rho),h)}.
```

The next statement is checked from $(\Gamma_l,K_l)$, independently of any
stronger facts proved by predecessors. Loop heads use the same interface on both
initial and back edges. Empty knowledge means forget all extra facts; an empty
_content predicate_ remains an impossible observation, not an absent one.

**Expression claims are local obligations within a statement, not full-state
interfaces.** Their supplied result type must be justified at the expression;
a supplied current predicate is checked at a no-op result checkpoint, naming
slot zero before projection, unless every contract of the read object already
implies it: then it is the persistent-observation obligation below, which
holds at any point, a closure's entry included, where nothing of the heap is
known. Within the statement, the checked effect rules may
retain its entry assumptions and derive postconditions. Calls and writes forget
facts according to those rules. Administrative copies do not discard facts.
Thus a Boolean read claim is compatible with locally proving a true result from
an explicit entry observation; it does not license recovering an observation
forgotten at an earlier statement boundary.

At an expression checkpoint, required knowledge is checked by entailment,
$\mathrm{checkKnowledge}(K_c,K_r,\mathrm{id})=\mathsf{true}$.
`checkAssertions_sound` proves the implication. The independent source consumer
reconstructs both kinds of boundary and checks them alongside graph acceptance
and supplemental expression proofs; these are not producer-selected policies.

Ordinary compositional expression proofs, including lambda bodies, do not carry
heap contexts. For a point assertion $\mathrm{ObservedRef}(B,R)$ there,
the adapter conservatively requires the ordinary sequent:

```math
x:B\ \vdash\ x:R.
```

Here $x$ is an arbitrary **stored value**, not the reference. This checks that
the invariant implies the observation uniformly. For a union of cell contracts,
$B$ is the union of their invariant contents, so every alternative must imply
the observation. Its proof is a supplemental
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

[CertificateProducer.lean](lean/Verification/Model/Programs/CertificateProducer.lean) accepts an actual graph, its declared result type and
start label, and one `PointClaim` per node. Each claim fixes both the entry
context and the expression result type. These are annotations in this Lean
interface. The source adapter supplies them for the supported
fragment; new source forms require the corresponding extraction obligations.
[DirectProof.lean](lean/Verification/Model/Programs/DirectProof.lean) holds the recipes for source closures: untrusted plans fixing rule structure and intermediate types.

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

The semantic coverage rule `CallArrow` now admits ordered parameter lists.
Source selection checks inclusion contravariantly at every argument position,
with equal actual counts. A union may split at any position while preserving
its prefix and suffix. An empty type at any position makes the domain
uninhabited; an empty parameter list itself still admits a zero-argument call.
Result combination uses the same compatibility check and shared-execution
argument as unary overloads. Graph signatures now use domain lists directly,
and `checkArrow` checks `CallArrow` derivations with soundness and completeness
proofs. Search splits unions at any parameter position. Function-creation rules
check that every signature offers at least the descriptor's arity and type the
body under the parameters the code takes, followed by captures. Application evidence and source
lowering still expose unary calls; accepted source programs have not widened.

The final `accept` check binds the evidence to **all the requested point claims**
as well as calling `checkEntry` on the actual program and external input context. Thus a valid certificate
for different annotations is rejected. Lean proves:

```math
\begin{gathered}
\mathrm{produce}(G,I,f,R,P,Q,\ell,H,\Gamma_0)=\mathrm{ok}(C)
\\
\Longrightarrow\quad
\mathrm{accept}(G,R,P,Q,C,p,\Gamma_0)=\mathsf{true},
\\
\mathrm{accept}(G,R,P,Q,C,p,\Gamma_0)=\mathsf{true}
\\
\Longrightarrow\quad
\mathrm{claims}(C)=Q
\;\land\;
\mathrm{checkEntry}(G,R,P,C,p,\Gamma_0)=\mathsf{true}.
\end{gathered}
```

Here $I$ enumerates labels, $f$ bounds expression search depth, $Q$ contains the
supplied point annotations, $\Sigma$ contains optional type hints, and $\Gamma_0$ is
the independent input contract. Search fuel is
not an execution budget and never occurs in the typing rules or certificates.
`produce_checked` proves the first implication; `accept_claims` proves claim
fidelity, and `accepted_from_inputs` obtains safety for arbitrary typed arguments
from the consumer alone. `accepted_safe` is its closed-entry counterpart.
The producer can be replaced without changing the soundness argument.

Expression evidence validation uses `ProgramCertificates.checkTreeResult` in a
single traversal. Its coercion checks retain the requested subtype judgment and
resource exhaustion in `CheckResult`, the result shared with proposal search.
`checkTreeUsing_eq` proves that the acceptance projection has exactly the
declarative rule premises. `ExpressionClaims.checkResult` additionally checks
label validity, the requested root judgment and term scope; `checkUsing_eq`
proves its acceptance condition. Member-binding coverage uses the Boolean
subtype predicate. These results concern expression evidence; the program
acceptance and safety implications above remain the semantic boundary.

Failure reports a claim-count mismatch, an expression label, an edge's source
and destination, or final consumer rejection. Failure means unsupported or
unjustified within this search, not a proof that the program is untypable.
No evidence is returned as successful unless the consumer accepts it.

The [serialized request protocol](REQUEST-PROTOCOL.md) exposes this path from a
program and its annotations to checked evidence through the verifier binary.
Source extraction correctness, producer completeness and integration of
extended source claims are outside these results.

### Derived source forms

A condition of a Boolean literal type takes only its arm (`ifKnown`): the
pipeline case `known-condition` reaches the rule, and `ocaml-producer/test.mts`
claims its result at that arm alone, a claim refused for
`invalid-known-condition`, whose condition a closure resets. [ExecutionModelTests.lean](lean/Verification/Model/Tests/ExecutionModelTests.lean) shows the
machine keeping a known condition's write. Source closure blocks support
terminal branches with both arms returning, including nested branches and
checked entry refinements.
Source ternaries reuse these rules and the existing primitive-tag union elimination.
Their own expression claim supplies the result type; both arm claims are checked
under the corresponding refined context. This introduces no additional rule or
trusted proof-search step.
Null coalescing is likewise a derived form: a let saves the left value, and
`unionVar` with known nullish-tag conditionals selects the fallback or saved value.
No truthiness rule is involved; false remains a result of the left operand.

**Shadowing.** JavaScript's scopes nest; the lowering's are lists of
names, each declared once (a second is `duplicate or shadowing local
declaration`). The parser renames instead: a local whose name another
declaration binds in a scope enclosing its own (a module binding, an outer
local or parameter, a named function or class expression's own name) binds
$x^{@l:c}$, its spelling and its declaration's line and column
(`x@3:9`, which no source identifier spells), and every identifier
TypeScript binds to that declaration, a shorthand property `{ x }`
included, reads it. This is $\alpha$-conversion, which changes no value:

```math
\frac{x\in\mathrm{dom}\Gamma\quad x'=x^{@l:c}\notin\mathrm{names}(\Gamma,S)\quad \Gamma\vdash_R\ \mathsf{const}\ x'=e;\ S[x'/x]}
     {\Gamma\vdash_R\ \mathsf{const}\ x=e;\ S}\ \textsf{shadow}
```

and likewise for `let` (a cell included), parameters, patterns, closure
parameters, `for...of` and `catch` bindings, in function and closure bodies
alike. JavaScript gives the name to the declaration from its block's start,
so a mention of a shadowing local above its declaration, a closure's
included, or in its own initializer is refused by the parser (the temporal
dead zone: JavaScript throws there, and the outer binding is not what it
reads); a pattern element may name one bound before it in the pattern:

```math
\frac{x'\ \text{renames}\ x\ \text{declared at}\ d\quad \text{a mention}\ m\ \text{of}\ x'\quad m<d\ \lor\ m\in\mathit{init}(d)}
     {\text{refused (temporal dead zone)}}
```

**A `let` nothing assigns.** A `let` statement whose bindings are all
initialized and which no assignment, compound or logical assignment, update,
destructuring assignment or `for` head in their scope writes (closures
included, found by the name the parser gives each binding) is the `const`
statement: each binding holds its initial value throughout, so a read of it
is that value either way:

```math
\frac{\overline{x}\ \text{initialized}\quad \overline{x}\notin\mathrm{written}(S)\quad \Gamma\vdash_R\ \mathsf{const}\ \overline{x=e};\ S}
     {\Gamma\vdash_R\ \mathsf{let}\ \overline{x=e};\ S}\ \textsf{let-const}
```

So a tag test narrows such a binding as it narrows a `const`, and a `let`
pattern binds. A `let` pattern whose bindings are written binds names no
source spells, as a `const` pattern does, then a `let` of each source name
at its value: a cell of its own, whose contract is an unannotated `let`'s,
its initial value's type widened:

```math
\mathsf{let}\ p = e\;\equiv\;\mathsf{const}\ p[\overline{x\mapsto x^{\circ}}] = e\,;\ \mathsf{let}\ \overline{x = x^{\circ}}
```

JavaScript reads and defaults the pattern's positions, then initializes the
bindings, in that order either way; each cell is claimed at its name, where
its initial value is. Such a pattern in a `for` head is refused. A `let` that is written and holds a union of objects is
not narrowed by a test of its object (a cell's known contents are primitive
values, or that it holds no `undefined`, and a write between the test and the
read may replace it); a read of a member only some arms state is refused
with that reason.

**Shorthand properties.** A shorthand property writes the value its name
reads, as the field of that name, the name resolved as any read of it (a
shadowing local's renaming, above, included):

```math
\{\ldots,\ x,\ \ldots\}\;\equiv\;\{\ldots,\ x\colon x,\ \ldots\}
```

**Older spellings.** `<T>e` is `e as T` and `<const>e` is `e as const`,
the same assertion (an obligation on the operand, never a fact); a
top-level `;`, as one in a body, is nothing.

A derived class's constructor (`class D extends B`, its body
`s̄₁; super(ā); s̄₂`, `s̄₁` reading no `this`) is its base's construction,
bound to a name no source spells, then the class constructor's lowering
([classes](#classes)) whose
allocation is the allocation from parts copying it:

```math
\mathsf{class}(\vec x).\ \vec s_1\,;\ \mathsf{const}\ \textit{base} = \mathsf{new}\ B^{\circ}(\vec a)\,;\
  \mathcal{C}(\vec s_2,\ \varphi_0,\ \varnothing)
  \quad\text{with}\quad
  \mathcal{C}(\varepsilon,\varphi,A) = \{\texttt{[[proto]]}{:}\,D.\texttt{[[prototype]]},\ \ldots\textit{base},\ \varphi,\ \overline{f{:}\,\mathsf{undefined}}\}
```

where $B^{\circ}$ is `B`'s constructor claimed also at the fresh instance it
allocates, its keys exact (`ctorGraph` checks its code at that signature too).
`D` without a constructor has JavaScript's implicit one,
`constructor(...args) { super(...args); }`: its parameters are $B$'s, at
their types, under names no source spells, and $\vec a$ is them. A class's
prototype object is allocated once, at its definition:

```math
D.\texttt{[[prototype]]} = \{\texttt{[[proto]]}{:}\,B.\texttt{[[prototype]]},\ \kappa_D{:}\,\mathsf{undefined},\ m{:}\,D.m,\ \ldots\}
```

its own methods, linked to its base's under the prototype key, as
JavaScript's `D.prototype` is; $\kappa_D$, the class's key, is there where
`instanceof D` is written in the file, below. A prototype holding nothing
of its own that nothing tests is not allocated: `D`'s instances then hold
the nearest ancestor's (or none), and every read and test answers the same.
`super.m(ā)` is `B.m.call(this, ā)`, with `B.m` the closure `B`'s prototype
chain holds. So the allocation's keys are exact, and `D`'s declared type,
its own members and `B`'s, covers it through the prototype chain
([method coverage](POSITIVE-TYPES.md#clause-coverage), `CoversByProto`).

A generic method `m<V>(…)` is the instance's member with quantified
signatures ([generic methods](#generic-methods)), and its closure `D.m` a
generic closure, checked once at a scheme received by the instance
(`funScheme`), which the prototype holds. The parser names the closure's
binder $k$ by the member's key and the position (`"m"#k`,
`fragment-parse`'s `lambda`), and the producer's scheme row for the
prototype's field binds those names; the member's scheme binds the
declaration's. The prototype's scheme covers the member bound to the
instance up to renaming the member's binders to its own
([`CoversByScheme`](POSITIVE-TYPES.md#clause-coverage)): its receivers read
none of its binders and hold the instance, and its signatures cover the
member's renamed ones at every instance. A bounded binder is refused, since the row's
name spells its bound.

A method declaring `this: T` is the instance's member whose host must meet
`T` ([records](POSITIVE-TYPES.md#records)), and its closure `D.m` takes `T`
as its receiver, so its body reads `this` at `T`. The prototype's closure
covers the member through the member's `T`, whose values the closure's
receiver admits, whatever the instance type is
([method coverage](POSITIVE-TYPES.md#clause-coverage)); a call on the
instance, `this.m()` among them, proves its host within `T` (`bindMember`).

What a class declaration may not hold, each for its reason:

- a generic method declaring `this: T`: its member is a scheme the member
  bound to its host meets, whatever receiver it is given, which states no
  type the host must meet ([DESIGN](DESIGN.md#method-members-are-host-relative));
- a generic method with a bounded binder: the member's binder row is named by
  its bound, which the closure's binder, named by the parser, is not;
- a constructor parameter default reading `this`, or a constructor statement
  reading it other than as a field assignment's target: the instance is
  allocated at the constructor's end;
- a member with a computed key (a method is a binding and a prototype key
  named by its plain name) other than a static `[Symbol.hasInstance]`,
  below;
- an accessor (reading it runs code; a member read is a plain one), an
  index signature (instances are what construction allocates), a static
  block reading `this` (the class value, whose statics are bindings of their
  own);
- a private name in inheritance (a derived instance's base part is a copy,
  and a copy holds no private slot), and `#x in o` (it tests an own slot,
  where $\mathsf{hasKey}$ walks the prototype chain and would find an
  instance's slot from an object inheriting from it);
- extending a generic class other than at the base's own binders (a generic
  base's construction is at its binders' rows, [classes](#classes)), and
  extending `Array` (its instances are what the library's constructor
  allocates, not an ordinary object).

`e instanceof C`, with `C` an identifier TypeScript binds to a class the
file declares at its top level, evaluates $e$, then `C` (read as its
prototype object, which the class statement binds with it), then looks for
$\kappa_C = \texttt{[[}C\texttt{.prototype]]}$, the key only
$C.\texttt{[[prototype]]}$ owns, along $e$'s prototype chain:

```math
e\ \mathtt{instanceof}\ C\;\equiv\;\mathsf{let}\ x=e\ \mathsf{in}\ \mathsf{let}\ p=C.\texttt{[[prototype]]}\ \mathsf{in}\ \mathsf{hasKey}(\kappa_C)(x)
\qquad
\frac{\Gamma\vdash e:A\quad \Gamma\vdash C.\texttt{[[prototype]]}:P}
     {\Gamma\vdash e\ \mathtt{instanceof}\ C:\mathsf{boolean}}
```

Any operand is admitted: $\mathsf{hasKey}$ answers `false` on a primitive,
as `instanceof` does (it throws only on its right operand). A tested
immutable variable is refined as by every tag test ([guards](#guards)).

A class whose chain of bases, classes of the file, holds a static method
keyed by the realm's `Symbol.hasInstance` (TypeScript binds the key to the
standard library's `unique symbol` property) answers `instanceof` itself:
ECMA-262's InstanceofOperator calls `C[Symbol.hasInstance]` with the
operand and converts the result by `ToBoolean`, walking no chain. The
method is a static binding $C.\texttt{[Symbol.hasInstance]}$ as any static
method is, reading no `this`, so its receiver is unobservable and it is
called plainly; a derived class reads its nearest base's, which its
constructor inherits:

```math
e\ \mathtt{instanceof}\ C\;\equiv\;\mathord{!}\,\mathord{!}\,\big(C.\texttt{[Symbol.hasInstance]}(e)\big)
\qquad
\frac{\Gamma\vdash C.\texttt{[Symbol.hasInstance]}(e):B}
     {\Gamma\vdash e\ \mathtt{instanceof}\ C:\mathsf{boolean}}
```

The operand must meet the method's parameter, as any actual's, and the
test refines nothing: the method's answer says nothing of the operand's
type, where TypeScript narrows it to `C`.

An optional chain is the same derived form with the arms exchanged. The
parser writes `r?.x` and every link after it in the chain (`.b`, `[k]`,
`(a)`, `!`) as one `optional` node whose body applies those links to the
variable $\mathsf{chain}$ (`chainName`, spelled `?.`, which no source
identifier is), so a nullish receiver skips the rest of the chain, as
JavaScript's short-circuit does; a second `?.` in a chain tests the chain so
far, which is `undefined` where an earlier one skipped:

```math
r\,?.\,b\;\equiv\;\mathsf{let}\ \mathsf{chain}=r\ \mathsf{in}\ \mathsf{if}\ \mathsf{nullish}(\mathsf{chain})\ \mathsf{then}\ \mathsf{undefined}\ \mathsf{else}\ b,
\qquad
\frac{\Gamma\vdash r:A\quad T_{\mathsf{false}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash r\,?.\,b:\{\mathsf{undefined}\mid T_{\mathsf{true}}(A)\neq\emptyset\}\cup B}
```

with $T_q$ the nullish tag's slices. The body is checked where the saved
receiver holds its present slice, so a method called through the chain
(`o?.m()`) has the present `o` as its receiver. `o.m?.()` would test the
method but call it with `o`, which the chain does not save apart from the
tested value, and is refused. On a `null` or `undefined` literal receiver the
chain is `r, undefined`: the literal is the receiver's whole value, and the
body never runs.

`typeof e` as a value is the string naming the shape of $e$'s value, one tag
test per answer in turn, the operand evaluated once (`typeofTerm`); a value no
test holds of has call code, which `typeof` names `"function"`:

```math
\mathsf{typeof}\ e\;\equiv\;\mathsf{let}\ x=e\ \mathsf{in}\
\mathsf{if}\ \mathsf{isUndef}(x)\ \mathsf{then}\ \texttt{"undefined"}\ \mathsf{else}\
\mathsf{if}\ \mathsf{typeofObject}(x)\ \mathsf{then}\ \texttt{"object"}\ \mathsf{else}\ \cdots\
\mathsf{if}\ \mathsf{isSymbol}(x)\ \mathsf{then}\ \texttt{"symbol"}\ \mathsf{else}\ \texttt{"function"}
```

in the order undefined, object, boolean, number, string, bigint, symbol. It
splits $x$ by `unionVar` as `??` does (`selectPlan`), so a label whose shape
is settled reaches one answer; its claim is `string`. A comparison of `typeof e`
with a shape's literal stays the one tag test ([guards](#guards)).

`key in o` evaluates the key, then the object, then asks whether the object
has the key. A string literal key is the tag test $\mathsf{hasKey}(\kappa)$ of
the object, which refines a tested immutable variable as every tag test does.
A key whose claim is a union of string singletons $\kappa_1\mid\cdots\mid\kappa_n$
dispatches on them, the last needing no test since the key is one of them
(`inKeysTerm`):

```math
k\ \mathtt{in}\ o\;\equiv\;\mathsf{let}\ y=k\ \mathsf{in}\ \mathsf{let}\ x=o\ \mathsf{in}\mathsf{if}\ \mathsf{strEq}(\kappa_1)(y)\ \mathsf{then}\ \mathsf{hasKey}(\kappa_1)(x)\ \mathsf{else}\ \cdots\mathsf{hasKey}(\kappa_n)(x)
```

```math
\frac{\Gamma\vdash o:A\quad \forall\gamma\in\mathrm{expand}_G(A).\ \gamma\ \text{a record, dictionary, arrow or callable clause}
      \quad \kappa_i\notin\mathcal R}
     {\Gamma\vdash k\ \mathtt{in}\ o:\mathsf{boolean}}
```

where $\mathcal R$ is the keys the model does not answer as JavaScript does
(`inKeyRefusal`, [guards](#guards)). The operand's clauses are
objects because `in` throws on a primitive, where the test would answer
`false`, and not a class value, whose static members are bound apart.

A key TypeScript types as other than string literals (a `string`, a number,
an array index among them, a symbol) may name what the model does not answer
as JavaScript does: a prototype's key, or an array's element, which the store
holds rather than a key. Such a test is the host's, a call of the intrinsic
$\%\mathsf{HasProperty}\%$ (`intrinsics.mts`), which the parser writes where
TypeScript's type of the key has another part, and which narrows nothing:

```math
k\ \mathtt{in}\ o\;\equiv\;\%\mathsf{HasProperty}\%(k,\ o)
\qquad
\%\mathsf{HasProperty}\%:(\mathtt{string}\mid\mathtt{number}\mid\mathtt{symbol},\ \mathtt{object})\Rightarrow\mathtt{boolean}
```

The call evaluates the key, then the object, then the lookup, as `in` does;
converting the key runs no code, and neither does the lookup on the objects
a program holds (no proxy, [trust surface](DESIGN.md#trust-surface)).

A read `o[k]` of an object whose key is claimed at a union of string and number
singletons $\kappa_1\mid\cdots\mid\kappa_n$ dispatches the same way, each
singleton selecting the read of the key it converts to (a number's, the key
its `ToString` spells), as a literal key's read is (`keySingletons`,
`keyedReadTerm`):

```math
o[k]\;\equiv\;\mathsf{let}\ x=o\ \mathsf{in}\ \mathsf{let}\ y=k\ \mathsf{in}\
\mathsf{if}\ \mathsf{eq}(\kappa_1)(y)\ \mathsf{then}\ \mathsf{readAt}\;\kappa_1\;x\ \mathsf{else}\ \cdots\
\mathsf{readAt}\;\kappa_n\;x
```

with $\mathsf{eq}$ the tag `strEq` or `numEq`. It is typed by `unionVar`,
`ifTag` and the read rules alone. NaN is no singleton here, since no equality
test finds it.

Logical AND and OR return an operand, as in JavaScript: the left one where its
truthiness decides, the right one elsewhere. For a left operand that is not a
Boolean they are the same derived form on the truthiness test:

```math
a\mathbin{\&\&}b\;\equiv\;\mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{if}\ \mathsf{truthy}(x)\ \mathsf{then}\ b\ \mathsf{else}\ x,
\qquad
a\mathbin{\Vert}b\;\equiv\;\mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{if}\ \mathsf{truthy}(x)\ \mathsf{then}\ x\ \mathsf{else}\ b,
```

split by `unionVar` on $x$ (`selectPlan`, which `??` and default parameters
share): a label whose truthiness is settled selects its arm by `ifTag`, and
one that is not (a number, a string) takes both arms by `ifBool` on the test.
Writing $T_q(A)$ for the labels of $A$ that may answer $q$ (`tagSlice`):

```math
\frac{\Gamma\vdash a:A\quad T_{\mathsf{true}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash a\mathbin{\&\&}b:T_{\mathsf{false}}(A)\cup B}
\qquad
\frac{\Gamma\vdash a:A\quad T_{\mathsf{false}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash a\mathbin{\Vert}b:T_{\mathsf{true}}(A)\cup B}
```

The right operand is checked where the saved left operand holds the slice
that reaches it; a named immutable left operand moves to that slot, as for
`??`, so `o && o.a` reads a field of the truthy `o`. The falsy slice is
exactly what `ToBoolean` leaves: of `number`, all of `number`, since `0`, `-0`
and NaN are falsy (TypeScript's `0` there omits NaN). `!a` of a value that is
not a Boolean is $\mathsf{if}\ \mathsf{truthy}(a)\ \mathsf{then}\ \mathsf{false}\ \mathsf{else}\ \mathsf{true}$,
by the same split. A condition that is not a Boolean is its truthiness: a
statement guard dispatches with `tagBind` on $\mathsf{truthy}$, refining a
tested immutable variable to $T_q$ of its type on each edge, and a closure
branch uses the split above. A disjunctive outcome (a false `&&`, a true
`||`) joins at its target, whose entry claim each incoming edge establishes
under its own refinement.

For Boolean left operands, logical AND and OR use the derived forms:

```math
a\mathbin{\&\&}b\;\equiv\;\mathsf{if}\ a\ \mathsf{then}\ b\ \mathsf{else}\ \mathsf{false},
\qquad
a\mathbin{\Vert}b\;\equiv\;\mathsf{if}\ a\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ b.
```

They share the source conditional proof builder, including null refinement within
the right operand;
the synthetic constant arm requires a literal proof, not a source claim.
At statement guards the source compiler instead emits short-circuit graph paths,
whose Boolean/null observations justify the intermediate and successor contexts.
It also checks the complete expression claim using the derived expression form.
Thus graph decomposition cannot silently discard the producer's condition type.

A chain of one operator is read right-nested, the parser's left nesting
reassociated:

```math
(a\mathbin{\&\&}b)\mathbin{\&\&}c\;\equiv\;a\mathbin{\&\&}(b\mathbin{\&\&}c),
\qquad
(a\mathbin{\Vert}b)\mathbin{\Vert}c\;\equiv\;a\mathbin{\Vert}(b\mathbin{\Vert}c),
```

which JavaScript evaluates in the same order to the same value (a falsy
$a$ is the result either way, and so on). Read so, $c$ is checked where $a$
and $b$ each answered, and the inner operator is typed at the whole's
claim, which covers every value it yields. A variable tested by both $a$
and $b$ is split twice; the inner split takes, of its planned arms, those
of the labels the outer one left.

Closure branches whose two arms fall through require no additional typing rule.
Their extracted shape is:

```math
\mathsf{let}\ z = (\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e)
\ \mathsf{in}\ k.
```

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

```math
\mathsf{if}\ c\ \mathsf{then}\ r\ \mathsf{else}\quad
(\mathsf{let}\ z=s\ \mathsf{in}\ k).
```

Here $s$ completes with administrative null, and its local bindings stay inside
$s$. Both $r$ and the surviving sequence check at the supplied function result
type. When $c$ tests an immutable Boolean variable, the surviving sequence uses
the justified false refinement; it does not have to discard this fact as a
shared join would. `early_return_trace` checks both outcomes of an extracted
closure: an early return skips the later write, while the other arm executes it.
General partially returning nested arms remain gated.

A block closure that does not return on every terminal arm completes, which in
JavaScript returns `undefined`; its body ends with $\mathsf{return}\
\mathsf{undefined}$ at the closing brace, so that the shapes above apply
unchanged, and the result claim must admit $\mathsf{Undef}$ (`void` is top). A
bare `return` is the same literal at its keyword.

A keyed access `a[k]` whose key is claimed at one string $s$ is the named
access of $\mathsf{str}(s)$, evaluated after `a` and `k`, and the read rules
above apply. A key claimed at one number $n$ names the property
$\mathsf{ToString}(n)$ (`numberToString`), as JavaScript's `ToPropertyKey`
converts it, where `a` is claimed only at records owning no array store
(`recordReceiver`); an array's number key is its store's element (`elemAt`):

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c_1\cup\cdots\cup c_m\ \text{records without a store}\quad
      \Gamma\vdash_G k:\mathsf{Num}(n)}
     {a[k]\ \leadsto\ \mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{let}\ \_=k\ \mathsf{in}\ x.\mathsf{str}(\mathsf{ToString}(n))}
```

([index signatures](#index-signatures)).

A statement `if` whose arm is one `return` of the read its singleton test
tests returns that read's saved value, in a function body and in a closure's
alike (`guardedReturn`). With $c$ a literal, a name or a field read, nothing
runs between the two reads of $x.f$, so they read the same value:

```math
\mathsf{if}\;(x.f \bowtie c)\;\mathsf{return}\;x.f
\;\leadsto\;
\mathsf{let}\ s=x.f\ \mathsf{in}\ \mathsf{if}\;(s \bowtie c)\;\mathsf{return}\;s
```

and the test's tag edge refines $s$ to the slice of its type the arm admits,
which must lie within the returned read's claim. A call or a write in the arm
leaves the shape, and the arm reads anew.

### Patterns

A pattern binds names from one value, in pattern order, and has no rule of its
own: it is reads, a tag dispatch and lets. Write
$\Gamma\vdash p\Leftarrow(t{:}R)\dashv\Delta$ when binding pattern $p$ to the
value term $t$ reads at $R$ under $\Gamma$ extends the scope by $\Delta$
(`bindTarget` in the graph lowering, `closureBind` in a closure body). A name
binds the read; a nested pattern holds it in an anonymous slot and binds its
own elements over it:

```math
\frac{\Gamma\vdash t:R}{\Gamma\vdash x\Leftarrow(t{:}R)\dashv x{:}R}
\qquad
\frac{\Gamma\vdash t:A\quad
      \Gamma,\_{:}A,\Delta_{<i}\vdash p_i\Leftarrow(\mathsf{read}_{f_i}(\_){:}R_i)\dashv\Delta_i\ \ (i\le n)}
     {\Gamma\vdash\{f_1{:}p_1,\ldots,f_n{:}p_n\}\Leftarrow(t{:}A)\dashv\Delta_1,\ldots,\Delta_n}
```

where $R_i$ is the type the ordinary read rules give $f_i$ of $A$ (`readCell`:
an invariant field at its contract, a view at its bound, an optional field at
its type or $\mathsf{Undef}$, an inherited member at the prototype's, a union
alternative by alternative); a method is refused, since read off its object
it is no function value. An array pattern is the same with
$\mathsf{elem}(\mathsf{read}_{[\,]}(\_),i)$ at the type of position $i$
(`positionRead`: a required position at its type, an optional or rest one at
its type or $\mathsf{Undef}$), a hole being a position no element names. The
array's own iterator, which JavaScript steps, reads the current length and the
next index at each step, so reading position $i$ where its element is bound,
after any default before it ran, is that step: the trust `%Iterate%` states
([trust surface](DESIGN.md#trust-surface)). A pattern over a host iterable that
is not an array is refused; one over an iterable the program defines is the
iterator protocol's steps ([loops](#loops-and-spreads-over-iterables)).

A default replaces a read that is `undefined`, and only then runs. With
$R'$ the read's labels told apart clause by clause (`byClause`: a label that
is a union row, such as a declared alias, is replaced by one label per
clause, the same values) and $T_q$ the tag slice:

```math
\frac{\Gamma\vdash t:R'\quad \Gamma,\_{:}R'\vdash d:D\quad
      \Gamma,\_{:}R'\vdash p\Leftarrow(\mathsf{if}\ \mathsf{isUndef}(\_)\ \mathsf{then}\ d\ \mathsf{else}\ \_\ {:}\ T_{\mathsf{false}}(R')\cup D)\dashv\Delta}
     {\Gamma\vdash (p=d)\Leftarrow(t{:}R)\dashv\Delta}
```

(`tagBind` in a graph, `selectPlan` in a closure). The default is checked
where the earlier bindings are in scope and the later ones are not; a default
that names a later binding of its own declaration is refused by the parser,
since JavaScript throws there (the temporal dead zone) where the lowering
would read an outer binding of that name.

An array rest $\ldots p$ at index $s$ over $A$ whose store is one tuple of
$n$ required positions, whose length is exact (`listT`), is the fresh array of
the positions from $s$ on, claimed at the rest's span $C$ like an array
literal:

```math
\frac{\mathrm{Store}(A)=[A_0,\ldots,A_{n-1}]\quad
      \Gamma\vdash\mathsf{alloc}\{[\,]{:}\mathsf{arr}(\mathsf{elem}(\_,s),\ldots,\mathsf{elem}(\_,n{-}1))\}:C\quad
      \Gamma\vdash p\Leftarrow(\cdot{:}C)\dashv\Delta}
     {\Gamma\vdash[\ldots,\ldots p]\Leftarrow(\_{:}A)\dashv\ldots,\Delta}
```

A rest TypeScript types as no one tuple of required positions (an array, a
union of tuples, a tuple with optional or rest positions) is a **slice**,
marked so by the parser, whose length only the run knows. It is a call of the
trusted intrinsic

```math
\mathtt{\%RestFrom{:}k\%}:\forall T.\ (\mathsf{readonly}\ [\underbrace{\mathsf{unknown}?,\ldots,\mathsf{unknown}?}_{k},\ \ldots T[\,]])\Rightarrow T[\,]
```

on the source, $k$ the rest's index, made after the pattern's reads and
defaults: the fresh array of the source's elements from $k$ to its current
length, claimed at the rest's span with the call's instance:

```math
\frac{\Gamma\vdash\_:A\quad A\le\mathsf{readonly}\ [\mathsf{unknown}?^k,\ldots T\sigma[\,]]\quad
      \Gamma\vdash p\Leftarrow(\mathtt{\%RestFrom{:}k\%}(\_){:}T\sigma[\,])\dashv\Delta}
     {\Gamma\vdash[\ldots,\ldots p]\Leftarrow(\_{:}A)\dashv\ldots,\Delta}\ \textsf{rest-slice}
```

The parameter says nothing of the first $k$ positions, so a union of tuples
of different lengths meets it arm by arm: `[number] | [number, string]` from
1 at $T=\mathsf{string}$. JavaScript steps the array's iterator on past the
pattern's elements to the end, reading the length at each step; no code runs
between the call and that stepping, so the call's reading of the current
length is the step's (the trust `%Iterate%` states). A slice in a closure's
directly checked body is refused. An object rest `{ a, ...r }` is the
[allocation from parts](#allocation-from-parts) copying the source's own
enumerable keys less the ones the pattern names, onto a fresh object.

A statement `const p = e` holds $e$ in an anonymous slot for its one entry,
binds $p$ over it, and drops the slot before the next entry, which states
$\Delta$. An array assignment `[x_1, …, ...r] = e` is the same with each read
written to its mutable local at the local's storage contract. A parameter
written as a pattern or with a default binds a hidden name $h$, which the
caller's argument initializes, and the body starts with the pattern over it,
in parameter order:

```math
\mathsf{function}\ f(\ldots,p_i=d_i,\ldots)\,\{S\}\;\equiv\;
\mathsf{function}\ f(\ldots,h_i,\ldots)\,\{\ldots;\ \mathsf{const}\ p_i=h_i\ (\mathsf{default}\ d_i);\ \ldots;\ S\}
```

where $h_i$'s type admits $\mathsf{Undef}$ when there is a default, so a
caller may omit it. A closure parameter's default stays the closure's own
(`parameterOrder`), and its pattern is a `destructure` first in the body.

[LoweringTraceTests.lean](lean/Verification/Model/Tests/LoweringTraceTests.lean) runs a lowered object pattern: the initializer held once, properties read in order, defaults run in pattern order for missing properties only.

### Mutable bindings and module constants

A `let` binding and an assigned parameter lower to a private cell
([DESIGN.md](DESIGN.md#mutable-bindings)). Its
contract $C$ is fixed where it is declared; the initializer and every write
are checked against it (`storage-contract`), and a point claim for the name
describes the cell's current contents, which the
[current-content rules](#current-content-rules-semantic-layer) justify on every
incoming edge. The contract is:

```math
\mathrm{contract}(\mathtt{let}\ x{:}T=e)=T
\qquad
\mathrm{contract}(\mathtt{let}\ x=e)=
\begin{cases}
Q_{\mathit{next}}(x) & \text{the claim for } x \text{ at the entry of the next statement}\\
Q(e) & \text{no statement follows in its block}
\end{cases}
```

with $Q(e)$ the claimed type of the initializer. A declaration ending its block
has no statement after it to read the binding, and the initializer meets its
own claim, so any choice every write is checked against is sound. The producer
proposes TypeScript's declared type, the initializer's type widened
(`let x = 1` stores $\mathsf{Num}$). A `null` or `undefined` initializer
has no declared type in TypeScript (an evolving `any`): the producer proposes
the union of what is written into the binding, its evolved type,

```math
\mathrm{contract}(\mathtt{let}\ x=e_0)=\bigcup_{x=e_i}\mathrm{widen}(Q(e_i))
\qquad e_0\in\{\mathtt{null},\mathtt{undefined}\},
```

over the initializer and every assignment of $x$ in its scope, closures
included, each read at the contract where it reads $x$; the proposal is
refused when no fixed union exists (a value consed onto $x$ grows with it).
An unannotated `[]` is claimed at the array of what its `push`, `unshift` and
index writes add. Any choice is sound here, since every write is checked
against the contract. A parameter $x{:}D$ that the body assigns (`assignsStmt`) has
contract $D$, the caller's value its initial contents.

A `let` without an initializer binds `undefined` where its declaration runs,
which is the derived form

```math
\mathtt{let}\ x{:}T;\quad\equiv\quad\mathtt{let}\ x{:}T\cup\mathsf{Undefined}=\mathtt{undefined}.
```

Definite assignment is not an extra rule: a read at $T$ types only where the
cell's current contents are known to be in $T$, a fact a write of a $T$ value
establishes and a join keeps only when every incoming edge proves it. A
closure reads a captured cell at its contract, $T\cup\mathsf{Undefined}$,
since it may run before the write. Current contents are primitive predicates
or `defined`, which a write of a value whose type rules `undefined` out
records: so a `let x: T;` of an object type `T` assigned on every path is read
at $T$ ([`read-sliced`](#checked-expression-postconditions)), and a call in
between forgets it. Without an annotation there is no contract and the parser
refuses it.

A module constant $c$ bound to $e_c$ by the initialization unit is read by
the module's functions at

```math
\mathrm{type}(\mathtt{const}\ c{:}T=e_c)=T
\qquad
\mathrm{type}(\mathtt{const}\ c=e_c)=Q_{\mathit{init}}(e_c),
```

the initialization unit's claim for its initializer. That unit checks
$\Gamma\vdash e_c:Q_{\mathit{init}}(e_c)$ where it binds $c$, exactly as it
checks an annotation, and a constant never changes, so the functions'
assumption is what the unit establishes (the composition argument is
[DESIGN.md](DESIGN.md#modules-and-code-units)'s, unchanged).

A non-generic class $C$ bound by the initialization unit at its construct
signature $K_C$ is read by its own instance methods and constructor, closures
that unit creates before it binds $C$, as the class's own binding
$C^{\mathit{self}}$ (`C.[[self]]`), which the initialization unit $I$ reads
the way a function reads a module constant:

```math
\frac{\mathtt{const}\ C{:}K_C=\mathtt{ctor}\ldots\in I}
     {\Gamma_I(C^{\mathit{self}})=⟦K_C⟧}\ \textsf{class-self}
```

The unit checks the class value against $K_C$ where it binds $C$, and nothing
reaches $C^{\mathit{self}}$ before: only those closures read it, and none
runs until an instance or the class value exists.

### Source closures and their annotations

A source closure `(x₁: D₁, …, xₙ: Dₙ): Rₛ => t` is checked at the arrows its
claim names, by the creation rule of [Callables](#typing-rules): each claimed
arrow $(R,\vec A,B)$ types the body at its own receiver, its first $n$
parameters and its result. The source adds two requirements. Each claimed
parameter is within the annotation's, $A_j\sqsubseteq_G D_j$ for $j\le n$
(`within`), and, where the source states a result, the body meets it at the
annotated signature (the `closure-result` obligation):

```math
\frac{\forall(R,\vec A,B)\in L.\;\bigl(\forall j\le n.\;A_j\sqsubseteq_G D_j\bigr)
        \land\;\Gamma,\mathit{this}{:}R,\vec x{:}\vec A_{\le n}\vdash_G t:B
      \qquad
      R_s\neq\bot\;\Rightarrow\;\Gamma,\mathit{this}{:}Q_s,\vec x{:}\vec D\vdash_G t:R_s}
     {\Gamma\vdash_G \bigl(\vec x{:}\vec D\bigr)\colon R_s\Rightarrow t\;:\;\bigwedge L}
```

with $R_s=\bot$ for a closure whose result the source leaves out (the
Fragment's `result` is `null`) and $Q_s$ the receiver the source states (`top`
for an arrow). The premise over $L$ is the creation rule's, so leaving the
result out drops a requirement and no check: the result is the claim's, like
any expression's. A parameter written without a type has for $D_j$ the type
TypeScript gives it from its context, which the parser writes
(`closureParamType`): a proposal like any claim, since the body is checked at
$A_j\sqsubseteq_G D_j$ and the closure at $\bigwedge L$ wherever it goes, the
call offering it included. A closure is **offered** each signature binding
more parameters than it does that is expected where it flows: passed where
a callback is offered more parameters (`xs.reduce(acc, null)`), bound under
such an annotation directly or through another binding, returned at such a
result. It is claimed where it is created at that signature beside its own,
and its code is checked at each (`CodeOffers`), the premise over $L$ above
keeping each claimed parameter within its annotation:

```math
\frac{\lambda(\vec x{:}\vec D).t\ \text{flows to a position expecting}\ (R;\vec A)\to B\quad |\vec x|<|\vec A|}
     {(R,\vec A,B)\in L}\ \textsf{offer}
```

A closure is offered a variadic signature too, `process.on(sig, shutdown)`
at `(...args: unknown[]) => void`, when its parameters are among the
signature's fixed ones: $L$ then holds that signature's fixed row
(`offerRows`), and each claimed parameter is within the annotation's as for
any row. A signature binding no more parameters than the closure does is no
offer: a closure binding an optional second parameter, held at a
one-parameter annotation, is not claimed at a two-parameter signature it
later flows to, and its binding there is only that annotation. A `void` result is $\top$, so a closure returning a promise meets it.
No subtyping widens an arrow's parameters: a value typed `() => undefined` is
not a variadic callback, only a closure literal is created at one.

A class is the same case reached from a construct signature. Its methods are
closures with the instance as receiver, and its value is construct-only code
allocating the instance from them. Where the class value is expected at
$\mathsf{new}()\Rightarrow I$ whose instance $I$ has a member $m$ at
$(\vec Q\,\vec U)\to D$ while the class's method $m$ takes $\vec Q$, the method's
closure is claimed at $(C;\vec Q\,\vec U)\to B$ beside its own $(C;\vec Q)\to B$, with
$C$ the class's instance type, and the class value at $\mathsf{new}()\Rightarrow I$
beside $\mathsf{new}()\Rightarrow C$. The creation rule checks the method's
code at both, and `ctorGraph` the constructor's at both, so the instance it
allocates, holding the method as a field of the longer signature, meets $I$'s
member by `CoversByFunction`:

```math
\frac{\Gamma\vdash_G \lambda\vec x.t:\bigl((C;\vec Q\to B)\land(C;\vec Q\,\vec U\to B)\bigr)
      \quad\Gamma,m{:}F\vdash_G \{m{=}m\}:C\quad\Gamma,m{:}F\vdash_G \{m{=}m\}:I}
     {\Gamma\vdash_G \mathsf{class}\{m(\vec x)\{t\}\}:\mathsf{new}()\Rightarrow C\land\mathsf{new}()\Rightarrow I}
```

with $F$ the method's claimed type. Nothing here is a new rule: the premises
are the creation rule, `alloc` and subsumption under each construct signature.

The constructor is offered the same way. Where the class value is expected at
$\mathsf{new}(\vec P\,\vec V)\Rightarrow I$ while its constructor binds
$\vec x{:}\vec D$ with $|\vec x|=|\vec P|$, the class value is claimed at
$\mathsf{new}(\vec P\,\vec V)\Rightarrow I$ beside
$\mathsf{new}(\vec D)\Rightarrow C$ (a resource class constructed with the
request's parameters it ignores: `{ add: Add }` at
`ResourceClass<Collections, Json>`, `new (params: Json) => Resource<Collections>`).
`ctorGraph` checks the code at the first $|\vec x|$ parameters, $\vec P$, and the
source requires each within the constructor's annotation, as for a closure:

```math
\frac{\forall(\vec A,B)\in L.\;|\vec x|\le|\vec A|\;\land\;
        \bigl(\forall j\le|\vec x|.\;A_j\sqsubseteq_G D_j\bigr)\;\land\;
        U,\vec x{:}\vec A_{<|\vec x|},\Gamma\vdash_G b:B
      \qquad U,\vec x{:}\vec D,\Gamma\vdash_G b:C}
     {\Gamma\vdash_G \mathsf{class}(\vec x{:}\vec D)\{b\}:\bigwedge L}
```

with $C$ the class's instance type, its own signature
$\mathsf{new}(\vec D)\Rightarrow C$ among $L$. A constructor needing more than
the offered parameters meets no such signature, and the value holding it is
refused: a class whose constructor calls its parameter's `toString` is not a
`new (params: Json) => Resource<C>`, as a Json object may own that key at any
Json (`invalid-sum-sound-binding-constructor.ts`).

### Certifying inferred call effects

**Definition certification and initial producer inference are implemented;
native overloads and graph composition, including fixed qualified calls, are implemented.** The semantic foundation is
[the qualified arrow equation](SEMANTICS.md#effect-qualified-call-contracts).
Definition checking and application both carry the effect;
changing only the native `map` declaration would introduce a trusted assumption
about client code.

Write $\Gamma\vdash e:B\;!\epsilon$ for safety with the entry-relative
postcondition $Q_\epsilon$ from that equation. Semantically this quantifies over
every eligible budget, world, heap $h$ and environment satisfying $\Gamma$, and
requires `SafePost B (Qε h)` for the instantiated term. It is not a Boolean
producer judgement and does not mean “no write syntax occurs.”
For a fixed-arity closure, the intended introduction rule is schematically

```math
\frac{\Gamma_c,\mathit{this}:R_c,\vec x:\vec A
             \vdash b:B\;!\epsilon}
 {\Gamma_c\vdash\mathrm{closure}(\vec x,b):
             \mathcal F_\epsilon(R_c,\mathrm{ArgsShort}(\vec A),B)}.
```

Here $\Gamma_c$ describes the actual captured values and fixed storage
contracts, not transient captured-cell observations. The premise ranges over
all admitted arguments and future calls. Existing source-annotation checks,
code arity/binding checks and the ordinary body-safety obligation remain.
Parameter defaults execute on invocation, so their effects are included; rest
allocation is allowed. An overload needs the premise for each claimed qualified
signature, and a scheme needs it for every admissible binder assignment, not
just observed instances. These are obligations on the eventual graph certificate,
not permissions to omit those forms from its accounting.

Application uses that type alone. With callee, receiver and arguments already
values, its intended rule is

```math
\frac{\Gamma\vdash f:\mathcal F_\epsilon(R_c,\mathcal A,B)
 \qquad\Gamma\vdash r:R_c\qquad\Gamma\vdash\vec v:\mathcal A}
 {\Gamma\vdash\mathrm{invoke}(f,r,\vec v):B\;!\epsilon}.
```

The effect's entry heap is the heap **after** evaluating the callee, receiver
and actual expressions. Their evaluation may mutate state; it needs its own
composition proof. A call-site rule must not inspect the callback body. Named,
returned and imported callbacks are handled by the same rule whenever their
qualified type is established. Calls inside a checked body in turn consume
their callees' qualified types; higher-order effect requirements are types too.

Forgetting an effect is valid, and manufacturing one by subsumption is not.
The coverage condition, in addition to the usual domain contravariance
and result covariance, is

```math
\frac{R'_c\le R_c\quad\mathcal A'\subseteq\mathcal A\quad B\le B'
 \quad\forall h,h',v.\;Q_\epsilon(h)(h',v)\Rightarrow Q_{\epsilon'}(h)(h',v)}
 {\mathcal F_\epsilon(R_c,\mathcal A,B)
       \le\mathcal F_{\epsilon'}(R'_c,\mathcal A',B')}.
```

In particular, heap-preserving entails unrestricted, but the converse has no
rule. Normalization and substitution must carry the effect per signature.
No per-function global flag can justify a stronger effect on another overload.

For native `map`, the realm's ordinary-construction invariant supplies the
construction premise. A dense receiver and a heap-preserving callback produce
no holes, so the qualified overload can promise the source-readable result
`U[]` at every `U`. The allocation chooses that lifetime store contract; it does
not force the stronger dense contract onto the result's writable store location.
The unrestricted overload promises a sparse result. Both use ordinary selection and application;
there is no body-inspecting `map` rule. `find`/`findIndex` similarly consume a
qualified callback accepting `T`, or an unrestricted one accepting `T | undefined`.
An explicitly submitted stronger effect
claim must fail with a located obligation rather than silently disappear.

The semantic introduction and elimination rules are proved in
`ProgramTyping.callsT_of_graph`, `restsT_of_graphRest`, and `CallEffects.call_safe`.
`GraphCode.codeChecked_sound` checks ordinary safety and the signature's effect
together; a separate unqualified body check cannot introduce a qualified type.
Rest-collecting entries retain their store contract in the checked frame, and
the entry allocation preserves the input heap before the checked body runs.
The effect algorithm ([ExpressionEffects.lean](lean/Verification/Model/Programs/ExpressionEffects.lean)) composes pure computations, required field reads through
invariant cells or readonly views, and fresh object/array allocations. Reads use
the field contract to establish valuehood; arbitrary heap entries are not assumed
to be values. Allocations append locations. `ControlFlow.state_progress` is shared
with ordinary safety, so the additional graph proof has no second set of edge or
branch rules. During expression evaluation, `GraphCode.ReturnsPost` tracks the
normal-return postcondition independently of the safety proof's evolving world.
A caught exception cannot use that postcondition: compositional checking refuses
handlers, while the independent pure-graph rule still admits pure handlers.
Fixed calls use `ExpressionEffects.selectedCall_sound`: the selected application
rule must carry `preservesInputHeap`, and its operands must already be values.
The proof consumes `CallEffects.call_safe`, including padded missing arguments;
a result-subtyping derivation retains the same postcondition. It never inspects
the callee's implementation. Pure immutable lets also compose: $\mathsf{Pure}(a) \land
\mathsf{Pure}(b)$ implies $\mathsf{Pure}(\mathsf{let}\ x=a\ \mathsf{in}\ b)$.
[Purity.lean](lean/Verification/Model/Semantics/Purity.lean) checks purity; its `pure_subst` proves preservation under the value substitution at the
binding step; instantiation respects bound variables at every binder depth.
This covers the nested lets introduced by pure coalescing and logical operands.
Other call forms and nested heap operations remain conservative.

`PromiseWith.combine` retains both premises' effects when combining result
guarantees (the effect meet, so either premise can supply heap preservation). Both promises concern the same admitted calls; determinism gives
the same resulting heap, while the ordinary cross-world compatibility premise
still governs the result type. No effect can arise solely from combining
unrestricted results. `PromiseWith.bound` is the common forwarding proof for
fixed and variadic binding: saving a receiver and prefix changes the admitted
arguments, not the forwarded call's heap guarantee.

This checker is wired into source acceptance, including
`SourceClaimJson.checkJson_safe`. One contract record carries receiver,
arguments, result and required effect through graphs, claims and certificates;
subtyping checks effect implication and substitution preserves it. Ordinary
source annotations remain unrestricted; OCaml proposes preservation for pure
closure bodies, required field reads, fresh allocations and fixed calls to
qualified callees, retaining it through symbolic claims and substitution.
Broader composition remains implementation work. Evidence production adds a
code entry to its search table only after the complete body/effect check passes.
A forged effect thus fails at the defining callable's located typing obligation.
All code certificates remain in the submitted response, and final acceptance
independently checks every one; withholding a search hint cannot hide a failure. Qualified graph claims can
already be submitted and certified through the ordinary source pipeline.

### Parameter initialization order

The source adapter also performs acyclic closure conversion for literal
closures capturing later parameters. `Fragment.parameterOrder` delays only
closure allocations, until their dependencies are initialized; no executing
initializer may read or expose a pending closure. Potentially effectful defaults
keep their relative order. A closure is allocated once and captures initialized
immutable parameters and unchanged outer cell identities. This preserves
sharing and observations up to renaming fresh locations. Cycles and pending
closure exposure are refused. This source-correspondence argument remains in
the trusted adapter; it is not claimed as a Lean proof about JavaScript.
The same schedule orders a code's entry nodes, a default's evaluation among
them. No heap location changes its fixed world type.

## Reading the source

How the trusted front end reads a module, its declarations and the standard
library into the forms above, and the source rules that reading derives. The
decisions and trust behind each are in [DESIGN.md](DESIGN.md); this section
states the rules. Throughout, $⟦T⟧$ is the graph type a
declared or written term lowers to, and $T[\vec p:=\vec U]$ the term with its
binders fixed to ground types.

### Modules and code units

A module is the unit of verification. Its function declarations are hoisted;
its other top-level code (constants, classes, enums, expression statements)
is the initialization unit $I$, run once, in order. With $F$ the module's
functions and $\Gamma_M$ the module's scope:

```math
\frac{\forall f\in F.\;\Gamma_M\vdash f\quad
      (I\neq[\,]\Rightarrow\Gamma_M\vdash I:\mathsf{undefined})\quad
      F\neq\emptyset\lor I\neq[\,]}
     {\vdash M}\ \textsf{module}
```

where $\Gamma_M\vdash I:\mathsf{undefined}$ checks the initialization unit as
a body with no parameters that completes with `undefined`. A module with
neither runs nothing and states no claim; it is refused, so an acceptance
always checked some code. A class's methods are closures its initialization
allocates, so they are checked in that unit. A module function's slot is its
annotated signature; a module constant is read at its annotation or at the
initialization unit's claim for its initializer
([module constants](#mutable-bindings-and-module-constants)). The
initialization unit refuses a call, direct or through module functions, that
can read a constant not yet initialized (`checkInitializationOrder`).

**Claims against annotations.** A claimed type $C$ is within the
annotation's $A$ (`within`) when

```math
\frac{\mathrm{canon}_G(C)\subseteq\mathrm{canon}_G(A)}{C\sqsubseteq_G A}
\qquad
\frac{\mathrm{check}(G,C,A,p)=\mathsf{true}}{C\sqsubseteq_G A},
```

and $C\sqsubseteq_G A$ implies $⟦C⟧_G\subseteq⟦A⟧_G$
(by `check_sound`; the first rule compares rows with identical clauses). A
top-level function's claimed parameter and result types are the
annotation's (`sameMeaning`):

```math
\frac{C\sqsubseteq_G A\quad A\sqsubseteq_G C}{A\simeq_G C},
```

so the claim may replace the annotation. A closure's claimed signatures, a
method's among them, and a class's claimed construct signatures need only be
within the source's, parameter by parameter
([source closures](#source-closures-and-their-annotations)). The body is
checked at each claimed signature, so this comparison is not what makes a
claim sound; it keeps a producer from advertising a signature the source does
not state.

### Imported, ambient and global values

A value the module does not define joins its scope at the type its
declaration states. These rules are assumptions a result is relative to:

```math
\frac{x\ \text{imported, declared at}\ T\ \text{with no binders}}
     {\Gamma(x)=⟦T⟧}\ \textsf{import}
\qquad
\frac{\begin{array}{c}
x\ \text{declared at}\ \forall\vec p\le\vec B.\,T\quad
\text{(certified by its own unit, or imported)}\\
\forall k.\;\vec U_k\ \text{ground},\ |\vec U_k|=|\vec p|,\quad
\forall i.\;G\vdash⟦U_{k,i}⟧\le⟦B_i[\vec p:=\vec U_k]⟧
\end{array}}
{\Gamma(x)=\bigwedge_k⟦T[\vec p:=\vec U_k]⟧}\ \textsf{instances}
```

where $\vec U_1,\ldots,\vec U_m$ are the type arguments the unit's calls of
$x$ name and the conjunction is one callable carrying every instance's
signatures (`Scheme.moduleInstances`); the second rule is sound because each
instance holds of the value. An intersection in the signature whose operands
are ground once the binders are fixed is the graph's meet of those operands
(`meetRow`); one still over a binder at a non-record operand is refused. A
class is read at its construct signature, which `new` meets.

A function declared with overloads $S_1,\ldots,S_n$ ($n>1$) is callable at
exactly those; an implementation's own signature is not callable from outside:

```math
\frac{x\ \text{declared with overloads}\ S_1,\ldots,S_n\ (n>1),\ \text{none generic}}
     {\Gamma(x)=\bigwedge_i⟦S_i⟧}\ \textsf{overloads}
```

Each call is checked against the conjunction, so it is typed by any overload
whose parameters admit its actuals. A generic overload is refused.

An ambient declaration the module writes (`declare function`, `declare
const`, `declare class`) runs nothing and is in scope everywhere, read as an
import is. With $D$ the declarations TypeScript binds $x$ to:

```math
\frac{x\ \text{bound by ambient declarations}\ D\ \text{of the module}}
     {\Gamma(x)=⟦\mathsf{type}(D)⟧}\ \textsf{ambient}
```

where $\mathsf{type}(D)$ is what `import` and `overloads` read. `declare const
k: unique symbol` names a symbol and binds no value. A name that is also an
interface or alias denotes the value in a value position and the other
declaration in a type position.

A value name the module neither imports nor binds is a **global** when
TypeScript binds it to a global variable. A global is read only at the
members and call signatures the module's references select (`selectGlobal`):
every reference reads a member by name or is called; a method's reference
must be called; a `this` result is the selection itself; a generic, optional
or modified method, and a member of a generic base interface, are refused.
With $I$ the annotated interface, $M$ the names read, $O_m$ the overloads
TypeScript resolves the calls of method $m$ to, and $C$ the call signatures
it resolves the calls $x(\ldots)$ to:

```math
\frac{x\ \text{a global variable annotated}\ I\qquad
      M=\{m\mid x.m\ \text{occurs}\}\qquad
      \text{every occurrence of}\ x\ \text{is some}\ x.m\ \text{or a callee}\qquad
      O_m\subseteq\mathsf{overloads}_I(m)\qquad
      C\subseteq\mathsf{calls}_I}
     {\Gamma(x)=⟦\mathsf{sel}_{M,O,C}(I)⟧}\ \textsf{global}
\qquad
⟦I⟧\subseteq⟦\mathsf{sel}_{M,O,C}(I)⟧ .
```

The inclusion is why the rule assumes no more than the declaration: a record
says nothing of keys it does not name, a method's receiver is its host, and a
`this` result is the host. A declaration's `any` is read as `unknown`. A
global both called and read through a method, or both constructed and read
through members, has no clause and is refused. A standard library global is
read through the reviewed overlay ([Library globals](#library-globals)).

In the SKJS test environment a bare import specifier resolves to SKJS's stub
module, and the environment file's constants are globals:

```math
\frac{x\ \text{imported from}\ s\ \text{bare}\qquad
      x\ \text{declared at}\ T\ \text{in}\ \mathsf{stub}(s)}
     {\Gamma(x)=⟦T⟧}\ \textsf{stub}
\qquad
\frac{\mathtt{declare\ const}\ x{:}\,I\in E}
     {x\ \text{is a global variable annotated}\ I}\ \textsf{env}
```

where $\textsf{env}$ feeds $\textsf{global}$.

### One equation per declaration

A declaration is one equation, and a type a unit names is a finite term over
the equations ([RECURSIVE-EQUATIONS §5](RECURSIVE-EQUATIONS.md#5-from-source)).
Lowering (`EquationLowering.source`) makes a head per declaration whose
equation is an object type or has bases, per generic method of such a head,
per source type literal and per generic unit, never per instance: a
generic application $`D\langle\vec U\rangle`$ is the label $`D(\vec U)`$,
and its row is $`D`$'s template instantiated at $`\vec U`$ when a check reads
it, which leaves every application inside unexpanded. So a recursive family
of applications, `Pair<[T, U]>` or `Promise`'s `catch`, is finitely many
heads, and there is no budget, colour or depth: an alias reached again before
a constructor is refused as unguarded, and everything else terminates
because heads are keyed by source occurrence.

An interface declared more than once, as TypeScript merges it, is one
declaration: its first declaration is its identity, and its body holds every
declaration's members, each at its own type. The declarations bind the same
type parameters, name no member twice and state at most one index signature
of each key kind, or the interface is refused:

```math
\frac{\mathtt{interface}\ I\langle\vec X\rangle\ \{\varphi_i;\ \vec\sigma_i\}\ \ (1\le i\le n)\quad
      \mathrm{names}(\varphi_i)\ \text{pairwise disjoint}}
     {⟦I\langle\vec X\rangle⟧=⟦\{\varphi_1\cdots\varphi_n;\ \vec\sigma_1\cdots\vec\sigma_n\}⟧}\ \textsf{interface-merge}
```

with $\varphi_i$ a declaration's fields, methods and index signatures and
$\vec\sigma_i$ its call signatures.

The store a unit is extracted over is the lowering's heads, and extraction
grows it ([EquationStore.lean](lean/Verification/Model/Source/EquationStore.lean)): a union of clauses, a scheme over a closure's
binders and a bounded binder's meet each become a head whose template lifts
the owned parameters it names to arguments. Every unit of a file grows the
one store in turn, and once extraction is done the heads are validated
(`Equations.ofRaw`) and every request is checked over their
`Equations.graph` (`SourceClaimJson.freezePlans`).

#### Generic methods

A declaration's generic method `m<U⃗>` is a head `D.m` of its own, taking
`D`'s parameters and binding `U⃗`: a scheme whose signatures take the
declaration as receiver, lowered as a host-relative member with quantified
signatures whose receivers admit every value (the member bound to its host
is what meets the scheme, [records](POSITIVE-TYPES.md#records)). Its binders
are owned by its application, $`\mathsf{bound}(D.m,\vec A,j)`$, so two
applications of `D` at different arguments bind different labels, and two
members of different declarations do too. Such members relate by quantified
coverage up to renaming the target's binders to the source's
([RECURSIVE-EQUATIONS §4.1](RECURSIVE-EQUATIONS.md#41-quantified-signatures),
`SchemeRenames`): as many binders, of the same kinds, each target bound
within the source's, and the source's signatures covering the target's
renamed. Members binding different numbers of binders are not related. A generic
member of a library prototype (`ArrayProto`'s `forEach`, whose receiver is an
array of its element binder) stays a readonly view of its scheme. A rest
typed by one of the method's binders makes it a pack parameter, bounded by
its element pack. A value binder $`p`$ with a declared bound $`B_p`$
establishes a parameter's bound $`B`$ through that one:

```math
\frac{p\ \text{a value binder}\quad G\vdash_c B_p\le B}
     {p\ \text{establishes}\ B}\ \textsf{binder-bound}
```

A binder the source spells by its name, in an annotation or a claim, is its
name's placeholder until the unit or closure that binds it is extracted: a
generic unit's binders are the owned parameters of its head
(`EquationLowering.enterUnit`), a generic closure's those of the scheme its
claim states (`Scheme.schemeRowOf`), and each annotation and claim inside
reads the name as that parameter (`EquationStore.rebind`).

#### Binders met with ground types

An intersection of a value binder with ground types, `V & DepSafe`, is a
meet label ([RECURSIVE-EQUATIONS §2.2](RECURSIVE-EQUATIONS.md#22-meaning)),
whose row is the [meet row](POSITIVE-TYPES.md#parameter-and-scheme-rows)
$p\sqcap\vec c$. Lowering an intersection (`meetOf`) distributes it over its
operands' unions, one meet label per choice; on ground operands:

```math
\frac{A_k=[p],\ p\ \text{a value binder}\qquad
      \forall i\ne k.\ A_i\ \text{of clause rows}}
     {⟦A_1\mathbin{\&}\cdots\mathbin{\&}A_n⟧=
      [\,p\sqcap\mathsf{meet}(A_{i\ne k})\,]}\ \textsf{binder-meet}
\qquad
\frac{\forall i.\ A_i\ \text{of clause rows}}
     {⟦A_1\mathbin{\&}\cdots\mathbin{\&}A_n⟧=
      [\,\mathsf{meet}(A_1,\ldots,A_n)\,]}\ \textsf{meet}
```

```math
\frac{\vec p\ \text{the value binders among the}\ A_i\ \text{and the parameters of their meet rows},\ |\vec p|\ge 2\ \text{or a meet row among them}\qquad
      \vec c\ \text{the meet of the other operands' and those rows' clauses, or}\ \top}
     {⟦A_1\mathbin{\&}\cdots\mathbin{\&}A_n⟧=
      [\,p_1\sqcap p_2\cdots\sqcap\vec c\,]}\ \textsf{binders-meet}
```

where $\mathsf{meet}$ is the operands' clauses met pairwise and folded from
the right: `meetLists` ([conjunction](POSITIVE-TYPES.md#conjunction-and-normalization)),
except that a record of invariant fields met with a function type is the
callable carrying them (`sourceMeetLists`, [below](#intersections-of-functions-and-records)),
and any other intersection (a scheme, a union holding a binder) is refused
rather than an operand being dropped. A function's own annotation lowers its
intersections so (`annotationClaim`), each binder read as the row the unit
reads it as, its parameter row met with a ground bound or with the binder
bounding it (`binderRows`): `T & U`, `T & "fixed"`, `T & object` and
`A<U> & B<V>` are meet rows or meets of application rows over the binders'
rows. An operand whose row is not yet filled, a declaration being lowered or
a recursive application met inside its own equation
(`TreeNode<T> & TreeLeaf<T>` in `TreeLeaf<T>`'s field), makes the meet a row
of its own that waits for it (`waitingMeet`), filled once every operand is
(`settle`); a nullary declaration an intersection names is lowered first, so
the declarations' order does not matter. No lowering ends with a meet left
waiting. A meet row is below each of its parameters, so
it establishes what each does. At an instance $p_1:=U_1,\ldots,p_k:=U_k$ it
means $\mathsf{meetLists}(G(U_1),\ldots,G(U_k),\vec c)$ (`meetOk`, the meet
folded left to right, or in the reverse order), which is exactly what lowering
the intersection at $\vec U$ gives. A producer names a meet it does not compute by
an intersection label in its claims ([`{"meet": ...}`](SOURCE-CLAIMS.md#encoding)),
whose row Lean fills with `meetRow`.

A generic body's bounded binder is read the same way, as the meet of its
parameter row and its bound, and a binder bounded by another, `U extends T`,
as the meet of the two, $p_U\sqcap p_T\sqcap\vec c$ with $T$'s clauses or
$\top$ (`SourceTypes.dependentMeet`), which is below $T$ by its parameters
([`meetBelow`](POSITIVE-TYPES.md#covered-pairs); [generic
bodies](#overloads-polymorphism-and-binding)). Any other bound naming a binder
leaves the parameter row alone.

### Explicit type arguments

A method call may state its instance, `o.m<A₁,…,Aₖ>(…)`. The arguments
instantiate the member's binders in order, its own leading; binders past them
(an `ArrayProto` member's element `T`, listed last) are fixed by the receiver
and actuals. Lean reads the member's scheme row $S$ from the receiver's
contract (a quantified member's scheme, or a view's), finds the instance map $\theta$ relating $S$ to the read's claimed
arrows $M$, checks it (`checkInstArrsUsing`, sound by `checkInstArrsUsing_sound`) and
requires each explicit argument to mean what $\theta$ gives its binder:

```math
\frac{o:O\quad \mathsf{field}_G(O,m)=S=[\forall\vec p.\Sigma]\quad
      \mathsf{checkInstArrs}(G,S,M,\theta)=\mathsf{true}\quad
      \forall i\le k.\;\theta(p_i)\simeq_G A_i}
     {o.m\langle A_1,\ldots,A_k\rangle(\vec a)\ \text{is called at its stated instance }M}.
```

A plain call or `new` of a generic module value, or a local quantified
closure, states its instance alike (`Scheme.explicitInstance`):

```math
\frac{f\ \text{generic over}\ p_1,\ldots,p_n\quad
      \text{the call's claimed instance}\ \sigma\quad
      k\le n\quad
      \forall i\le k.\;\sigma(p_i)\simeq_G⟦A_i⟧}
     {f\langle A_1,\ldots,A_k\rangle(\vec a)\ \text{is called at its stated instance}\ \sigma},
```

with $\simeq_G$ inclusion both ways by certified subtyping. Both rules only
refuse: acceptance rests on the call's typing, so safety does not depend on
them; they make a stated instance honoured. The instance's bounds are checked
as for any call. A declaration's defaults for method binders are not read.

### Classes

A class declares its instance type in the declaration graph, and its value is
a statement of the initialization unit: method closures, the prototype object
`C.[[prototype]]` holding them (allocated once; not allocated when it holds
nothing of its own that `instanceof` tests), then the class value,
construct-only code. Its own name inside its body is `C.[[self]]`
([`class-self`](#mutable-bindings-and-module-constants)). Static members are
module bindings of their own, `static C.x`, after the class; a static read
`C.x` is that binding where TypeScript binds it to the member (`staticReads`).
A static block runs where it stands among the static fields, as the closure
of its statements called at once, reading no `this`:

```math
\mathtt{static}\ \{\ \vec s\ \}\;\equiv\;\mathsf{const}\ \textit{b} = (()\Rightarrow\{\ \vec s\ \})()
```

with $\textit{b}$ a binding no source spells. An `async` method is a method
whose body reads as an async function's, its returns and `await`s the
[async intrinsics](#async-functions-and-await).

**Private names.** A private name `#x` is a key no code outside its class
spells: the declaration reader lists it as a symbol of its own, identified by
the member declaring it ($\sigma_{C.\#x}$), as it lists a `unique symbol`
constant, and TypeScript binds each `#x` of the class body to that member. A
private field is an own key of each instance, allocated with the others
(entries $\sigma_{C.\#x}\mapsto e$ of $\varphi_0$); a private method is held
by the prototype under its key, as a method under its name; a static one is
a static binding `static C.#x`. So `o.#x`, `o.#x = e` and `o.#m(ā)` are the
named read, write and method call at $\sigma_{C.\#x}$, and a copy
(`{...o}`) takes no private slot, in JavaScript as in the model. JavaScript
throws where `o` holds no slot of its own; the model reads `o.#x` along the
prototype chain as any key, where only an object inheriting from an instance
differs, and there JavaScript throws, which safety admits.

The instance type states each member as what it is at run time: a field
`f: T`, `f!: T` or `readonly f: T` a required field or view, `f?: T` the
optional field `f?: T | undefined`, a parameter property `p: T` a field and
`p?: T` the optional field `p?: T | undefined`. An optional member is
TypeScript's `T | undefined` there, not the exact `f?: T` (absent or a `T`)
the pipeline reads elsewhere: a class field is defined on every instance, at
`undefined` where nothing assigns it. With $\varphi_0$ the entries, in member order, of
the prototype key ($\texttt{[[proto]]} \mapsto C.\texttt{[[prototype]]}$,
for a class with methods), the initialized fields ($f\mapsto e_f$) and the
parameter properties ($p\mapsto p$), $U$ the fields without an initializer
and $T_f$ each field's annotation, `constructor(x̄) { s̄ }` is
$\mathsf{class}(\vec x).\,\mathcal{C}(\vec s,\varphi_0,\varnothing)$ where

```math
\begin{aligned}
\mathcal{C}(\varepsilon,\varphi,A) &= \mathsf{alloc}(\varphi,\ \overline{f\mapsto\mathsf{undefined}}^{\,f\in U\setminus A})\\
\mathcal{C}(\texttt{this.}f\texttt{ = }e;\ \vec s,\varphi,A) &= \mathcal{C}(\vec s,\ \varphi,f\mapsto e,\ A\cup\{f\})
  && f\in U\setminus A\\
\mathcal{C}(\texttt{if (}c\texttt{) }\{\vec t\}\texttt{ else }\{\vec u\},\varphi,A) &=
  \beta(\varphi)\,;\ \mathsf{if}\ c\ \mathsf{then}\ \mathcal{C}(\vec t,\varphi',A)\ \mathsf{else}\ \mathcal{C}(\vec u,\varphi',A)
  && \text{last, assigns a field}\\
\mathcal{C}(s;\ \vec s,\varphi,A) &= \beta(\varphi)\,;\ s\,;\ \mathcal{C}(\vec s,\varphi',A)
  && \text{otherwise}
\end{aligned}
```

and `this` occurs in no $e$, $c$ or $s$. $\beta(\varphi)$ binds each entry
$f\mapsto e$ that is not a literal or already bound as `const this.f: T_f =
e`, in order, a name no source binding spells, and $\varphi'$ reads `this.f`
there, so every value is evaluated where JavaScript evaluates it. The
allocation is checked like any other: a field without an initializer holds
`undefined` until assigned, so `f!: T` holds exactly when the constructor
assigns `f` on every path, and `f?: string` left unassigned holds its
`undefined`. A
derived class's constructor is the [derived form](#derived-source-forms) over
this one; an override must be sound, since the derived class's declared type
is its own members and its base's.

A generic class's binders are its declaring unit's parameter rows, one per
spelling, so a generic class may extend a generic base exactly at the base's
own binders, which it declares too: `class D<T> extends B<T>`. The base's
construction, fields and methods are then at the rows the derived class's
are, and the derived form is the non-generic one. Its instance type
$D\langle T\rangle$ is its application row, as a class with methods is,
holding its own members met with those of $B\langle T\rangle$'s row. A base at
other arguments (`extends B<number>`) is refused: its construction would have
to be instantiated there.

### Library types

Write $⟦\tau⟧$ for the source term the declaration reader
gives type syntax $\tau$ (`typeTerm`), and $\mathit{lib}(N)$ when every
declaration TypeScript binds $N$ to is in a standard library file:

```math
\frac{\mathit{lib}(\mathtt{Array})}
     {⟦\mathtt{Array}\langle T\rangle⟧=⟦T[\,]⟧}
\qquad
\frac{\mathit{lib}(\mathtt{ReadonlyArray})}
     {⟦\mathtt{ReadonlyArray}\langle T\rangle⟧=⟦\mathtt{readonly}\;T[\,]⟧}
\qquad
\frac{\mathit{lib}(\mathtt{Function})}{⟦\mathtt{Function}⟧=\mathsf{callable}}
```

with $\mathsf{callable}$ the union of `arrs [] []` and `ctors [] []`
([functions and classes](POSITIVE-TYPES.md#functions-and-classes)); `object`
is `refs [] [] []` with $\mathsf{callable}$, and `{}` adds every primitive but
`null` and `undefined`. A mapped type whose value does not name its key is
expanded where its key is known, with $\mathsf{key}(\texttt{"}s\texttt{"})=s$,
$\mathsf{key}(n)=\mathsf{ToString}(n)$ and $m$ its modifiers:

```math
\frac{P\notin\mathrm{fv}(V)\quad⟦K⟧=\lambda_1\mid\cdots\mid\lambda_n\ \text{literals}\quad(n\ge0)}
     {⟦\{[P\ \mathtt{in}\ K]^m\colon V\}⟧=\{\mathsf{key}(\lambda_1)^m\colon⟦V⟧;\ \ldots;\ \mathsf{key}(\lambda_n)^m\colon⟦V⟧\}}
\qquad
\frac{P\notin\mathrm{fv}(V)\quad\mathtt{string}\in⟦K⟧\subseteq\mathtt{string}\cup\mathtt{number}\cup\text{literals}\quad\mathtt{?}\notin m}
     {⟦\{[P\ \mathtt{in}\ K]^m\colon V\}⟧=\{[k\colon\mathtt{string}]^m\colon⟦V⟧\}}
```

`number` without `string` is a number index and `symbol` a symbol index
beside the remaining literals' fields; an optional one, a type parameter or
any other key is refused. The keys are the union TypeScript computes for $K$
([computed types](#computed-types)). A library alias whose equation is a
mapped type is that type at the reference's arguments:

```math
\frac{\mathit{lib}(L)\quad L\langle\vec X\rangle=\{[P\ \mathtt{in}\ K]^m\colon V\}}
     {⟦L\langle\vec A\rangle⟧=
      ⟦\{[P\ \mathtt{in}\ K[\vec A/\vec X]]^m\colon V[\vec A/\vec X]\}⟧}
```

so `Record<"a" | "b", V>` has both fields required and `Record<string, V>` is
the writable string index. An interface's `extends` clauses are the meet of
its own clauses with each base's, its own members first (`inheritRows`,
[conjunction](POSITIVE-TYPES.md#conjunction-and-normalization)); a source
intersection has the same meaning (`meetRow`).

An annotation's intersection of records is the one meet, with $\varphi_i$
the invariant and $\psi_i$ the readonly fields of $R_i$ (any other field is
refused):

```math
\frac{\forall i.\ ⟦R_i⟧=\mathsf{Ref}(\varphi_i;\psi_i)}
     {⟦R_1\mathbin{\&}\cdots\mathbin{\&}R_n⟧=
      \mathsf{Ref}(\varphi_1\cdots\varphi_n;\,\psi_1\cdots\psi_n)}\ \textsf{record-meet}
```

with each list sorted and deduplicated (`Fragment.cellConjunction`); it is
exact by `recT_append`.

**Signatures.** A type literal or an interface whose members are call
signatures only is the function type they state, and one of construct
signatures only the constructor type, several signatures being overloads of
the one value; call signatures beside writable fields are the callable
carrying them ([callable-meet](#intersections-of-functions-and-records)).
With $⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧$ the signatures' fixed ones $L$ and
variadic ones $S$, each receiver `top` unless a `this` parameter states it,
and $\varphi$ writable fields:

```math
\frac{⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧=L;S}
     {⟦\{\,\sigma_1;\ \ldots;\ \sigma_n\,\}⟧=\mathsf{arrs}(L;S)}\ \textsf{call-literal}
\qquad
\frac{⟦\sigma_1⟧,\ldots,⟦\sigma_n⟧=L;S}
     {⟦\{\,\sigma_1;\ \ldots;\ \sigma_n;\ \varphi\,\}⟧=\mathsf{callable}(\varphi;L;S)}
\qquad
\frac{⟦\mathtt{new}\,\sigma_1⟧,\ldots,⟦\mathtt{new}\,\sigma_n⟧=L;S}
     {⟦\{\,\mathtt{new}\,\sigma_1;\ \ldots;\ \mathtt{new}\,\sigma_n\,\}⟧=\mathsf{ctors}(L;S)}\ \textsf{construct-literal}
```

Construct signatures beside other members, which describe a class value's
statics, are refused ([model limits](DESIGN.md#model-limits)). A rest
parameter over a union of tuples of required positions is one signature per
tuple, all at the signature's result, which a value meets by meeting every
one; the library's `next(...[value]: [] | [TNext])` is `next()` and
`next(value: TNext)`:

```math
\frac{⟦R⟧=[\vec A_1]\mid\cdots\mid[\vec A_n]}
     {⟦(\vec P,\ \ldots r\colon R)\colon B⟧=(\vec P\,\vec A_1)\colon B;\ \ldots;\ (\vec P\,\vec A_n)\colon B}\ \textsf{rest-tuples}
```

#### Intersections of functions and records

A record type's clause is a plain object, which no function is, so the
model's meet of a function type and a record is empty. TypeScript's record
type also holds functions with those properties, and its intersection with a
function type is exactly those functions: the callable with the record's
fields (`sourceMeetLists`), as an interface with a call signature and fields
is. With $\varphi$ invariant fields and no view, optional field, method or
bound:

```math
\frac{⟦F⟧\ni\mathsf{arrs}(L;S)\quad ⟦R⟧\ni\mathsf{Ref}(\varphi)}
     {⟦F\mathbin{\&}R⟧\ni\mathsf{callable}(\varphi;L;S)}\ \textsf{callable-meet}
\qquad
\frac{⟦F⟧\ni\mathsf{callable}(\psi;L;S)\quad ⟦R⟧\ni\mathsf{Ref}(\varphi)}
     {⟦F\mathbin{\&}R⟧\ni\mathsf{callable}(\varphi\psi;L;S)}
```

An interface's `extends` clauses meet so too. A record with a readonly or
optional field, a method or an index met with a function type has no clause:
that pair is dropped, as the model's meet drops it (so `{}`'s function arm
meets such a record as nothing, and its record arm as the record), and an
intersection it leaves with nothing is refused for it. An array owns its store, so a function is
never one, and their meet is empty. An interface stating no member of its own
is its bases' meet (`interface Callback extends Function {}` is `Function`).
An intersection whose meet is empty (`string & { a: number }`, a function and
an array, `number[] & { map: number }`) is refused rather than verified
vacuously: TypeScript keeps such a type (a branded primitive), which no value
of the model inhabits.

### Computed types

`typeof x`, `keyof T`, `T[K]`, template literal types and intersections of
primitives and literals mean the type TypeScript's checker computes
(`computed-types.mts`). With $\mathit{ts}(\tau)$ the checker's type of the
node $\tau$ and $\mathsf{lits}(t)$ for $t$ as a union of literals and
primitive families when it is exactly one:

```math
\frac{\mathsf{lits}(\mathit{ts}(\tau))=U}{⟦\tau⟧=U}\ \textsf{computed}
\qquad
\frac{x\ \text{declares}\ x\colon\sigma\quad\mathit{ts}(\sigma)=\mathit{ts}(\mathtt{typeof}\ x)}
     {⟦\mathtt{typeof}\ x⟧=⟦\sigma⟧_{x}}
\qquad
\frac{x\ \text{a function or class value, not generic, no statics}}
     {⟦\mathtt{typeof}\ x⟧=\mathsf{type}(x)}
```

where $⟦\sigma⟧_x$ reads $\sigma$ where $x$ is declared and
$\mathsf{type}(x)$ is what an import of $x$ reads. An indexed access projects
$⟦T⟧$ at each key of $\mathsf{lits}(\mathit{ts}(K))$: a
record's field (with `| undefined` where optional), an array's element at
`number`, a tuple's position, a union's parts, an intersection's operands'
members met, an alias through its equation (a generic one's at the
reference's arguments), a named type's member through its annotation under
the same identity premise.

A **computed alias** is a generic alias whose equation is a computed form or
an application of another computed alias (`computedAlias`): `type
ElementOf<T> = T[number]`, `type Keys<T> = keyof T`. Over its parameters it
is known only at an application, so it has no equation of its own, and an
application of it is a computed type, evaluated where it is written, its
equation read with the parameters as the arguments:

```math
\frac{A\langle\vec X\rangle=\tau\ \text{a computed alias}\quad
      \mathsf{lits}(\mathit{ts}(A\langle\vec\sigma\rangle))=U}
     {⟦A\langle\vec\sigma\rangle⟧=U}
\qquad
\frac{A\langle\vec X\rangle=\tau\ \text{a computed alias}\quad
      \mathsf{lits}(\mathit{ts}(A\langle\vec\sigma\rangle))\ \text{undefined}}
     {⟦A\langle\vec\sigma\rangle⟧=⟦\tau⟧_{\vec X:=⟦\vec\sigma⟧}}\ \textsf{computed-alias}
```

where $⟦\tau⟧_{\vec X:=\vec S}$ evaluates $\tau$ by the
rules here with each $X_i$ read as $S_i$: an indexed access projects its
argument, and `keyof` of a type literal is the union of its property names'
string literals (`keysOf`), so `ElementOf<readonly E[]>` is `E` and
`Keys<{ good: E }>` is `"good"`. A `typeof` of a constant without an
annotation is the type TypeScript infers for its initializer where that is a
union of literals and primitives or an object literal's record of such
types, each property a writable field and each index a spread copied, read
from the checker (`inferredTerm`):

```math
\frac{\mathtt{const}\ x=e\quad \mathit{ts}(\mathtt{typeof}\ x)=\{\overline{k_i\colon t_i};\ \overline{[\theta_j]\colon u_j}\}\ \text{from}\ e\text{'s literal}\quad
      \forall i.\ ⟦t_i⟧\ \text{inferred}}
     {⟦\mathtt{typeof}\ x⟧=\{\overline{k_i\colon⟦t_i⟧};\ \overline{[\theta_j]\colon⟦u_j⟧}\}}\ \textsf{typeof-inferred}
```

Refused: a template literal type with a `${string}` or `${number}` hole; a
form over a function's own type parameter (`keyof T`, `T[number]` with `T`
the function's binder), which denotes a function of the type an instance
names, not of the values a parameter row stands for; `keyof` with a
unique-symbol key, which no type of the fragment names; `typeof` of a binding
TypeScript infers another type for (a `let`, a method, a `const` assertion);
`typeof C` of a class with statics.

### Index signatures

An index signature is a view (and, mutable, a writable contract) over a
[key class](POSITIVE-TYPES.md#records). The reader states:

```math
⟦\{[k\colon\mathtt{number}]^m\colon V\}⟧=\mathsf{Dict}(\mathsf{numeric}{:}V)
\qquad
⟦\{[k\colon\mathtt{symbol}]^m\colon V\}⟧=\mathsf{Dict}(\mathsf{symbols}{:}V)
\qquad
⟦\{[k\colon\mathtt{string}]^m\colon S;\ [k\colon\mathtt{number}]^m\colon N\}⟧=
  \mathsf{Dict}(\mathsf{strings}{:}S,\ \mathsf{numeric}{:}N)
```

An index over a union of key types is one per member; one over `string |
number`, or a number index at the string index's contract, is the string
index alone. A named key reads through an index whose class surely admits it,
at $V\mid\mathtt{undefined}$ (`readDict`); a computed `string`, `number` or
`symbol` key through an index over a class containing its keys (`indexDict`),
the narrower number index where both admit it. No write through an index is
typed. A numeric property name is the key its value's `ToString` spells
(`numericKey` in `type-term.mts`), and a number key of a receiver claimed only
at records is the [named access](#derived-source-forms) of that key.

### Prototype contracts

`ArrayProto`, `StringProto`, `NumberProto`, `BigIntProto` and `BooleanProto`
are records of readonly members read from TypeScript's `ReadonlyArray`/`Array`
and `String`, `Number`, `BigInt`, `Boolean` through the overlay
(`array-prototype.mts`): only listed members, each read from the declaration
whose text is the reviewed one, at the receiver the entry names (`readonly
T[]` for `ReadonlyArray`, `T[]` for a mutator, the primitive for a
primitive's member), without dropped parameters. An entry may state its
signature family instead, with $\omega$ the entry of member $m$ of prototype
$p$, and $R_j$ its reviewed receiver (defaulting to $p$):

```math
\frac{\omega\in\Omega_p\quad \omega.\mathit{text}=\mathsf{text}(m)\quad
      \omega.\mathit{stated}=[(R_j,\vec P_j,Q_j)]_{j=1}^n\quad n>0}
     {⟦m⟧_\omega=\bigcap_{j=1}^n
       (\mathsf{this}:R_j,\ \vec P_j)\Rightarrow Q_j}\ \textsf{proto-stated}
```

The reviewed overlay can restrict quantified binders (`bounds`) and weaken a
native's promised result (`result`). These specify trusted natives; source
annotations are still translated in full. `join` bounds `T` to the conversion
contract below,
unrestricted `find`/`findIndex` callbacks receive `T | undefined`, and unrestricted
`map` callbacks produce a sparse result. Qualified overloads require a certified
`preservesInputHeap` callback and respectively pass `T` or promise a dense result.
Source `U[]` requires readability; the fresh qualified map result may choose that
lifetime contract even when its initial contents are physically dense.

Native array results rely on the ordinary-construction invariant: an array owns
neither `constructor` nor any key declared by `ArrayProto`; the host keeps the
standard array constructor/species behavior. The same own-key exclusion is used
in array lowering and the realm invariant (`RequestJson.arrayExcludedKeys`).
Thus `filter` and `slice` can promise ordinary arrays, and certified callback effects
justify the dense `map` overload.

**Standard array conversion.** Let P be the primitive types, including
`undefined`, and define the regular recursive contract

```math
D=\mu X.\;P\;\cup\;\mathsf{ReadonlyArray}(X).
```

This is the synthetic declaration `StringConvertible`, lowered by the ordinary
recursive declaration mechanism. The array realm excludes own `toString`,
`join` and `Symbol.toPrimitive`; the prototype contract states an optional
`Symbol.toPrimitive` field whose only possible value is `undefined`. Standard
prototype behavior is required of external code too. Thus string conversion of
an admitted array reaches standard `toString`, which calls standard `join`,
whose element conversions meet the same D contract. No client conversion hook
is called. Primitives may throw (a symbol, for example); termination is not
claimed for recursive arrays. Without a library identity for `Symbol.toPrimitive`,
D conservatively contains primitives only.

`join` and `toString` each quantify `T` with bound `T ≤ D`. For `sort`, let
A(T) be the mutable array contract, V(D) its readonly view at D, and C(T) the
comparator `(T,T) → number`.
Its one scheme offers the intersection:

```math
\forall T.\quad
 ((\mathsf{this}:A(T),\ C(T))\Rightarrow A(T))
 \;\cap\;
 ((\mathsf{this}:A(T)\cap V(D),\ \mathtt{undefined})\Rightarrow A(T)).
```

These are audited native contracts, consumed by the existing quantified call
and subtype rules, not new calculus axioms or a proof of ECMA-262's algorithms.
Custom array conversion is deliberately outside the admitted language: it adds
dispatch and alias obligations without helping the motivating framework code.
`native-array-conversion` and the unchanged tuple-sort examples verify;
`invalid-array-conversion-override` refuses the conflicting own-key contract.
Runtime controls show why accepting externally overridden hooks would invalidate
the assumption. See [ECMA-262](REFERENCES.md#ecma-262), `ToPrimitive`,
`Array.prototype.toString` and `CompareArrayElements`.

Omitting the comparator supplies `undefined`, so it needs the second receiver
contract. A comparator on arbitrary objects needs only the first. These are
ordinary scheme instantiation and arrow application; the result is the same
mutable array contract throughout. Selecting one signature never erases the
other signature or its receiver condition from the declared scheme.

`Set<T>`, `Map<K, V>` and `Date` are read through the same mechanism
(`interfaceOverlay`), as an interface with only its listed members:

```math
\frac{\mathit{lib}(I)\quad \Omega_I=[\omega_1,\ldots,\omega_n]\quad
      m_j\ \text{the member of}\ I\ \text{with}\ \mathsf{text}(m_j)=\omega_j.\mathit{text}}
     {⟦I\langle\vec X\rangle⟧_\Omega=\{k_1:⟦m_1⟧_{\omega_1};\ \ldots;\ k_n:⟦m_n⟧_{\omega_n}\}}\ \textsf{library-interface}
```

a supertype of the declared interface. $⟦m⟧_\omega$ drops
`thisArg`, reads a `this` result as the receiver, and reads a declared
iterator result as `Iterator<T>`, which it extends. A property is a readonly
view. A string's own `length` and indices are the calculus's `lenStr` and
`elemStr`, never the prototype's; `s[i]` is `string | undefined`.

### Library globals

A standard library global is read only through the reviewed overlay
(`library-globals.mts`), one entry per signature, with exactly the
declaration text it was reviewed against. With $s$ a selected signature,
$\Omega$ the overlay and $\omega$ an entry:

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega.\mathit{global}=x\quad \omega.\mathit{text}=\mathsf{text}(s)\quad
      \omega\ \text{admits}\ (i, S)}
     {⟦s⟧_\Omega=⟦s⟧\bigl[\,p_i:=S\,\bigr]}\ \textsf{library-global}
```

and an entry without `admit` reads $s$ as declared. Replacing a parameter by
a subset gives a supertype of the declared signature. An entry may state the
signature the host meets (`stated`), for a construct signature, a method (a
scheme over its binders, host-relative) or a property (its type the result):

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad \omega.\mathit{global}=x\quad
      \omega.\mathit{text}=\mathsf{text}(s)\quad
      \omega.\mathit{stated}=\forall\vec X.\ \mathsf{new}(\vec P)\Rightarrow R\quad
      |\vec a|\le|\vec P|\ \text{for each}\ \mathsf{new}\ x(\vec a)\ \text{selecting}\ s}
     {⟦s⟧_\Omega=\forall\vec X.\ \mathsf{new}(\vec P)\Rightarrow R}\ \textsf{library-construct}
```

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad \omega=(x,\ m,\ \mathsf{text}(s),\ \mathsf{stated}\ \forall\vec X.\ (\vec P)\Rightarrow R)\quad
      |\vec a|\le|\vec P|\ \text{for each}\ x.m(\vec a)\ \text{selecting}\ s}
     {⟦s⟧_\Omega=\forall\vec X.\ (\mathsf{this}:\mathsf{self},\ \vec P)\Rightarrow R}\ \textsf{library-stated}
```

Overloads stated alike are one signature. A statement may name a library
interface (`Set<T>`, read through [its overlay](#prototype-contracts)) or a
declaration no library has, which joins the document with the entry:

```math
\mathsf{JsonValue}=\mathsf{null}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\{\mathsf{readonly}\ [k:\mathsf{string}]:\mathsf{JsonValue}\}
```

(`JSON.stringify`'s parameter). An entry may read a member as a test of the
calculus (`test`), and the variable's declaration as the right operand of
`instanceof`:

```math
\frac{\mathit{lib}(\mathtt{Array})\quad \omega\in\Omega\quad
      \omega=(\mathtt{Array},\ \mathtt{isArray},\ \mathsf{text}(s),\ \mathsf{test}\ \mathsf{isArray})}
     {⟦\mathtt{Array.isArray}(e)⟧=\mathsf{test}\ \mathsf{isArray}\ ⟦e⟧}\ \textsf{library-test}
\qquad
\frac{\mathit{lib}(\mathtt{Array})\quad \omega\in\Omega\quad
      \omega=(\mathtt{Array},\ \cdot,\ \mathsf{text}(d),\ \mathsf{test}\ \mathsf{isArray})}
     {⟦e\ \mathtt{instanceof}\ \mathtt{Array}⟧=\mathsf{test}\ \mathsf{isArray}\ ⟦e⟧}\ \textsf{library-instanceof}
```

The branch rule is the tag rule on $\mathsf{isArray}$
([SEMANTICS](SEMANTICS.md#operational-language)); the declared guard `arg is
any[]` is not read. An entry may read a member, or a construct signature, as
a call of an [intrinsic](#async-functions-and-await) stating the same step
(`intrinsic`), instantiated at each call by $\textsf{instances}$:

```math
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega=(x,\ m,\ \mathsf{text}(s),\ \mathsf{intrinsic}\ \iota)}
     {⟦x.m(\vec e)⟧=\iota(⟦\vec e⟧)}\ \textsf{library-intrinsic}
\qquad
\frac{\mathit{lib}(x)\quad \omega\in\Omega\quad
      \omega=(x,\ \cdot,\ \mathsf{text}(s),\ \mathsf{intrinsic}\ \iota)\quad s\ \text{a construct signature}}
     {⟦\mathsf{new}\ x(\vec e)⟧=\iota(⟦\vec e⟧)}\ \textsf{library-construct-intrinsic}
```

`Promise.resolve(v)` is `%AsyncReturn%(v)`, `Promise.resolve()` is
`%AsyncComplete%()`, `Promise.all` is `%PromiseAll%`, `Promise.reject` is
`%PromiseReject%` and `new Promise` is `%NewPromise%`.

**Symbol keys.** A computed key `[k]`, in a type, a literal or a read,
names a `const k: unique symbol` (or a readonly property so declared), and
the symbol it names is what made the constant: `Symbol()` makes a fresh one,
the declaration's own, and `Symbol.for(s)`, with $s$ a string literal, the
registry's symbol for $s$, which every constant made so holds. A declared
constant (`declare const`) holds its own. Any other initializer is refused,
the symbol it holds not being known:

```math
\mathrm{sym}(k)=\begin{cases}
\sigma_k & k=\mathtt{Symbol}(\ldots)\ \text{or}\ \mathtt{declare\ const}\ k\\
\sigma_{\mathtt{for}\,s} & k=\mathtt{Symbol.for}(s)
\end{cases}
```

So two constants made by `Symbol.for` of one string name one key, and a
type naming both names that key twice, which is refused, though TypeScript
types each constant a distinct `unique symbol`.

### Async functions and await

The parser writes each async form as a call of an intrinsic, a value named
`%…%` that no source identifier spells (`intrinsics.mts`):

```math
\begin{aligned}
⟦\mathsf{await}\ e⟧&=\mathtt{\%Await\%}(⟦e⟧)\\
⟦\mathsf{return}\ e⟧_{\mathsf{async}}&=\mathsf{return}\ \mathtt{\%AsyncReturn\%}(⟦e⟧)\\
⟦\text{completion}⟧_{\mathsf{async}}&=\mathsf{return}\ \mathtt{\%AsyncComplete\%}()
\end{aligned}
```

in an async function, arrow or function expression's own body. The
declaration reader lists the intrinsics among the module's values, with $P$
the primitives (the values that are never thenables):

```math
\begin{aligned}
\mathtt{\%Await\%}&:\forall T,\,U\le P.\ (\mathit{value}:\mathsf{Promise}\langle T\rangle\mid U)\Rightarrow T\mid U\\
\mathtt{\%AsyncReturn\%}&:\forall T\le P,\,U\le P.\ (\mathit{value}:T\mid\mathsf{Promise}\langle U\rangle)\Rightarrow\mathsf{Promise}\langle T\mid U\rangle
\qquad P=\mathsf{null}\mid\mathsf{undefined}\mid\mathsf{boolean}\mid\mathsf{number}\mid\mathsf{string}\mid\mathsf{bigint}\mid\mathsf{symbol}\\
\mathtt{\%AsyncComplete\%}&:()\Rightarrow\mathsf{Promise}\langle\mathsf{void}\rangle\\
\mathtt{\%PromiseAll\%}&:\forall T.\ (\mathit{values}:\mathsf{readonly}\ \mathsf{Promise}\langle T\rangle[\,])\Rightarrow\mathsf{Promise}\langle T[\,]\rangle\\
\mathtt{\%PromiseReject\%}&:\forall T.\ (\mathit{reason}:\mathsf{unknown})\Rightarrow\mathsf{Promise}\langle T\rangle\\
\mathtt{\%NewPromise\%}&:\forall T\le P.\ (\mathit{executor}:(\mathit{resolve}:(T)\Rightarrow\mathsf{void},\ \mathit{reject}:(\mathsf{unknown})\Rightarrow\mathsf{void})\Rightarrow\mathsf{void})\Rightarrow\mathsf{Promise}\langle T\rangle
\end{aligned}
```

Instantiated by $\textsf{instances}$, with $R$ the async function's result
annotation, they derive:

```math
\frac{\Gamma\vdash e:\mathsf{Promise}\langle A\rangle\mid B\quad B\le P}{\Gamma\vdash\mathsf{await}\ e:A\mid B}\ \textsf{await}
\qquad
\frac{\Gamma\vdash e:A\mid\mathsf{Promise}\langle B\rangle\quad A\le P\quad B\le P\quad \mathsf{Promise}\langle A\mid B\rangle\le R}{\Gamma\vdash_R\mathsf{return}\ e}\ \textsf{async-return}
\qquad
\frac{\mathsf{Promise}\langle\mathsf{void}\rangle\le R}{\Gamma\vdash_R\text{completion}}\ \textsf{async-complete}
```

`Promise<void>` is `Promise<unknown>` (`void` is top), so a void async
function may only complete. A throw in an async body leaves it as a throw.
A non-promise operand is awaited at its own type only where it is a
primitive ($U\le P$): `await` calls an object's callable `then` instead. A
value of type `Promise<A>` is a realm promise
([trust surface](DESIGN.md#trust-surface)), which resolution never fulfills
with a thenable, since it adopts one, so awaiting it yields an $A$ at any
$A$; a returned promise of a primitive is adopted the same way. The source
builds no object with a `then` member (`fragment-parse.mts`), which could
pass for a promise. A trusted generic signature instantiated at a thenable
`T` would state a promise of it, which a realm promise never is (it adopts
the thenable), so each binder a `Promise` or `PromiseLike` argument of an
imported, ambient or library signature or method names is bounded by

```math
N=P\mid\{\,\mathtt{readonly\ then?}:P\,\}\mid\mathsf{readonly\ unknown[]}
```

the types no thenable inhabits (`promisedBinders`); the client's own generic
bodies are checked at every instantiation instead. The producer infers $T$ and $U$ as TypeScript infers a
union with one bare binder: an object part of the operand goes to the
`Promise` arm, a primitive to the bare binder, and an arm nothing reaches is
inferred at `never`. A `Promise` method's binder written beside a
`PromiseLike` of itself is inferred the same way: `then`'s callback returns
`TResult1 | PromiseLike<TResult1>` and `catch`'s `TResult | PromiseLike<TResult>`,
so a callback returning a promise of $U$, or a primitive $V$, instantiates
the binder at $U$ or $V$:

```math
\frac{\Gamma\vdash f:(\vec A)\Rightarrow\mathsf{Promise}\langle U\rangle\mid V\quad V\le P}
     {\mathit{TResult}:=U\mid V\ \ \text{at}\ \ (\vec A)\Rightarrow\mathit{TResult}\mid\mathsf{PromiseLike}\langle\mathit{TResult}\rangle}
```

The instance is the producer's proposal, checked as any instance of a
scheme ([`InstArrs`](POSITIVE-TYPES.md#instances-of-a-scheme-row)).
Background: [promises and flattened types](REFERENCES.md#promises-and-flattened-types).

### Loops and spreads over iterables

`for (const x of e) S` steps a trusted **iteration intrinsic**, one per kind
of host iterable, which the parser picks by TypeScript's type of $e$
(`iterationKind` in `declaration-graph.mts`, every part of a union alike).
With $\mathit{Step}(E)=()\Rightarrow\{\mathsf{readonly}\ \mathit{value}:E\}\mid\mathsf{null}$:

```math
\begin{array}{ll}
\mathtt{\%Iterate\%}:\forall T.\ (\mathsf{readonly}\ T[\,])\Rightarrow\mathit{Step}(T) & \text{an array or tuple}\\
\mathtt{\%Iterate{:}string\%}:(\mathsf{string})\Rightarrow\mathit{Step}(\mathsf{string}) & \text{a string, by code point}\\
\mathtt{\%Iterate{:}Set\%}:\forall T.\ (\mathsf{Set}\langle T\rangle)\Rightarrow\mathit{Step}(T) & \\
\mathtt{\%Iterate{:}Map\%}:\forall K\,V.\ (\mathsf{Map}\langle K,V\rangle)\Rightarrow\mathit{Step}([K,V]) & \text{a fresh entry per step}\\
\mathtt{\%Iterate{:}Iterator\%}:\forall T.\ (\mathsf{Iterator}\langle T\rangle)\Rightarrow\mathit{Step}(T) & \text{a SetIterator or MapIterator}
\end{array}
```

`Set` and `Map` are the [interface overlay](#library-types)'s, whose
`keys`, `values` and `entries` give a `SetIterator` or `MapIterator` read as
an `Iterator` of its argument. None of these iterators has a `return`, so a
loop left early by `break`, `return` or a throw calls nothing. An iterable of
any other kind with a `[Symbol.iterator]` (an `Iterable<T>`, a class or a
record with one), or a union with one, is the program's, and runs the
[iterator protocol](#the-iterator-protocol); any other steps `%Iterate%`,
whose typing then refuses what is no array. Lean compiles the loop over a
host iterable itself (`SourceExtraction.body`), $\mathit{it}$ the picked
intrinsic:

```math
⟦\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S⟧=
n\leftarrow\mathit{it}(⟦e⟧);\
\mathit{head}:\ r\leftarrow n();\
\mathsf{if}\ r\ \mathsf{is\ null}\ \mathsf{then}\ \mathit{exit}\
\mathsf{else}\ x\leftarrow r.\mathit{value};\ ⟦S⟧;\ \mathsf{goto}\ \mathit{head}
```

`n` is a slot at the call's claimed type, the head a cut stated by the loop's
entry claims, `continue` and the body's end go to the head and `break` to the
exit; the tag dispatch refines `r` on each arm (`tagBind isNul`). The derived
rule, with $\mathit{it}:\forall\vec\alpha.\ (P)\Rightarrow\mathit{Step}(E)$ and
$\sigma$ the call's instance:

```math
\frac{\Gamma\vdash e:A\quad A\le P\sigma\quad
      \Gamma_{\mathit{head}},x:E\sigma\vdash S\quad \Gamma_{\mathit{head}}\ \text{the loop's entry claims}}
     {\Gamma\vdash\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S}\ \textsf{for-of}
```

The native iterator requires a readable array receiver, so every in-bounds
read yields `T`, including a hole when `T` admits `undefined`. A sparse store
needs a separate proof of readability before it satisfies that contract. Array patterns read positions under the same trust
([patterns](#patterns)).

An argument spread `f(…, ...e, …)` over an iterable of one of the other kinds
is the spread of the fresh array its iterator yields, collected where the
spread is written: $\ldots e\equiv\ldots\mathtt{\%Spread{:}K\%}(e)$, with
$\mathtt{\%Spread{:}K\%}:\forall\vec\alpha.\ (P)\Rightarrow E[\,]$ for each
$\mathtt{\%Iterate{:}K\%}:\forall\vec\alpha.\ (P)\Rightarrow\mathit{Step}(E)$, the
array of what that step yields until $\mathsf{null}$. It is an ordinary call
of a trusted value, and the array an ordinary spread into a variadic
callee. A spread of a program's iterable is collected by the
[protocol](#the-iterator-protocol).

A tuple meets `Iterable<T>` through the readonly array of its positions: the
producer claims a tuple expected at an iterable other than an array at
$\mathsf{readonly}\ (A_0\cup\ldots\cup A_{n-1})[\,]$, which Lean derives from
the tuple ($\mathsf{list}$ inclusion) and relates to the iterable through
`Array.prototype[Symbol.iterator]`, as for any array.

### The iterator protocol

An iterable the program defines is iterated as
[ECMA-262](REFERENCES.md#ecma-262)'s ForIn/OfBodyEvaluation runs it, in
ordinary forms the parser writes (`protocolForOf`), each an ordinary call or
read typed by the declarations TypeScript gives the iterable (`Iterable<T>`,
`Iterator<T, TReturn, TNext>`, `IteratorResult<T, TReturn>`, or the program's
own class or record), under names no source spells:

```math
\begin{array}{l}
[\![\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S]\!]=
\{\ \mathsf{const}\ i=e[@@\mathit{iterator}](),\ n=i.\mathit{next}.\mathsf{bind}(i);\\
\quad\mathsf{while}\ (\mathsf{true})\ \{\ \mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\
  \mathsf{const}\ x=r.\mathit{value};\ \mathsf{closing}\ \{S\}\ \mathsf{close}\ C_i\ \}\ \}\\[2pt]
C_i=\mathsf{const}\ m=i.\mathit{return};\ \mathsf{if}\ (\mathsf{typeof}\ m\ne\texttt{"undefined"})\ \{\ \mathsf{const}\ \_:\mathsf{object}=m.\mathsf{call}(i)\ \}
\end{array}
```

GetIterator reads `next` once, and each step calls it on the iterator: the
bound function is that call ([`bindMember`](#judgments-and-constructor-views)). A
`return` the iterator's type declares a required method is read bound the
same way, $C_i=\mathsf{const}\ m=i.\mathit{return}.\mathsf{bind}(i);\ \mathsf{const}\ \_:\mathsf{object}=m()$;
an optional one or a property is read, tested and called on the iterator, as
GetMethod and IteratorClose do. The result must be an object, which is the
TypeError IteratorClose throws otherwise, made impossible by the annotation's
obligation. The test of `r.done` refines $r$ to the arms whose `done` may be
falsy (a [field slice](#refinement-under-an-observed-outcome) through the
read's link, optional where `IteratorYieldResult` leaves `done` optional), so
`r.value` is read at the not-done arm's type, `T`. An iterator whose type
states no `return` is refused where the loop could close it: an open record
may own any `return`.

The library's declarations are read by the rules of
[library types](#library-types): `Iterable<T>` is the record of its one
method under the realm's `Symbol.iterator` key, returning an `Iterator`, and
so no `Iterator`, whose `next` it lacks; `Iterator`'s
`next(...[value]: [] | [TNext])` is the two signatures `next()` and
`next(value: TNext)` (**rest-tuples**), and its `return?` and `throw?` are
optional methods: optional fields whose functions take the iterator as
receiver ([records](POSITIVE-TYPES.md#records)), which is what the close's
test of `return` reads.

The closing region is a `finally` that runs on some ways out of $S$ only,
compiled by the machinery of `try` (`SourceExtraction.body`, `Finalizer`):

```math
\frac{\begin{array}{c}
\Gamma\vdash_R S\ \text{with}\ \mathsf{break}\mapsto C;\mathit{exit},\quad
  \mathsf{return}\ v\mapsto C;\mathsf{return}\ v,\quad
  \mathsf{continue}\mapsto\mathit{head},\quad
  \mathsf{throw}\ u\mapsto(\mathsf{try}\ C\ \mathsf{catch}\ \{\});\mathsf{throw}\ u\\
\Gamma\vdash_R C\ \text{on each of those ways}
\end{array}}
     {\Gamma\vdash_R\ \mathsf{closing}\ \{S\}\ \mathsf{close}\ C}\ \textsf{closing}
```

The close runs before a `break` of the loop leaves it, before a `return`
returns the value held in a slot of its own (as through any `finally`), and,
its own throws discarded by a handler that drops them, before a throw out of
the body is thrown again: IteratorClose with a throw completion keeps the
body's. Its end and a `continue` go to the head, and a done result leaves
without it, as IteratorClose is not called there. A jump past the loop to an
outer target passes it as it passes a `finally`. Every edge is checked as
any other; the close's statement entries state each cell at its contract.

A spread of a program's iterable (`collect`), the one element of an array
literal or an argument of a call of a name after names and literals the file
never assigns, and the statement's value, is collected before the
statement, where nothing the statement evaluates before the spread can be
changed by the iterator's code: $\mathsf{const}\ a=[\,],\ i,\ n;\ \mathsf{while}\
(\mathsf{true})\ \{\ \mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\
a.\mathit{push}(r.\mathit{value})\ \}$, then $\ldots a$ (or $a$ for the literal);
a spread steps to the end and closes nothing. The one element of an array
literal spreading a host iterable (a string, a `Set`, a `Map`, a host
collection iterator) is its spread intrinsic's call, `[...e]` $\equiv$
`%Spread:K%(e)`, the fresh array of what the host's iterator yields, as an
argument spread of one is. An array pattern
`const [p₀, …, ...q] = e` over one (`protocolPattern`) steps once per element,
a hole too, into cells $v_j$ starting `undefined`, leaves a labeled block when
a step is done, collects the rest to the end, and without a rest closes the
iterator after the elements, as IteratorBindingInitialization does; the
source's names are then bound from the cells, which binding names does not
observe. A default or a nested pattern, which run code between the steps, is
refused.

### Statement forms

The statement forms of a body are lowered to the graph compiler's where the
lowering is exact ([as graphs](#statement-forms-as-graphs)). $\Gamma\vdash_R S$
reads "the statements $S$ are safe under $\Gamma$ in a function whose result
is $R$". An unbraced arm is the block holding it and `else if (c) S` is
`else { if (c) S }`; `return;` is `return undefined`, and a block closure that
does not return on every terminal arm ends with `return undefined`:

```math
\frac{\mathsf{undefined}\le R}{\Gamma\vdash_R\ \mathsf{return};}\ \textsf{return-bare}
\qquad
\frac{\Gamma\vdash_R S_1\quad S_1\ \text{always jumps}\quad \mathit{names}(S_2)\ \text{free in no live statement, none hoisted}}
     {\Gamma\vdash_R S_1;S_2}\ \textsf{dead}
```

`for (init; cond; update) S` is `{ init; loop }` with a `while (cond)` whose
body's end and every `continue` run `update`, then go to the head (a closure
capturing a `for` loop's `let` is refused, since JavaScript copies it per
iteration):

```math
\frac{\Gamma\vdash_R \mathit{init}:\Gamma'\quad \Gamma_h\ \text{the head's entry claims}\quad
      \Gamma'\le\Gamma_h\quad \Gamma_h\vdash c:\mathsf{boolean}\quad
      \Gamma_h\wedge c\vdash_R S\ \text{with}\ \mathsf{continue}\mapsto u\quad
      \Gamma_u\vdash \mathit{update}\ \text{back to}\ \Gamma_h}
     {\Gamma\vdash_R\ \mathsf{for}\ (\mathit{init};c;\mathit{update})\ S}\ \textsf{for}
```

`switch (d) { … }` is a labeled block per clause, nested in source order
inside one for the whole switch: the innermost holds the dispatch, each case
label in order `if (d === l) break` to the end of its clause's block, and
each clause's statements follow its block's end, so fall-through is ordinary
sequencing. The discriminant is evaluated once into a slot no source names,
unless it is a name or a field of a name and every label a literal or a name,
when it is re-read at each test. A name declared in one clause and read in
another is refused.

```math
\frac{\Gamma\vdash_R S\ \text{with}\ \mathsf{break}\ \ell\mapsto\Gamma_{\mathit{after}}\quad
      \Gamma_{\mathit{after}}\vdash_R S'}
     {\Gamma\vdash_R\ \ell:\{S\};S'}\ \textsf{labeled-block}
```

`for (const k in o) S` is `for (const k of %ForIn%(o)) S` with the trusted

```math
\mathtt{\%ForIn\%}:(o:\mathsf{unknown})\Rightarrow\mathsf{readonly}\ \mathsf{string}[\,],
```

the keys the loop visits: strings, for any value. Where the body reads the
entry at the key, `P[k]` with `P` the loop's operand spelled again (a name,
or a chain of named reads from one), before anything that could change the
entry runs, the loop steps the entries instead,
`for (const e of %Iterate:ForIn%(P)) { const k = e[0]; S' }` with each such
read in $S'$ the step's value `e[1]`:

```math
\mathtt{\%Iterate{:}ForIn\%}:\forall V.\ (o:\{\mathsf{readonly}\ [k:\mathsf{string}]:V\})\Rightarrow
  ()\Rightarrow\{\mathsf{readonly}\ \mathsf{value}:[\mathsf{string},V]\}\mid\mathsf{null},
```

each step a fresh array of a key the loop visits and the value the object
holds under it at the step. A dictionary holds no prototype, and a plain
object's, `Object.prototype`, no enumerable key, so every key visited is the
object's own, whose value the index's contract states. The reads rewritten
are those of the statements the body starts with that run no code and write
no property, outside the functions they define, and the whole initializer of
the declaration after them; the operand's name is written nowhere in the
outermost function holding the loop (the file, at the top level), and a
chain of reads is read from a body that runs no code and writes no
property, so each read finds the object the loop enumerates and the value
the step read (`forInEntryReads` in `tools/fragment-parse.mts`). A read
after a call is the dictionary's read, `V | undefined`: the call may have
removed the key. `try B catch (e) C finally
F` names $C$'s entry as the handler of $B$'s nodes that may throw, with `e`
at `unknown` (the only annotation admitted), and compiles $F$ on every way
out: after a normal completion, before each `return` with the value held,
before each `break` or `continue` leaving it, then on to the jump's target
through the `finally` of every enclosing `try` the jump also leaves, after a
throw with the thrown value held and rethrown. A `return`, `throw`, `break`
or `continue` in $F$ leaves by its own way, as JavaScript's replaces the
pending completion:

```math
\frac{\Gamma\vdash_R B\ \text{with throws}\mapsto(\mathsf{unknown},\Gamma)\vdash_R C\quad
      \Gamma\vdash_R F\ \text{on each way out}}
     {\Gamma\vdash_R\ \mathsf{try}\ B\ \mathsf{catch}\ (e)\ C\ \mathsf{finally}\ F}\ \textsf{try}
```

The handler's and finalizer's entries state each cell at its contract, since
a throw may leave after any part of the body ran.

### Guards

Every guard is a tag test ([SEMANTICS](SEMANTICS.md#operational-language)),
refining a tested immutable binding by the tag slice $T_q$ of its type on
each edge ([refinement](#refinement-under-an-observed-outcome)). A
user-defined type guard (`x is T`) or assertion function (`asserts x is T`)
is refused where its type is written: its promise ties the call's result, or
its completion, to its argument, which no function type states:

```math
\frac{\Gamma(x)=A\quad\Gamma[x:T_{\mathsf{typeofObject}}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{typeofObject}}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{typeof}\ x\equiv\texttt{"object"})\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-typeof-object}
```

```math
\frac{\Gamma(x)=A\quad A\ \text{objects, no class value}\quad \kappa\notin\mathcal R\quad
      \Gamma[x:T_{\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{"}\kappa\texttt{"}\ \mathtt{in}\ x)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-in}
```

with $\mathcal R$ the refused keys (`inKeyRefusal`: `Object.prototype`'s,
`Array.prototype`'s and `Function.prototype`'s own string keys, array
indices, and the keys the model reserves). `in`'s answers are by keys the
types state (`inAnswer`): a failed test drops an arm owning the key, a passed
one drops an arm whose key bounds exclude it and the prototype key, and every
primitive; a passed test promotes an optional key to a field (`promote`). A
test against a claimed singleton $c$ of any primitive kind, and against a
field of an immutable binding's object, narrows the binding or the object's
arms:

```math
\frac{\Gamma\vdash a:A\quad \Gamma\vdash k:\{c\}\quad
      \Gamma[x:T_{\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_1\quad
      \Gamma[x:T_{\lnot\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (x\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-singleton}
\qquad
\frac{\Gamma\vdash k:\{c\}\quad
      \Gamma[o:F^{f}_{\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_1\quad
      \Gamma[o:F^{f}_{\lnot\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (o.f\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-field}
```

with $F^f$ the field slice. The truthiness of a field of an immutable
binding's object, where an arm of it leaves the field optional or unnamed (so
that no fact about what the field holds is claimed, as of an
`IteratorResult`'s `done`), narrows the object's arms the same way, the read
dispatched on its truthiness:

```math
\frac{\Gamma[o:F^{f}_{\mathsf{truthy}}(\Gamma(o))]\vdash_R S_1\quad
      \Gamma[o:F^{f}_{\lnot\mathsf{truthy}}(\Gamma(o))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (o.f)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-field-truthy}
```

`x === y` with `x` claimed at a union of
singletons is dispatched as the disjunction over its singletons $c$ of
$x\equiv c\land y\equiv c$ (`savedSplit` where `x` has effects). Strict
equality without a singleton is the $\equiv$ operator of `arith`, which
narrows nothing and is refused between two operands that may both be objects
without a field. `x instanceof C`, for a class the file declares at its top
level, is $\mathsf{hasKey}(\kappa_C)$ ([derived form](#derived-source-forms)).
It does not narrow `unknown`: an object gets $C$'s prototype without $C$'s
constructor running (`Object.create(C.prototype)`), so the key is no evidence
of $C$'s fields. `Array.isArray(x)` narrows a record or dictionary arm of $x$
to the realm's `sparse ReadonlyArray<unknown>` where it holds
([**tag-array**](#refinement-under-an-observed-outcome)), and keeps
`unknown`, which the array invariant says nothing of:

```math
\frac{\Gamma(x)=A\quad A\preceq_{\mathsf{isArray}=\mathsf{true}}B\quad \Gamma[x:B]\vdash_R S_1\quad
      \Gamma[x:T_{\lnot\mathsf{isArray}}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\mathtt{Array.isArray}(x))\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-array}
```

### Enums

With $m_1,\ldots,m_n$ an enum's members and $v_i$ the value TypeScript
computes for $m_i$ (`getConstantValue`):

```math
\frac{\forall i.\ v_i\ \text{computed by TypeScript, finite if a number}\quad
      \text{no reverse key names a member}}
     {\texttt{enum E}\{\vec m\}\ \leadsto\ \texttt{const E}:\mathcal O(E)=\{\overline{m_i:v_i},\ \overline{\mathrm{str}(v_j):\text{"}m_j\text{"}}^{\,v_j\in\mathbb R}\}}
```

with $\mathcal O(E)$ the object type of those fields, each readonly at its
value's literal type, in JavaScript's key order where the declaration is. The
type `E` is $\bigcup_i\{v_i\}$, `E.A` the literal type of `A`'s value, and
`typeof E` is $\mathcal O(E)$. A `const enum` read is its member's value
(`constEnumReads`), and the declaration runs nothing.

### Const assertions

`e as const` returns its operand, claimed at the operand's *const type*:

```math
\mathsf{const}(\ell)=\{\ell\},\qquad
\mathsf{const}([e_1,\ldots,e_k])=\mathsf{readonly}\;[\mathsf{const}(e_1),\ldots,\mathsf{const}(e_k)],
```
```math
\mathsf{const}(\{f_1:e_1,\ldots\})=\{\mathsf{readonly}\;f_1:\mathsf{const}(e_1),\ldots\},\qquad
\mathsf{const}(x)=\Gamma(x),\qquad
\mathsf{const}(e\;\texttt{as const})=\mathsf{const}(e),
```

for a literal $\ell$; any other operand is refused. An element or field of a
literal that is none of these (`[x.f] as const`) keeps its own type,
$\mathsf{const}(e_i)=\tau(e_i)$, as TypeScript's const context does. The const type is a
proposal: Lean checks the operand's allocation at it and the cast's claim
from the operand's. Other assertions (`e as T`, `e satisfies T`, `e!`) are
the same node with $T$ an obligation the operand meets; nothing decides an
assertion true.

## Callables

The callable fragment described below is implemented. The rest of
this section states the broader design and the rules it would add, in the terms of the rules above, so the
design can be read as a user of the verifier would read it: what can be claimed
about a value, what a claim commits to, and what the verifier will and will not
check. Where a fact below is already proved, the theorem is named; where it is
not, the sentence says so.

### What a function is, and what the calculus has

A JavaScript function value is three things: **code** — its `[[Call]]`
behaviour, which cannot be changed after creation; a **property bag** —
`f.cancel = …` is an ordinary object write; and an **identity** — `f === g`.
A value is a function exactly when it has `[[Call]]`, which is what
`typeof f === "function"` tests. Having `[[Call]]` does not make a call safe: a
class constructor's `[[Call]]` always throws, and a value of TypeScript's
`Function` type has `[[Call]]` and no known signature. Every constructor also has
`[[Call]]`, so constructibility implies `typeof "function"`.

The original [operational language](SEMANTICS.md#operational-language) separated
lambdas from locations. The Lean runtime now has only object values for both
plain objects (`objAt fields absent`) and functions (`objAt fields code`, graph
code for every source function), where `fields` is the finite map from field names to the locations
they stand for, fixed at allocation. `CallCode` is a separate descriptor type;
its body is not a runtime value. `makeAt code names inits` takes one fresh
location per named field; a source function is the one-field case,
`makeFn code null`, a null-initialized bag under the key `[[code]]`, which no
source key spells and a copy does not take — a function has no properties of
its own, and that one location is what gives it an identity to compare.
`letE` binds without allocation. Plain allocation and one-field function
creation are abbreviations of `makeAt`, with one congruence rule, one
allocation step, and the shared semantic proofs `make_rule`, `makeFn_rule`
and `make_fields_rule`. `isFun` recognizes function objects and
`isRef` recognizes plain objects, both independently of the heap.

[CallableObjects.lean](lean/Verification/Model/Programs/CallableObjects.lean) proves that a callable object's fields are read and written as a record's.
`bagT P` describes an object's writable fields independently of its call code,
read and written as a record's (`bag_read`, `bag_write`); the call contracts
(`callsT`, `restsT`) hold of the same value. `EnvOk.prepend` extends environments with ordered
parameter lists, `frame_envOk` builds the frame graph code is entered with
from the receiver, the parameters the code takes and the captured values, and
`graph_invoke` and `graphRest_invoke` derive the native call contract from a
checked code. Source functions lower to graph code, and the certificate
producer and consumer use its allocating typing rules (`funGraph`,
`funScheme`, `ctorGraph`, `callableGraph`). A checked creation effect preserves existing heap knowledge without
executing the body. Allocation, application, bag reads and writes,
and overload conjunction have safety proofs. The graph clause
`callable first rest arrows variadic` combines a nonempty conjunction of bag
invariants with fixed and variadic call promises on one object. Normalization
merges the corresponding lists; structural
subtyping checks invariant bag coverage and arrow coverage separately, and can
forget properties to obtain `arrs`. The producer and consumer support
`callableGraph`, `callCallable`, `readCallable`, and `writeCallable` evidence.

Receivers are implemented along the same lines. Every signature carries its
receiver, and every call its receiver premise; an ordinary function expression
or object-literal method binds the receiver of each call as `this`, and an
arrow's `this` is a capture of the enclosing one. A method call saves the
object, reads and saves the method, evaluates the actuals, then invokes the
saved method with the saved object, so an actual that replaces the method
field changes only later calls and one that writes a receiver field is seen by
the body. The receiver each call passes is also a located `method-receiver`
obligation. `.bind` allocates the forwarding descriptor `bound(f, r, p⃗)`
(`bindE`), whose invocation ignores its own receiver: a second `.bind` or a
`.call` on it cannot replace the first receiver, and a write to the receiver's
field after binding is seen, since the descriptor saves the object, not its
fields. A quantified ordinary function may name its binder as its receiver; its
body is checked once under the binder and each call is an instance at the
receiver it passes. The witnesses are `tests/callables/methods.ts`,
`call-objects.ts`, `apply.ts` and `generic-receivers.ts`.
The pipeline case `recursive-callable` holds the recursive contract
`R = callable(null | R; Boolean → Boolean)`: a function is written into its
own bag, read back, narrowed and called, and passed and returned at `R`;
`invalid-recursive-callable` refuses a view of the bag that also admits
`true`, as the bag's field is invariant. These use the existing rules; no
recursive-callable special case or additional semantic axiom is needed.
The safety contract guarantees progress, not termination.
The existing
`refT` and graph reference clauses still mean plain objects. A callability-neutral
bag view can be expressed as `refs P Ps | callable P Ps []` using two graph
labels. `CallableConjunctions.neutral_iff` proves that this union is precisely
the bag conjunction on scoped values, whatever code they carry; it forgets
invocation promises without changing the object. The pipeline case
`callable-bag-union` reads and writes a field through a union of a record and
a function carrying it, and `invalid-callable-bag-union` refuses a write the
function's bag does not admit. Proof search first tries a single
constructor view, then splits an explicitly union-typed receiver variable for
reads, writes, and calls, using the existing `unionVar` evidence. Every alternative
must check; a null alternative cannot be ignored. Both allocation shapes run
through the same read/write graph and JSON protocol without a runtime tag
branch. The view makes no invocation promise.
A call through a union of known signatures needs every alternative to accept
the actual argument and produce a result covered by the requested type. The
producer states no claim for a call through a union of functions carrying
different fields (`callable-bag-union-call-refused`). This does
not invent a signature from `typeof`, pick a successful alternative, or require
a common arrow label in the graph. The producer emits ordinary `unionVar`
evidence; the consumer and wire format are unchanged.
The pipeline case `callable-union-capture` is the source-closure path for
unions of primitive-only function signatures. The direct recipe saves the
callee and argument in order, then checks each alternative at the saved
callee slot and joins the signature results; `ocaml-producer/test.mts`
refuses a result claim narrowed to one alternative at the call.
Single-arrow call recipes keep their existing form.
Explicit normalized source claims also exercise unions of overloaded functions:
the applicable signature occurs at different positions in the two alternatives,
and changing from a null to a Boolean argument reverses those positions. Both
calls verify; discarding a possible result or omitting one alternative's applicable
signature fails. This validates the source adapter and independent consumer.
Null-guard regressions retain every callable alternative on the non-null arm
for both comparison polarities and operand orders. Calls on the null arm and
unjustifiably narrow results fail. The `guardedCallableUnion` TypeScript fixture
also runs through the parser, a claim producer, the independent source
consumer, and the annotated report pipeline. Report syntax groups arrow alternatives and
preserves each alternative's hidden metadata when reading the union back.
The `coalescedCallable` fixture selects between a null/undefined-or-callable
input and a fallback before invocation. Both distinct return contracts survive
export and verification. Producer and consumer regressions reject a discarded
fallback alternative, a narrowed result, reuse of the nullish input as the
fallback, a null fallback, and an incompatible argument.
These sources live in the dedicated [Callables group](tests/callables/README.md),
with their own pipeline suite and corpus/viewer section.
The `andGuardedCallable` and `orGuardedCallable` examples exercise short-circuit
calls with singleton call results. Their full expression results also include
the skipped branch. Reversing the guard, changing the short-circuit operator,
or discarding the skipped result fails both production and independent checking.
`capturedGuardedCallable` returns a closure from a guarded branch, retaining the
immutable capture's non-null refinement for later calls. Both callable alternatives
remain possible. A reversed guard, discarded alternative, narrowed closure
signature, or narrowed inner call result fails producer and consumer checks.
`aliasedCallableSelection` selects an immutable local alias with a ternary and
captures it in a nested closure. Both alternatives survive the selection and
the next statement's environment. False initializer and entry claims, reversed
selection, reuse of the original nullable input, and narrowed nested-call results
fail independently checked obligations.
`sharedCallableDomain` selects between Boolean-accepting and true-only functions.
The shared true argument verifies. A false argument, forged widening of the
callee's domain, removal of its restrictive alternative, or narrowed result
fails both production and independent consumption.
`branchLocalCallableDomains` uses the tested Boolean as the argument inside
each branch: its true refinement satisfies a true-only domain, while its false
refinement requires the wider Boolean domain. Both singleton results reach the
join. Forged argument refinements, an incompatible false-branch callee, false
branch-result claims, and a narrowed join fail producer and consumer checks.
`callableArgumentWrite` writes a captured Boolean cell in a call's argument.
Storage and parameter obligations both remain checked, and the assignment
returns its RHS. The original Boolean export verifies; an explicit false-result
refinement also verifies with a false-only callee view and fresh evidence.
The original evidence cannot justify that stronger request. Captured reads
continue to use the Boolean invariant rather than an invented singleton.
`nestedCallableArgumentWrite` exercises the compositional closure path for an
argument write. Its exact expression proof saves the receiver, binds the named
RHS at the shifted position, writes once, and returns that saved RHS. Corrupting
the evidence to use the Boolean seed capture instead of the Boolean parameter
fails, even though their types agree. Wrong receiver and narrowed RHS/result
claims also fail production and independent consumption.
The pipeline cases `cell-union-capture` and `invalid-cell-union-write` check
reads and writes through unions of locally
allocated invariant cells inside source closures. Reads join possible contents. Writes check the saved
RHS against every alternative, evaluate each operand once, and return that RHS
as the source assignment value. Direct recipes need no expression-search fuel.
A write accepted by only one alternative fails the source consumer.
`ocaml-producer/test.mts` adds current-content assertions to the producer's
claims, each a located obligation over the union of invariant contents: a
broad observation verifies at the closure's read, one narrowed to the
allocation's initial value fails there, a null-only statement-entry
observation holds after the closure writes `null` and fails where nothing
wrote it, and an entry environment that narrows the captured storage contract
fails its own obligation even when its contents observation holds.
Typed reads retain current heap
facts and read links when every alternative has the same invariant operand.
The regression keeps a known `false` fact about another cell across a neutral
read, then checks a singleton result from that cell through the JSON pipeline. Source export of a combined callable/property type covers one required `value`
field on a function.
Source integration also needs explicit property-presence/initialization rules:
the model's initial function bag does not establish a source `value` field.
Object parameters are admitted at their annotation: the interpretation of a
structural annotation as a plain data object is part of the caller contract,
as the arrow interpretation already was (DESIGN.md, the trust surface). The
heap evidence is stated over locations and so covers aliased parameters.
`ObjectCoherence.step_preserves` proves global identity/descriptor coherence
for the operational machine using an append-only ghost registry, including
objects nested in code and heap cells. `GraphCoherence.accepted_closed_coherent`
connects that invariant to every finite run of an accepted graph. The consumer
checks that graph syntax cannot embed runtime identities; external inputs must
already be coherent. Semantic type families remain defined over unrestricted
raw values, so coherence is a separate execution invariant, not a new membership
premise. Construction, receivers, exceptions, and richer property operations
remain outside this implemented slice.

SKJS has no separate function type. A function type is an object type whose
fields carry a `call` member, and every object type carries a call mode from a
four-point lattice: `CPresent(L)`, invocable with the signatures in $L$;
`CFunction`, which has `[[Call]]` and no known signature (`Function`, a class
constructor); `CAbsent`, provably not callable (object literals, class
instances, arrays); and `CUnknown`, a structural object type — `{}`, an
interface — which width subtyping lets a function inhabit. The
[views these modes obtain](#shape-tests-and-identity) are given with the rules.
The claims exporter still refuses positive callability on cells and function
shape without a signature. Ordinary exported function signatures already run
through the allocated-function path.

### A first proposal, and its generalisation

A first proposal added one value shape, the pair JavaScript has: a closure body
and a location for its properties, $\mathsf{callable}(b,\ell)$, created by
$\mathsf{attach}(\lambda x.t,\,v)$, which allocates the bag as $\mathsf{alloc}$
does; a call on it is one beta step, reads and writes go to the bag, and
$\mathsf{isFun}$ answers true for it. Its type $\mathsf{Callable}(L;C)$ is the
arrow family over $L$ intersected with the bag's reference contract, every
callable is a function, and $\mathsf{isFun}$ stays total and heap-independent.
The rest of this section is the complete account that proposal grows into: a
generalisation of it, a uniform object model with identity, property
operations, and separate call and construction behaviours. Call that design
**C\***. The proposal's operations, types and rules are recovered below as
special cases, and the sentences that say so name it as the first proposal.

| Notation                                                                                | Meaning                                                                                                           |
| --------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| $\Gamma\vdash_G t:A\;!E$                                                                | a computation whose normal results have type $A$ and whose thrown values have type $E$; $E=\bot$ when unannotated |
| $\vdash_G^{\mathsf{call}}$, $\vdash_G^{\mathsf{construct}}$, $\vdash_G^{\mathsf{init}}$ | auxiliary judgments on invocation programs and initial property layouts                                           |
| $\sigma=(R;\alpha)\xrightarrow{E}B$                                                     | a call signature: receiver contract $R$, argument-list contract $\alpha$, exception bound $E$, result $B$         |
| $\nu=(N;\alpha)\xRightarrow{E}B$                                                        | a construction signature, with $N$ the contract on `new.target`                                                   |
| $\bar a$, $\bar p$                                                                      | an actual argument list, and stored bound arguments                                                               |
| $\mathsf{Obj}(P)$, $\mathsf{Fun}$, $\mathsf{Ctor}$                                      | objects meeting the property contract $P$; objects with `[[Call]]`; objects with `[[Construct]]`                  |
| $\top_p$                                                                                | the property contract imposing no requirement                                                                     |
| $\ell$, $\delta$, $\pi$, $\kappa$, $\eta$                                               | an identity, an operation descriptor, and its property, call and construction components                          |

### One object identity, several operations

Every source-level object, including every function, has an identity.
Represent an object value schematically as

```math
\mathsf{object}(\ell,\delta),
```

where $\ell$ is its identity and $\delta$ is an internal operation descriptor:

```math
\delta =
\left\langle
  \mathsf{properties}:\pi,\quad
  \mathsf{call}:\mathrm{Option}(\kappa),\quad
  \mathsf{construct}:\mathrm{Option}(\eta)
\right\rangle.
```

The descriptor determines **how operations are dispatched**. The heap contains
the mutable state those operations use. Neither the descriptor nor its
components are ordinary, source-visible properties.

This follows the relevant distinction in ECMAScript: objects support property
operations, while function objects additionally have `[[Call]]` and possibly
`[[Construct]]`. Those internal operations are not properties named `call` or
`construct`. ([TC39][c1])

Once creation is complete, the presence of the call and construction operations
is stable. Their behaviour need not be independent of mutable state.

In this representation,

```math
\mathsf{isFun}(\mathsf{object}(\ell,\delta))
\iff
\delta.\mathsf{call}\ne\mathsf{None},
```

and source-level object equality compares identities:

```math
\mathsf{object}(\ell,\delta)
  ===
\mathsf{object}(\ell',\delta')
\iff
\ell=\ell'.
```

Well-formedness requires a unique descriptor for each identity. Thus
function-shape tests can remain heap-independent without making function
behaviour heap-independent.

**All functions receive this representation at creation, not when their first
custom property is added.** A plain function type, a callable-with-properties
type, and a property-only type are views of the same value. Subsumption never
allocates, wraps, or replaces it.

That is the principal coherence requirement.

### Invocation is not restricted to beta reduction

The operational interface contains

```math
\begin{aligned}
&\mathrm{Call}(f,r,\bar a),\\
&\mathrm{Construct}(f,\bar a,n),\\
&\mathrm{Get}(o,k,r),\\
&\mathrm{Set}(o,k,v,r).
\end{aligned}
```

Here $r$ is the receiver, $\bar a$ is the actual argument list, and $n$ is
`new.target`.

A call descriptor specifies an invocation algorithm. Entering a closure body is
one such algorithm — not the definition of invocation for every callable.

The following are cases of that interface, rather than competing
representations:

| Source form                                 | Account in C\*                                                                                                                                                          |
| ------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Ordinary function declaration or expression | A closure with an environment and the appropriate strict or non-strict receiver discipline. Declaration versus expression also affects when its binding is initialized. |
| Arrow function                              | A closure whose references to `this`, `arguments`, `super`, and `new.target` resolve through the enclosing lexical environment. It has no construction operation.       |
| Object or class method                      | A function whose invocation receives the call-site receiver; its home-object association supports `super`. Extracting the function does not bind that receiver.         |
| Class-field arrow                           | Arrow creation performed during instance initialization, producing a distinct function identity for each instance.                                                      |
| Bound function                              | A fresh object whose call operation forwards to a target with stored receiver and arguments. Construction, when supported, has its own forwarding rule.                 |
| Class constructor                           | An object with a construction operation and a call operation that throws. Function shape therefore does not imply a successful ordinary call.                           |
| Callable proxy                              | A fresh object whose operations dispatch through proxy algorithms, consulting its target, handler, and revocation state.                                                |
| Async or generator function                 | A function whose invocation uses the corresponding promise or suspended-computation semantics.                                                                          |

The ordinary-function, arrow, method, and class distinctions come from the
function-creation and invocation rules; in particular, an arrow captures an
environment for the special bindings, not merely a copied receiver value.
([TC39][c2]) Bound functions and proxies have distinct forwarding algorithms.
([TC39][c3]) Async and generator behaviour requires the corresponding
control-state semantics. ([TC39][c4])

The important consequence is that **there is no need for a separate source type
constructor for "arrow-function values"**. Their creation and invocation rules
differ, but they may satisfy the same call contracts as ordinary functions.

Similarly, a TypeScript object type containing a call signature describes an
interface. It is not another runtime creation mechanism. TypeScript explicitly
permits call signatures, properties, and construct signatures to coexist in one
type. ([TypeScript][c5])

### Properties must mean object operations, not just a bag of cells

For the complete account, the property component cannot be specified solely by

```math
\mathrm{Get}(o,k)=H(o)[k].
```

An object may have data properties, accessors, inherited properties, and
symbol-keyed properties. Property operations can invoke code; proxies can
intercept them. ECMAScript accordingly specifies property descriptors and
internal property operations separately from a simple field store. ([TC39][c1])

C\* should therefore distinguish two semantic assertions:

```math
\mathsf{OwnData}(o,k,A)
```

for a particular kind of stored property, and

```math
\mathsf{Readable}(o,k,A)
```

for an appropriate contract on reading the property.

They are not interchangeable. The latter may require a computation contract,
including effects and exceptions. Writable properties require corresponding
write permissions and preservation obligations.

Ordinary data properties can retain the simpler reference-based rules. They
become a **verified special case** of the general object interface.

This also explains how decoration and wrapping differ in the design. Decoration
operates on an existing object identity. Wrapping creates a new object with a
forwarding call operation; sharing or copying properties is a separate action.
`Object.assign`, for example, returns its target rather than replacing its
identity. ([TC39][c3])

### Types describe behaviour, not internal storage

Keep shape, properties, calls, and construction as separate predicates.

For shape,

```math
\mathsf{Ctor}<:\mathsf{Fun}<:\mathsf{Obj}.
```

The first inclusion reflects the ECMAScript invariant that an object with
`[[Construct]]` also has `[[Call]]`; it does **not** assert that ordinary
invocation succeeds. ([TC39][c6])

For callable contracts,

```math
\mathsf{Callable}(L;P)
=
\mathsf{Fun}
\cap \mathsf{Props}(P)
\cap \bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma).
```

This is also the organizing equation of the implemented model, not just the
future object design. [SEMANTICS.md](SEMANTICS.md#one-meaning-for-callable-contracts)
states the indexed call promise precisely and maps each component to Lean.
Fixed and variadic signatures share that promise; code-specific binding rules
establish it at creation. Construction and receivers below remain planned
extensions. Quantified rest signatures use the same universal introduction
and instantiated call promises as fixed signatures.

For construction contracts,

```math
\mathsf{Constructible}(M)
=
\mathsf{Ctor}
\cap \bigcap_{\nu\in M}\mathsf{ConstructSpec}(\nu).
```

A value usable both ways has their intersection. A property-only view drops the
call and construction requirements without asserting their absence.

The empty call family still means function shape with no supplied call
contract:

```math
\mathsf{Callable}([];P)
=
\mathsf{Fun}\cap\mathsf{Props}(P).
```

This preserves the distinction between `CFunction` and `CUnknown` above:
knowing that a value is a function is different from merely not excluding
functions.

**Overloads.** Several call contracts are conjunctions of behavioural
obligations:

```math
\mathsf{CallSpec}(L)
\cap
\mathsf{CallSpec}(M)
=
\mathsf{CallSpec}(L\mathbin{+\!+}M).
```

They are **not** assertions that a writable internal cell has two different
invariant content types. This is the law
[`CallEffects.callsT_append`](lean/Verification/Model/Semantics/CallEffects.lean)
proves for `callsT`.

Consequently, placing the implementation in the heap does not itself damage
overloads. The difficulty with A — boxing every function as an ordinary
reference — was typing the implementation through an ordinary writable
reference. A\* avoids that by separating the internal invocation mechanism from
source-level mutation.

**Generics and argument lists.** A call contract must be able to express a
quantified relationship, schematically

```math
\forall\bar X.\;
(R;\alpha)\Rightarrow B,
```

where $R$ describes the receiver and $\alpha$ describes an argument list.

Quantification is needed for generic input/output relationships; argument-list
contracts handle optional and rest parameters. These are features of the
contract language, not new runtime callable shapes. TypeScript exposes both
generic signatures and these parameter forms. ([TypeScript][c5])

This means the complete account needs more than the finite families of
monomorphic arrows this document has so far. It needs a specified
quantification discipline and rules connecting those richer contracts to the
existing type fragment.

Quantified contracts are scheme rows
([quantified schemes](POSITIVE-TYPES.md#quantified-scheme-layer)): a generic
unit is a graph request over parameter rows, and a generic closure is graph
code at a scheme row (`funScheme`), both certified at every assignment of the
rows ([Generic-Body](#overloads-polymorphism-and-binding)). There is no second
checker for generic bodies.

**Effects and state.** The behavioural obligation must use the computation
semantics, not just a relation between input and output values. Schematically,

```math
\{\mathcal P\}\;
\mathrm{Call}(f,r,\bar a)
\;\{\mathsf{return}\ v.\mathcal Q;\;
    \mathsf{throw}\ e.\mathcal E\}.
```

An ordinary arrow can abbreviate a suitable special case. Contracts for promises
and generators additionally describe subsequent interactions with the returned
objects.

This is where mutable captured state, callback protocols, and revocable
capabilities belong.

For example, revoking a callable proxy leaves its function shape intact, but
subsequent calls throw. Its callability is therefore a stable shape fact; a
guarantee that invocation will not throw requires stronger assumptions about
state. ([TC39][c7])

A contract saying "every normal return is a number" may survive revocation. A
contract promising a successful numeric return does not follow merely from the
same shape information. The design must state which guarantee its arrows
express.

**What this means for the first proposal.** C\* is another realisation of it.
Carry the invocation descriptor in the value and keep mutable object state in
the heap. This preserves the motivation for the first proposal while replacing
"every call is beta reduction" and "every property operation is a bag access"
with the general interface.

### Typing rules

The rules below extend the first proposal's callable introduction,
application, property access, and subsumption. They retain the ordinary
judgment $\Gamma\vdash_G t:A$; exception bounds, construction contracts, and the
stateful judgments are explicit additions. These are proposed rules, not claims
about what is already implemented or proved. The four that _are_ implemented
and proved are the ones stated above under
[Judgments and constructor views](#judgments-and-constructor-views) —
`callableGraph`, `callCallable`, `readCallable` and `writeCallable`, over the
$\mathsf{Callable}(\varphi;L)$ clause. Nothing below is in force.

The principal distinction is between checking an invocation implementation,
allocating an object carrying that implementation, and using the resulting
object through a contract.

#### Judgments and types

Write

```math
\Gamma\vdash_G t:A\;!E
```

for a computation whose normal results have type $A$ and whose thrown values
have type $E$. This is a safety judgment, not a termination guarantee. The
annotation bounds exceptions, not mutation. The unannotated judgment
abbreviates $E=\bot$.

Assumptions in $\Gamma$ are stable under permitted heap evolution. Assertions
about current contents belong in the state judgment introduced below.

Call and construction signatures are, respectively,

```math
\sigma=(R;\alpha)\xrightarrow{E}B,
\qquad
\nu=(N;\alpha)\xRightarrow{E}B.
```

Here $R$ constrains the supplied receiver, $\alpha$ constrains the actual
argument list, and $N$ constrains `new.target`. Construction signatures require

```math
N<:\mathsf{Ctor},
\qquad
B<:\mathsf{Obj}(\top_p).
```

Argument-list contracts need not specify an exact arity. Parameter binding,
defaults, and destructuring are computations in the function's entry program.

Define the constructor views

```math
\begin{aligned}
\mathsf{Calls}(L)
&=
\mathsf{Fun}\cap
\bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma),\\[2mm]
\mathsf{Callable}(L;P)
&=
\mathsf{Calls}(L)\cap\mathsf{Obj}(P),\\[2mm]
\mathsf{Constructor}(M;P)
&=
\mathsf{Ctor}\cap\mathsf{Obj}(P)\cap
\bigcap_{\nu\in M}\mathsf{ConstructSpec}(\nu).
\end{aligned}
```

$P$ is a property contract; $\top_p$ imposes no property requirement. In
particular,

```math
\mathsf{Calls}([])=\mathsf{Fun}.
```

An empty family supplies shape but no invocation contract.

Write $\mathsf{Plain}(P)$ for non-function objects satisfying $P$, and
$\mathsf{NoCtor}$ for objects without a construction operation. Neither asserts
an empty property store.

All operands in the operation rules below are values or previously bound
variables. Effectful operands are evaluated once, in source order, using
sequencing.

#### Structural views and intersections

**Forget-Properties** and **Forget-Calls** are the two essential forgetful
rules:

```math
\frac{\Gamma\vdash_G f:\mathsf{Callable}(L;P)}
{\Gamma\vdash_G f:\mathsf{Calls}(L)}
\qquad
\frac{\Gamma\vdash_G f:\mathsf{Callable}(L;P)}
{\Gamma\vdash_G f:\mathsf{Obj}(P)}.
```

These change the available view, not the value. Neither allocates nor wraps.

**Constructor-Shape.** Construction implies function shape, but supplies no
successful ordinary-call contract:

```math
\frac{\Gamma\vdash_G f:\mathsf{Constructor}(M;P)}
{\Gamma\vdash_G f:\mathsf{Callable}([];P)}.
```

**Sub.** The ordinary subsumption rule is

```math
\frac{
\Gamma\vdash_G t:A\;!E
\qquad G\vdash A<:B
\qquad G\vdash E<:F
}{
\Gamma\vdash_G t:B\;!F
}.
```

**Call-Sub.** For unconditional call signatures,

```math
\frac{
\begin{gathered}
G\vdash R_2<:R_1
\qquad G\vdash\alpha_2<:\alpha_1\\
G\vdash B_1<:B_2
\qquad G\vdash E_1<:E_2
\end{gathered}
}{
G\vdash
(R_1;\alpha_1)\xrightarrow{E_1}B_1
<:
(R_2;\alpha_2)\xrightarrow{E_2}B_2
}.
```

Construction signatures have the corresponding variance in `new.target`,
arguments, normal results, and exceptions.

The intended intersection laws are

```math
\mathsf{Calls}(L)\cap\mathsf{Obj}(P)
=
\mathsf{Callable}(L;P),
```

```math
\mathsf{Callable}(L;P)\cap\mathsf{Callable}(M;Q)
=
\mathsf{Callable}(L{+\!\!+}M;P\wedge Q).
```

Here $P\wedge Q$ is a conjunction of property contracts. It is not a pointwise
intersection of writable-cell content types.

**Value-Meet.** Intersection introduction on an already obtained value is

```math
\frac{\Gamma\vdash_G v:A\qquad\Gamma\vdash_G v:B}
{\Gamma\vdash_G v:A\cap B}.
```

Both premises concern the same value under compatible heap invariants.
Independently checking two allocations does not establish an intersection on
one allocated object.

#### Checking code and creating functions

Internal invocation descriptors are not source-level function values. Introduce
auxiliary judgments

```math
\Gamma\vdash_G^{\mathsf{call}}\kappa:L,
\qquad
\Gamma\vdash_G^{\mathsf{construct}}\eta:M,
\qquad
\Gamma\vdash_G^{\mathsf{init}}d:P.
```

The first two check invocation programs. The third checks an initial property
layout and the invariants it establishes. Initializer expressions have already
been evaluated.

**Ordinary functions: a dynamic receiver.** For strict ordinary-function code,
the rule **Dynamic** is

```math
\frac{
\left(
\Gamma,\mathsf{this}:R_i,\mathsf{argv}:\alpha_i
\vdash_G t:B_i\;!E_i
\right)_{i\in I}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{dyn}(\mathsf{this},\mathsf{argv}.t):
\left[(R_i;\alpha_i)\xrightarrow{E_i}B_i\right]_{i\in I}
}.
```

The entry program $t$ includes parameter initialization and the normal-return
convention.

For non-strict functions, the entry program first performs the specified
receiver conversion. The supplied receiver and the body's `this` value must not
simply be identified. ECMAScript distinguishes strict, non-strict, and lexical
receiver binding.

**Arrow functions: a lexical receiver.** The rule **Lexical** is

```math
\frac{
\left(
\Gamma,\mathsf{argv}:\alpha_i
\vdash_G t:B_i\;!E_i
\right)_{i\in I}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{lex}(\mathsf{argv}.t):
\left[(\top;\alpha_i)\xrightarrow{E_i}B_i\right]_{i\in I}
}.
```

The enclosing lexical environment in $\Gamma$ is captured. The rule introduces
no new source binding for `this`, `arguments`, `super`, or `new.target`;
$\mathsf{argv}$ is an internal parameter, not the source identifier
`arguments`. This corresponds to the lexical binding discipline of arrows.

A method uses Dynamic, with its home-object association in the captured
environment. A class-field arrow uses Lexical, with allocation performed during
instance initialization.

The stateful variants check the body under its invocation precondition. In
particular, capturing an initialization-sensitive lexical binding does not
require pretending that it was read at function creation.

**Allocation.** A callable without construction behaviour is introduced by
**Make-Function**,

```math
\frac{
\Gamma\vdash_G^{\mathsf{call}}\kappa:L
\qquad
\Gamma\vdash_G^{\mathsf{init}}d:P
}{
\Gamma\vdash_G
\mathsf{make}(\kappa,\mathsf{none},d):
\mathsf{Callable}(L;P)\cap\mathsf{NoCtor}
}.
```

A callable with construction behaviour is introduced by **Make-Constructor**,

```math
\frac{
\begin{gathered}
\Gamma\vdash_G^{\mathsf{call}}\kappa:L
\qquad
\Gamma\vdash_G^{\mathsf{construct}}\eta:M\\
\Gamma\vdash_G^{\mathsf{init}}d:P
\end{gathered}
}{
\Gamma\vdash_G
\mathsf{make}(\kappa,\eta,d):
\mathsf{Callable}(L;P)\cap
\mathsf{Constructor}(M;\top_p)
}.
```

An ordinary non-callable object is introduced by **Make-Object**,

```math
\frac{\Gamma\vdash_G^{\mathsf{init}}d:P}
{\Gamma\vdash_G
\mathsf{make}(\mathsf{none},\mathsf{none},d):
\mathsf{Plain}(P)}.
```

Every application of a make rule allocates one fresh object identity. There is
no rule with a construction descriptor but no call descriptor.

The first proposal's $\mathsf{attach}$ operation becomes a special case of
allocation. It is not the operation used to decorate a source function that
already exists.

#### Invocation, property calls, and extraction

**Call.** The ordinary application rule is

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Callable}(L;P)
\qquad (R;\alpha)\xrightarrow{E}B\in L\\
\Gamma\vdash_G r:R
\qquad \Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G\mathsf{invoke}(f,r,\bar a):B\;!E
}.
```

**Bare-Call.** For a bare call in the strict/module fragment,

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Calls}(L)
\qquad (R;\alpha)\xrightarrow{E}B\in L\\
G\vdash\mathsf{Undefined}<:R
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G f(\bar a):B\;!E
}.
```

**Method-Call.** A method call is lookup followed by invocation:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G\mathsf{get}(o,k,o):
\mathsf{Calls}(L)\;!E_g\\
(R;\alpha)\xrightarrow{E_c}B\in L
\qquad\Gamma\vdash_G o:R
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G o[k](\bar a):B\;!(E_g\vee E_c)
}.
```

For effectful source expressions, the elaboration evaluates the base and key,
performs lookup, evaluates the arguments, and invokes the retrieved function
with the saved base as receiver. It neither reevaluates the base nor binds a
receiver during lookup.

Method extraction is only lookup. Consequently, extraction preserves the
receiver requirement in the function's contract; it does not transform that
contract into a bound-function contract.

#### Properties

Property contracts expose operation signatures. For example,

```math
P\vdash_G\mathsf{get}(k):(R;[])\xrightarrow{E}A
```

states a contract for lookup at $k$, starting from an object satisfying $P$,
with a receiver in $R$.

The general rules are **Get** and **Set**:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G o:\mathsf{Obj}(P)
\qquad\Gamma\vdash_G r:R\\
P\vdash_G\mathsf{get}(k):(R;[])\xrightarrow{E}A
\end{gathered}
}{
\Gamma\vdash_G\mathsf{get}(o,k,r):A\;!E
},
```

```math
\frac{
\begin{gathered}
\Gamma\vdash_G o:\mathsf{Obj}(P)
\qquad\Gamma\vdash_G r:R
\qquad\Gamma\vdash_G a:A\\
P\vdash_G\mathsf{set}(k):(R;[A])
\xrightarrow{E}\mathsf{Bool}
\end{gathered}
}{
\Gamma\vdash_G\mathsf{set}(o,k,a,r):
\mathsf{Bool}\;!E
}.
```

Set returns an internal success flag. A strict source assignment throws on
failure and returns the assigned value on success. That differs from the
calculus's `write`, which returns $\mathsf{Null}$.

**Ordinary data properties.** For a stable, writable own-data-property
invariant, the reference-style rules are recovered as **Read-Cell** and
**Write-Cell**:

```math
\frac{
\Gamma\vdash_G o:\mathsf{Obj}(\{k:\mathsf{cell}(A)\})
}{
\Gamma\vdash_G\mathsf{read}_k(o):A
},
\qquad
\frac{
\Gamma\vdash_G o:\mathsf{Obj}(\{k:\mathsf{cell}(A)\})
\qquad\Gamma\vdash_G a:A
}{
\Gamma\vdash_G\mathsf{write}_k(o,a):\mathsf{Null}
}.
```

These apply to callables through Forget-Calls. The cell contract is invariant
and also protects the descriptor assumptions against unchecked deletion or
redefinition.

For a fresh property layout, **Init-Data** is

```math
\frac{\Gamma\vdash_G v:A}
{\Gamma\vdash_G^{\mathsf{init}}
[k\mapsto\mathsf{data}(v)]:
\{k:\mathsf{cell}(A)\}}.
```

**Accessors.** An own getter is checked by **Init-Getter**:

```math
\frac{
\Gamma\vdash_G g:
\mathsf{Calls}([(R;[])\xrightarrow{E}A])
}{
\Gamma\vdash_G^{\mathsf{init}}
[k\mapsto\mathsf{accessor}(g,\mathsf{none})]:
\{\mathsf{get}(k):(R;[])\xrightarrow{E}A\}
}.
```

Dually, a setter with call contract

```math
(R;[A])\xrightarrow{E}\top
```

supplies a set contract returning $\mathsf{True}$ on normal completion: the
setter's returned value is discarded. These rules assume the corresponding
descriptor invariants; inherited lookup additionally requires the
prototype-chain obligations.

General accessors and proxies use Get/Set, not Read-Cell/Write-Cell.

An ordinary property named `call` or `apply` supplies no premise for Call.

#### Construction

**Construct.**

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Constructor}(M;P)
\qquad (N;\alpha)\xRightarrow{E}B\in M\\
\Gamma\vdash_G n:N
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G
\mathsf{construct}(f,\bar a,n):B\;!E
}.
```

**New.** Ordinary `new` uses the constructor itself as `new.target`:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Constructor}(M;P)
\qquad (N;\alpha)\xRightarrow{E}B\in M\\
\Gamma\vdash_G f:N
\qquad\Gamma\vdash_G\bar a:\alpha
\end{gathered}
}{
\Gamma\vdash_G\mathsf{new}\ f(\bar a):B\;!E
}.
```

**Construction-Code.** The introduction rule checks the complete construction
program:

```math
\frac{
\begin{gathered}
\left(
\Gamma,\mathsf{newTarget}:N_i,\mathsf{argv}:\alpha_i
\vdash_G t_\eta:B_i\;!E_i
\right)_{i\in I}\\
(G\vdash N_i<:\mathsf{Ctor})_{i\in I}
\qquad
(G\vdash B_i<:\mathsf{Obj}(\top_p))_{i\in I}
\end{gathered}
}{
\Gamma\vdash_G^{\mathsf{construct}}
\mathsf{constructCode}(\mathsf{newTarget},\mathsf{argv}.t_\eta):
[(N_i;\alpha_i)\xRightarrow{E_i}B_i]_{i\in I}
}.
```

This program includes receiver allocation, prototype lookup, instance
initialization, and explicit-return handling. Derived constructors additionally
require `super` and initialization of `this`. Checking the source body as an
ordinary function returning $B$ is insufficient.

A contract proved only for ordinary `new` may restrict $N$ to the constructor's
own identity. It must not silently become a guarantee for arbitrary
`Reflect.construct` calls.

A class's ordinary-call descriptor can have the exception-aware signature

```math
(\top;\mathsf{Args})
\xrightarrow{\mathsf{TypeError}}\bot.
```

Thus it has function shape without a successful ordinary-call contract.

#### Overloads, polymorphism, and binding

**Overloads.** The premises of Dynamic and Lexical check the same code against
every advertised signature before allocating one function object. Call selects
an applicable member. Forgetting members is subsumption; no writable
implementation cell is retyped.

**Generic signatures.** Let $S$ be a scheme row, $\eta_0$ the assignment
outside its binders, and $\mathsf{Instance}_{G,P}(\eta_0,S,\eta)$ the
reassignments of its binders within their bounds, $\eta_0$ unchanged outside
them (`Bounded`), as
[POSITIVE-TYPES.md](POSITIVE-TYPES.md#quantified-scheme-layer) defines. The exact
introduction rule **Call-Scheme-I**, which unfolds the definition of scheme
membership (`schemeSemWithArgs`), is

```math
\frac{
\mathsf{Invocable}(v)
\qquad
\forall\eta.\;
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
\Rightarrow
(\mathsf{Calls}(\mathsf{Sig}_{G,P,\eta}(S),n,W,v)
\land\mathsf{Rests}(\mathsf{RestSig}_{G,P,\eta}(S),n,W,v))
}{
⟦S⟧^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
}.
```

The value $v$, step index $n$, world $W$, and outer assignment $\eta_0$ are
outside the quantifier. The proof is therefore uniform in the binders, and
captured mutable cells retain the same invariant at every instantiation.
Fixed-signature elimination **Call-Scheme-E**, by the same unfolding, is

```math
\frac{
⟦S⟧^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
\qquad
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
}{
\mathsf{Calls}(\mathsf{Sig}_{G,P,\eta}(S),n,W,v)
}.
```

The same premises give the corresponding conclusion for the rest
signatures, $\mathsf{Rests}(\mathsf{RestSig}_{G,P,\eta}(S),n,W,v)$, from the
same premises: an instance's contract is both (`instanceTWithArgs`).

A call names its instance: the callee is read at the instance's signatures,
below the scheme by a checked instance table (`InstArrs`), which constructs one
such $\eta$ after the type arguments' bounds are checked. It selects a
signature of the same callable; it neither allocates a new value nor changes
the outer assignment. These are rules for quantified invocation contracts, not
unrestricted generalization of an effectful allocation expression. One
callable value and one captured world satisfy every admissible assignment,
while elimination selects a signature only afterwards. A generic closure is
graph code at a scheme row (**funScheme**,
[above](#judgments-and-constructor-views)), its introduction the table's check
of its code, which holds at every assignment, a rest, a default or a binder
bounded by another included.

**Generic bodies.** A generic function's body is a graph request whose
binders are parameter rows $\vec p$: rows the graph's assignment interprets,
which no rule reads (a type holding one has no expansion). Acceptance does not
read the assignment (`accept_reassign` in [Parametricity.lean](lean/Verification/Model/Programs/Parametricity.lean)), so the rule
**Generic-Body** is the ordinary safety theorem at every reassignment:

```math
\frac{
\mathsf{accept}(G,R,P,\mathit{claims},C,s,\vec I)=\mathsf{true}
\qquad
\mathsf{EnvOk}_{G[\mathit{env}:=\eta]}(\vec I,\rho,n,W)
\qquad \mathsf{WorldAdm}(W)\qquad \mathsf{HeapOk}(n,W,h)
}{
\mathsf{SafeGraph}\bigl(P,⟦R⟧^{\eta},n,W,h,\mathsf{at}(s,\rho)\bigr)
}
\quad\text{for every }\eta .
```

One derivation, checked once, covers every instantiation of the binders: the
inputs and the result are read at the same $\eta$. A bounded binder is read as
the meet of its row and its bound, and one bounded by another binder as the
meet of the two ([binders met](#binders-met-with-ground-types)); at every
instantiation within the bounds the meets are the binders, and the body is
certified at the others too. Every generic unit takes this one path. The
binders of a generic class are those of the unit that declares it, the
module's initialization unit, so its constructor and methods are certified at
every instantiation the same way. Lean:
`Parametricity.accepted_at`, `RequestJson.verify_safe_at`,
`SourceExtraction.checkRequests_safe_at`.

**Bound functions.** The internal bound-call descriptor has the rule
**Bound-Code**:

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:
\mathsf{Calls}([(R;\alpha{+\!\!+}\beta)
\xrightarrow{E}B])\\
\Gamma\vdash_G r:R
\qquad\Gamma\vdash_G\bar p:\alpha
\end{gathered}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{bound}(f,r,\bar p):
[(\top;\beta)\xrightarrow{E}B]
}.
```

Allocation gives this descriptor a fresh identity and its own properties. The
target's property contract is not copied.

For construction, a bound object $g$ forwards as

```math
\begin{aligned}
&\mathsf{construct}(g,\bar a,n)\\
&\quad\rightsquigarrow
\mathsf{construct}\left(
f,\bar p{+\!\!+}\bar a,\,
\mathsf{if}\ \mathsf{same}(n,g)\
\mathsf{then}\ f\
\mathsf{else}\ n
\right).
\end{aligned}
```

Its construction contracts must be checked against this program; the bound
receiver is not used as the constructed receiver.

Source `f.call`, `f.apply`, and `f.bind` remain property lookups followed by
calls. Specialization requires the retrieved operation to be the standard
intrinsic. Argument extraction and the prototype, name, and length operations
of the full binding algorithm are separately checked computations. Bound-Code
is not a blanket no-effect rule for `.bind`.

#### Stateful contracts

Use the additional judgment

```math
\Gamma\vdash_G
\{\Phi\}\ t\
\{z:B.\Psi\mid e:E.\Xi\}.
```

It specifies normal and exceptional postconditions. The ordinary judgment is the
special case with no additional precondition or postcondition beyond type
safety and the ambient invariants. It is the exception-aware form of the
[Hoare typing above](#checked-expression-postconditions), whose $\Pi$ and
$\Sigma$ are one way of writing $\Phi$ and $\Psi$.

A stateful call signature is

```math
\sigma=
(r:R;\mathsf{argv}:\alpha)
\{\Phi\}
\Rightarrow
\{z:B.\Psi\mid e:E.\Xi\}.
```

Contracts may refer to a distinguished $\mathsf{self}$ denoting the callable.
Let $\theta$ substitute the actual callable, receiver, and argument list for
these formal names. **Call-State** is

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Callable}(L;P)
\qquad \sigma\in L\\
\Gamma\vdash_G r:R
\qquad\Gamma\vdash_G\bar a:\alpha
\qquad\Phi_0\vdash\Phi\theta
\end{gathered}
}{
\Gamma\vdash_G
\{\Phi_0\}\mathsf{invoke}(f,r,\bar a)
\{z:B.\Psi\theta\mid e:E.\Xi\theta\}
}.
```

The corresponding introduction rule checks the entry body under $\Phi$ and
establishes $\Psi,\Xi$. Construction, lookup, and update have the same stateful
form.

Only facts supported by postconditions, stable invariants, or a justified frame
rule survive a call. A transient observation is not promoted into a permanent
callable or property type.

**Decoration.** A representative strong property-addition rule is

```math
\frac{
\begin{gathered}
\Gamma\vdash_G f:\mathsf{Callable}(L;P)
\qquad\Gamma\vdash_G a:A\\
\mathsf{AddOK}_G(\Phi,f,k,A;P)
\end{gathered}
}{
\begin{gathered}
\Gamma\vdash_G
\{\Phi\}\mathsf{defineOwn}(f,k,a)\\
\{z:\mathsf{Callable}(L;P\wedge\{k:\mathsf{cell}(A)\}).
\ z=f
\mid e:\bot.\bot\}
\end{gathered}
}.
```

Here `defineOwn` is a core operation returning its target.

$\mathsf{AddOK}$ is a checked object-store obligation: the target is eligible,
the slot is available, the update is permitted, and the invariant extension
preserves established contracts. It cannot be discharged merely because the
call descriptor is immutable: behaviour can depend on properties.

Without those conditions, the general stateful property-definition contract is
required instead.

The postcondition $z=f$, rather than freshness, distinguishes decoration from
wrapping.

**Proxies and revocation.** The shape-only creation rule, **Proxy-Shape**, is

```math
\frac{
\Gamma\vdash_G f:\mathsf{Fun}
\qquad\Gamma\vdash_G h:\mathsf{Obj}(\top_p)
}{
\Gamma\vdash_G\mathsf{proxy}(f,h):\mathsf{Fun}
}.
```

There is no rule automatically copying the target's signatures. A stronger
contract requires checking the dispatch program: revocation check, handler
lookup, and target or trap invocation. Those operations can change the
behaviour relative to the target.

For a callable revocable proxy $q$, the state rules include

```math
\Gamma\vdash_G
\{\mathsf{Revocable}(q)\}\mathsf{revoke}(q)
\{z:\mathsf{Undefined}.\mathsf{Revoked}(q)
\mid e:\bot.\bot\},
```

```math
\Gamma\vdash_G
\{\mathsf{Revoked}(q)\}\mathsf{invoke}(q,r,\bar a)
\{z:\bot.\bot
\mid e:\mathsf{TypeError}.\top\}.
```

The core revocation operation requires the associated revocation capability.
The stable fact $q:\mathsf{Fun}$ survives. Liveness alone does not establish a
nonthrowing signature; handler and target obligations remain.

#### Shape tests and identity

SKJS's call modes obtain the following views:

| Mode          | View                                                 | $\mathsf{isFun}$ |
| ------------- | ---------------------------------------------------- | ---------------- |
| `CPresent(L)` | $\mathsf{Callable}(L;P)$, with advertised signatures | true             |
| `CFunction`   | $\mathsf{Callable}([];P)$                            | true             |
| `CAbsent`     | $\mathsf{Plain}(P)$                                  | false            |
| `CUnknown`    | $\mathsf{Obj}(P)$                                    | unknown          |

This retains SKJS's distinction between known function shape and unknown
callability, while supplying the structural object view.

**Function-Test.** For an unknown-callability object,

```math
\frac{
\begin{gathered}
\Gamma,x:\mathsf{Callable}([];P)
\vdash_G t:B\;!E_t\\
\Gamma,x:\mathsf{Plain}(P)
\vdash_G u:B\;!E_u
\end{gathered}
}{
\Gamma,x:\mathsf{Obj}(P)\vdash_G
\mathsf{if}\ \mathsf{isFun}(x)\
\mathsf{then}\ t\
\mathsf{else}\ u
:B\;!(E_t\vee E_u)
}.
```

The true branch gains shape, not an arbitrary signature. Graph slicing must
represent or safely approximate the refined views.

**Identity.** Object identity has the rule

```math
\frac{
\Gamma\vdash_G f:\mathsf{Obj}(\top_p)
\qquad
\Gamma\vdash_G g:\mathsf{Obj}(\top_p)
}{
\Gamma\vdash_G\mathsf{same}(f,g):\mathsf{Bool}
}.
```

Its refinement postcondition is

```math
b\iff\mathrm{id}(f)=\mathrm{id}(g).
```

Allocation additionally establishes freshness relative to identities existing
at entry. Subsumption establishes neither allocation nor freshness.

#### Async and generator callables

Their application uses Call. Their introduction needs additional computation
judgments, not additional callable-object representations.

What is implemented is weaker and trusted: `await` and an async body's returns
are calls of intrinsic values at declared signatures, and **Await**,
**Async-Return** and **Async-Complete** are instances of Call
([async functions and await](#async-functions-and-await)).
The judgments below remain the target that would discharge that trust.

An asynchronous entry judgment

```math
\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha
\vdash_G^{\mathsf{async}}
t:\mathsf{PromiseSpec}(B,E)
```

must check entry and resumption, including parameter initialization, promise
resolution, thenable assimilation, rejection, and state invariants across
suspension. These are obligations of the asynchronous execution semantics.

Its introduction schema, **Async-Code**, is

```math
\frac{
\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha
\vdash_G^{\mathsf{async}}
t:\mathsf{PromiseSpec}(B,E)
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{asyncCode}(t):
[(R;\alpha)\xrightarrow{\bot}
\mathsf{PromiseSpec}(B,E)]
}.
```

This schema assumes the entry proof accounts for ordinary entry failures as
rejections; other synchronous failure paths must be advertised separately.
$\mathsf{PromiseSpec}$ constrains fulfillment and rejection, not eventual
settlement.

For generators, let $\Pi$ be a protocol describing operations and transitions,
including `next`, `throw`, and `return`. Then **Generator-Code** is

```math
\frac{
\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha
\vdash_G^{\mathsf{generator}}
t:\Pi\;!E_{\mathrm{entry}}
}{
\Gamma\vdash_G^{\mathsf{call}}
\mathsf{generatorCode}(t):
[(R;\alpha)\xrightarrow{E_{\mathrm{entry}}}
\mathsf{Generator}(\Pi)]
}.
```

A protocol transition supplies a stateful contract for the corresponding
method. It must account for suspension, completion, and subsequent operations
on a completed generator.

These last two are module interfaces. Defining their premises requires an
async/coroutine logic; merely giving the names of those judgments does not
provide that logic.

#### A distinguishing instance

Let

```math
D=\mathsf{Obj}(\{n:\mathsf{cell}(\mathsf{Number})\}),
```

```math
M=(D;[])\to\mathsf{Number},
\qquad
A=(\top;[])\to\mathsf{Number}.
```

For a checked incrementing body, Dynamic gives $M$ to an ordinary method.
Lexical gives $A$ to an arrow capturing an instance of $D$.

After allocation, suppose

```math
m:\mathsf{Calls}([M]),
\qquad
a:\mathsf{Calls}([A]),
\qquad
o:D.
```

Then

```math
\Gamma\vdash_G
\mathsf{invoke}(m,o,[]):\mathsf{Number},
```

```math
\Gamma\vdash_G
\mathsf{invoke}(a,\mathsf{undefined},[]):\mathsf{Number}.
```

The available contract for $m$ does not justify supplying `undefined` instead
of $o$. Binding $m$ to $o$ produces a fresh function with a top-receiver
contract. Decorating $m$, under Decorate, preserves its identity. A plain
object containing $m$ in a property has a property-read rule, but no Call rule
for the object itself.

That is the intended separation: creation determines identity and dispatch;
contracts determine permitted operations; subsumption changes neither.

### The actual completeness claim

There are three distinct deliverables.

**A complete callable architecture** gives every pattern above a place without
changing representations when types change. C\* provides that target.

**A sound verification account** defines the operations and contracts, proves
the typing and state rules sound, and proves source elaboration preserves the
chosen observations. That includes identity, receiver binding, mutation,
exceptions, and any admitted asynchronous observations.

**A complete automated checker** is a separate claim. Neither object
representation establishes that the current certificate language can express
every required property or that its checker can discharge every valid
obligation.

This section establishes neither of the latter two deliverables. The one-cell
callable slice described above is implemented and proved in Lean; the fuller
architecture and rules below that slice remain proposed extensions.

[c1]: https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html "6 ECMAScript Data Types and Values - TC39"
[c2]: https://tc39.es/ecma262/multipage/ecmascript-language-functions-and-classes.html "ECMAScript® 2027 Language Specification"
[c3]: https://tc39.es/ecma262/multipage/fundamental-objects.html "ECMAScript® 2027 Language Specification"
[c4]: https://tc39.es/ecma262/multipage/control-abstraction-objects.html "ECMAScript® 2027 Language Specification"
[c5]: https://www.typescriptlang.org/docs/handbook/2/functions.html "Documentation - More on Functions - TypeScript"
[c6]: https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html "ECMAScript® 2027 Language Specification"
[c7]: https://tc39.es/ecma262/multipage/ordinary-and-exotic-objects-behaviours.html "ECMAScript® 2027 Language Specification"
