# Program typing over positive recursive types

[ProgramTyping.lean](lean/Verification/Model/Programs/ProgramTyping.lean) gives
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
| $\operatorname{pred}(A)$ | the predicate disjunction $A$ denotes, defined for supported primitives (`HeapKnowledge.atoms`)       |
| $G$                      | the normalized positive graph                                                                         |
| $\Gamma$                 | a typing context, one type per variable                                                               |
| $\Pi$, $\Sigma$          | the [equality and heap parts](#checked-expression-postconditions) of the assertion state              |
| $\rho$, $h$, $W$, $n$    | an environment, heap, world and budget, from [the model](SEMANTICS.md#types-worlds-and-heaps)         |
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

A numeric literal has the same pair and only that pair: `numLit` gives it its
own singleton, and `num` gives it the family. Neither reaches a union above
either one; that is the subsumption rule's work, exactly as for a Boolean. A
literal claimed at $\mathsf{Number}$ need not have a singleton label in the graph to be coerced from,
which is why the family rule is separate rather than derived.

$$
\frac{}{\Gamma\vdash_G n:\mathsf{numLit}(n)}
\qquad
\frac{}{\Gamma\vdash_G n:\mathsf{Number}}.
$$

A bigint literal has the same pair, `bigintLit` and `bigint`:

$$
\frac{}{\Gamma\vdash_G i\mathtt{n}:\mathsf{bigintLit}(i)}
\qquad
\frac{}{\Gamma\vdash_G i\mathtt{n}:\mathsf{BigInt}}.
$$

Functions take ordered parameter lists and a receiver. Write $\vec A$ for a
signature's parameter types, $|\vec A|$ for its length and $R$ for its
receiver: the `this` a call passes, which is not a parameter. In the
ordinary-closure creation rule below, every signature offers at least the
descriptor's arity, and its body is typed under that signature's receiver,
then its first $\mathit{arity}$ parameters, then the captured bindings. A
signature may offer more: the call binds the first $\mathit{arity}$ actuals
and discards the rest, as JavaScript does. One lemma,
`invocationSpec_of_instantiated`, turns a checked body into the code's
contract for every code-creating rule (functions, callable objects, classes,
and the parametric and generic layers), and the rules, certificates and search
share one context (`bodyFrame`) and one check (`offersArity`). Variadic code
keeps exact fixed parameters: its extra actuals go to the rest, not away.
This holds of the code, not of any value at a shorter signature: a variadic
function collects extra actuals and a bound one forwards them, so no subtyping
rule widens an arrow's parameters. For the same reason the ordinary closure
also meets a variadic signature $(R;\vec A,\ldots E\to B)$ whose fixed
parameters cover its arity: a call through it writes any number of actuals,
the code binds its first $\mathit{arity}$, all at fixed positions, and
discards the rest (`restsT_of_invocationSpec`). Its body is checked at that
signature's fixed row $(R,\vec A,B)$, with the fixed signatures
(`offerRows`); a closure binding a position of the rest, which a call may
leave unwritten, is not created at it. A call passes its receiver $r$ and
types it at the selected signature's receiver:

$$
\frac{\forall(R,\vec A,B)\in L\cup S^\flat.\;\mathit{arity}\le|\vec A|
      \quad\forall(R,\vec A,B)\in L\cup S^\flat.\;\Gamma,\mathit{this}{:}R,\vec x{:}\vec A_{<\mathit{arity}}\vdash_G t:B}
     {\Gamma\vdash_G \lambda\vec x.t:\bigwedge_{(R,\vec A,B)\in L}(R;\vec A\to B)
       \land\bigwedge_{(R,\vec A,E,B)\in S}(R;\vec A,\ldots E\to B)}
\qquad
\frac{\Gamma\vdash_G f:\bigwedge_{(Q,\vec C,D)\in L}(Q;\vec C\to D)
      \quad(R,\vec A\,\vec U,B)\in L\quad\Gamma\vdash_G r:R\quad\forall i.\;\Gamma\vdash_G a_i:A_i
      \quad\forall U\in\vec U.\;\Gamma\vdash_G \mathsf{undefined}:U}
     {\Gamma\vdash_G \mathsf{invoke}(f,r,\vec a):B}
$$

with $S^\flat=\{(R,\vec A,B)\mid(R,\vec A,E,B)\in S\}$. A plain call $f(\vec a)$ is $\mathsf{invoke}(f,\mathsf{undefined},\vec a)$. In
de Bruijn form the receiver's slot precedes the parameters, $\mathit{this}$
then $\vec x$, before the captures; an arrow's code has that slot too and
never reads it, and a source `this` in an arrow resolves to an enclosing
ordinary function's slot as a capture. The rule's receiver premise is
contravariant under subsumption like each domain
([`CallArrow`](POSITIVE-TYPES.md#function-and-class-coverage)), so a
function indifferent to its receiver, typed at $\top$, meets any receiver
requirement, and one that reads its receiver cannot be widened to arbitrary ones.

A call writes a prefix of the positions the selected signature declares:
$|\vec a|=|\vec A|$, and $\vec U$ are the positions it omits. Omission is
admissible exactly when each omitted contract admits `undefined`: that is part
of what the signature promises (below), and closure code keeps the promise
because `CallArguments.parameters` pads a short actual list, so the body
dispatched for $f(\vec a)$ is the same term as for the call that writes those
`undefined`s out (`CallArguments.parameters_pad`, used once, in
`callsT_of_invocationSpec`). With $\vec U$ empty this is the exact-arity rule.
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
That array is fresh, so a rest parameter's contract may also be `readonly`
(`readonly T[]`, a readonly tuple) or name one through a declared alias: the
body sees the fresh array through that view, which gives up only writes.

A function type is a promise about the actual lists a caller may write, not
about the callee's code. A fixed signature $\vec A\to B$ admits the prefixes of
$\vec A$ whose omitted positions admit `undefined`. A variadic signature
$\vec A,\ldots P\to B$ has a rest type $P$, an [argument pack](POSITIVE-TYPES.md#argument-packs):
it admits the lists whose first actuals $\vec A$ admits, as a fixed signature
does, and whose actuals past them are, as one list, in $P$'s argument lists,
at the current level (`argMeaning`). An element rest `...xs: E[]` admits any
number of actuals in $E$, $\mathsf{Pack}([\,],[\,],E)$ (`restElem_args`); a
tuple rest `...xs: [A, B]` exactly those positions:

$$
\operatorname{Adm}(\vec A)=\{\vec v\mid |\vec v|\le|\vec A|,\ \forall i<|\vec v|.\,v_i\in A_i,\ \forall |\vec v|\le i<|\vec A|.\,\mathsf{undefined}\in A_i\}
$$

$$
\operatorname{Adm}(\vec A;P)=\{\vec v\mid \vec v_{<|\vec A|}\in\operatorname{Adm}(\vec A),\ \mathsf{args}(\vec v_{\ge|\vec A|})\in P\}
\qquad(\texttt{ArgsRest}).
$$

A list shorter than $\vec A$ passes the empty pack, which an element rest
admits and a tuple rest with required positions does not.

A value meets a signature when every admitted list of values invokes it safely
at $B$, at every later world and budget (`Safety.Promise`, `callsT`, `restsT`).
This instantiates the [common behavioral equation](SEMANTICS.md#one-meaning-for-callable-contracts),
which also explains overload conjunction, callable fields and quantification.
Code enters only where it is created: closure code pads a short list
(`callsT_of_invocationSpec`), and variadic code collects the actuals past its
$k$ fixed parameters into a fresh array, which the term invocation yields
allocates with the ordinary steps (`RestCalls.restsT_of_restSpec`):

$$
\operatorname{invoke}(\langle k,t\rangle^{\ldots},\vec v)=
\mathsf{let}\ r=\mathsf{alloc}\{[\,]:\mathsf{arr}(v_k,v_{k+1},\ldots)\}\ \mathsf{in}\ t[\vec x:=\operatorname{pad}_k(\vec v)]
\qquad(\texttt{bindRest})
$$

A pack holds its actuals at their positions only below the current level. The
allocation is a step, after which the budget is one lower, so that is all the
fresh store's contracts need (`arr_alloc_rule_below`, `pack_alloc_safe`).

So one value may meet fixed and variadic signatures at once, and a graph call
clause carries both: `arrs L S`, `callable P Ps L S`. Write
$\operatorname{Store}_G(Q,P)$ when $Q$ is the store $P$'s one tuple contract
describes, writable since the store is fresh (`RestStore`), and $\operatorname{Spreads}_G(S,E)$ when $S$ is a
store contract every position of which is within $E$ (`SpreadsInto`); a typed
store has no hole, so a spread yields no $\mathsf{undefined}$ its positions do
not hold. Creation checks the body once per variadic signature, with the
rest store in slot 0, the receiver in slot 1, then the fixed parameters
(`funRest`; `makeCallableRest` adds a field bag as `makeCallable` does). The
body's first step wraps the store into the array the rest parameter names, an
ordinary allocation the extractor emits:

$$
\frac{\forall(\vec A,P,B)\in S.\;|\vec A|=k\quad\operatorname{Store}_G(Q_{\vec A,P,B},P)
      \quad\Gamma,\vec x{:}\vec A,r{:}Q_{\vec A,P,B}\vdash_G t:B}
     {\Gamma\vdash_G \lambda\vec x,\ldots r.\,t:\textstyle\bigwedge_{(\vec A,P,B)\in S}(\vec A,\ldots P\to B)}
$$

A call writes the fixed actuals, or a prefix whose omitted positions admit
`undefined`, then parts that fit the rest; a call that omits a fixed position
writes no part (`callRest`). With a spread among the parts, the rest is an
element rest $\mathsf{Pack}([\,],[\,],E)$ ($\operatorname{elem}_G(P)=E$,
`restElem`), and each part is an actual in $E$ or a spread of a store whose
elements are. Without one, $P$ is one tuple contract $\tau$, and the parts are
at its positions within its length bounds (`RestParts`):

$$
\frac{\begin{array}{c}\Gamma\vdash_G f:F\quad(\vec A\,\vec U,P,B)\in\operatorname{restSigs}_G(F)
      \quad\forall i.\;\Gamma\vdash_G a_i:A_i\quad\forall U\in\vec U.\;\Gamma\vdash_G\mathsf{undefined}:U\\
      \vec U=\varepsilon\lor\vec p=\varepsilon\qquad\operatorname{Parts}_G(P,\vec p)\end{array}}
     {\Gamma\vdash_G f(\vec a,\vec p):B}
$$

$$
\operatorname{Parts}_G(P,\vec p)\iff
\begin{cases}
\operatorname{elem}_G(P)=E\ \land\ \forall p\in\vec p.\;\Gamma\vdash_G p:E\ \lor\ (p={\ldots}s\land\Gamma\vdash_G s:S\land\operatorname{Spreads}_G(S,E)) & \text{a spread in }\vec p\\
P=\mathsf{Pack}(\tau)\ \land\ |\tau.R|\le|\vec p|\ \land\ (\tau.E=\varnothing\Rightarrow|\vec p|\le|\tau.R|+|\tau.O|)\ \land\ \forall i.\;\Gamma\vdash_G p_i:\mathsf{pos}_\tau(i) & \text{otherwise}
\end{cases}
$$

The first case is `rest_call_safe`: the actuals collected at $E$ form a list
the element rest admits (`restElem_args`). The second is `pack_call_safe`: the
actuals at the positions form a list $\tau$ admits (`restParts_pack`). The
rest store is allocated from those actuals at the current level; the
allocation step consumes the level (`restStore_safe`,
`RestCalls.argument_alloc_safe`).

A spread is read by the call once every earlier actual is a value, the store's
elements replacing it in order, `undefined` at a hole
(`Step.callSpread`, `spread_parts_safe`):

$$
(h,\ f(\vec v,\ {\ldots}\mathsf{arr}(\vec\ell),\ \vec p))\longrightarrow
(h,\ f(\vec v,\ h(\ell_1),\ldots,h(\ell_m),\ \vec p))
$$

A spread followed by an actual that runs code is copied where it is written,
`[...s]`, a fresh store the call then spreads, so the later actual cannot
change what it passes (`Step.arrSpread`, `copy_safe`, `arrCopy`):

$$
\frac{\Gamma\vdash_G s:S\quad\operatorname{Spreads}_G(S,E)}
     {\Gamma\vdash_G [{\ldots}s]:\mathsf{List}([\,],[\,],E)}
$$

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

$$
\frac{k=|\vec P|\le|\vec A|\quad\forall i<k.\;A_i\le P_i\quad\operatorname{elem}_G(P')=E\quad\forall k\le i<|\vec A|.\;A_i\le E\quad B\le D}
     {(\vec P,\ldots P'\to B)\le(\vec A\to D)}
$$

$$
\frac{k=|\vec P|\le|\vec Q|\quad\forall i<k.\;Q_i\le P_i\quad
      (k=|\vec Q|\ \lor\ \operatorname{elem}_G(P')=E\land\forall k\le i<|\vec Q|.\;Q_i\le E)\quad Q'\le P'\quad B\le D}
     {(\vec P,\ldots P'\to B)\le(\vec Q,\ldots Q'\to D)}
$$

$$
\frac{Q'=\mathsf{Pack}(\vec E)\ \text{exact}\quad\forall E\in\vec E.\,\mathsf{stable}(E)\quad
      |\vec P|=|\vec Q\vec E|\quad\forall i.\;(\vec Q\vec E)_i\le P_i\quad B\le D}
     {(\vec P\to B)\le(\vec Q,\ldots Q'\to D)}
$$

$$
\frac{\Gamma\vdash_G a:A\quad\Gamma,x:A\vdash_G b:B}
     {\Gamma\vdash_G \mathsf{let}\ x=a\ \mathsf{in}\ b:B}
$$

A bound function (`bindE`) is allocated from saved slots: the target $f$, the
receiver $r$ and the prefix $\vec p$, whose types the rule reads from the
context. The target's selected signature starts with the prefix's types; the
result takes the rest, at any receiver, since invoking it drops the receiver it
is given (`CallCode.bound`, `callsT_bound`):

$$
\frac{\Gamma(f)=F\quad(R,\vec P\,\vec D,B)\in\operatorname{callSigs}_G(F)
      \quad\Gamma(r)=R\quad\Gamma(\vec p)=\vec P}
     {\Gamma\vdash_G\mathsf{bound}(f,r,\vec p):(Q;\vec D\to B)}
$$

A method member is host-relative: its contract holds when it is invoked on
the object it is read from ([DESIGN.md](DESIGN.md#method-members-are-host-relative)).
A member bound to its host (`bindMember`) is read from the object in slot $i$
and bound to that same object in one term, so the member is read before any
actual runs, as JavaScript reads it, and the bound function meets the member's
signatures at any receiver, and every fixed signature one of them covers:
each claimed parameter within the member's, and the member's result within
the claimed one, by checked subtyping proofs the certificate carries
(`CoveredCall`, `CallProofs`). A claim may so name another row for the same
type, as a producer's own row for a declared `[number, number]`. With
$\operatorname{member}_G(O,k)=m$ the method of key $k$ in $O$'s one object
clause (`memberOf`):

$$
\frac{\Gamma(i)=O\quad\operatorname{member}_G(O,k)=m
      \quad\forall(Q,\vec D,B)\in L.\;\exists(\vec C,B')\in m.\mathsf{calls}.\;
        G\vdash\vec D\le\vec C\land G\vdash B'\le B
      \quad\forall(Q,\vec D,P,B)\in S.\;(\vec D,P,B)\in m.\mathsf{rests}}
     {\Gamma\vdash_G\mathsf{let}\ f=i.k\ \mathsf{in}\ \mathsf{bound}(f,i,[]):\mathsf{arrs}(L;S)}
$$

The member read from $v=\rho(i)$ meets $m$'s signatures with receiver $\{v\}$
(`memberOf_at`, `MethodMembers.onHost`). The read finds the key on $v$, or, one
step later, on the object $v$'s prototype holds (`Step.readProto`,
`member_read_safe`), as the member's meaning says. The bound descriptor, which has
no fields and allocates nothing, forwards any call to it with receiver $v$
(`callsT_bound`, `restsT_bound`).

A variadic target with an element rest (`bindRestE`, `restsT_bound`) gives
its first fixed positions to the prefix and, past them, its element $E$; the
result keeps the positions left and the rest $P$, which admits the prefix's
values past the fixed positions in front of any list it admits:

$$
\frac{\Gamma(f)=F\quad(R,\vec P,P',B)\in\operatorname{restSigs}_G(F)\quad\operatorname{elem}_G(P')=E
      \quad\Gamma(r)=R\quad\Gamma(\vec p)=\vec P_{<k}\,E^{\,k-|\vec P|}\quad k=|\vec p|}
     {\Gamma\vdash_G\mathsf{bound}(f,r,\vec p):(Q;\vec P_{\ge k},\ldots P'\to B)}
$$

Here $\lambda\vec x.t$ denotes source function creation, implemented as `funE t`: it
allocates an object before any invocation. `let` has its own operational constructor, `letE a b`. It evaluates `a`,
then substitutes the resulting value into `b` in one nonallocating step.
Neither a function value nor a function-type graph label is needed. The
producer and consumer use this constructor directly; lambda application no
longer has a special binding-certificate route.

A class value is construct-only code: JavaScript gives a function object
`[[Call]]` and `[[Construct]]` separately, and a class has only the second,
an arrow only the first. The calculus records which in the closure's code
(`kind`), a plain call dispatches only call code, and `new f(args)` is its own
term, which evaluates `f`, then the actuals, and runs only construct code, with
`undefined` for the receiver. A construct signature
$\mathsf{new}(A_1,\ldots,A_n)\Rightarrow B$ (the `ctors` clause) is met by a
class whose body, for actuals at the parameters, is safe at $B$. As for a
function, a signature may offer more parameters than the constructor binds:
the construct step binds its first $\mathit{arity}$ actuals and discards the
rest, so the body is typed at the signature's first $\mathit{arity}$
parameters:

$$
\frac{L\equiv_G\mathsf{Ctors}(\ldots,(\vec A,B),\ldots)\quad
      U\equiv_G\mathsf{Undefined}\quad
      \mathit{arity}\le|\vec A|\quad
      U,\vec x{:}\vec A_{<\mathit{arity}},\Gamma\vdash_G b:B\ \text{for each signature}}
     {\Gamma\vdash_G \mathsf{class}(\vec x).b : L}
\qquad
\frac{\Gamma\vdash_G f:L\quad L\equiv_G\mathsf{Ctors}(\ldots,(\vec A\,\vec U,B),\ldots)\quad
      \Gamma\vdash_G a_i:A_i\quad\Gamma\vdash_G\mathsf{undefined}:U_j}
     {\Gamma\vdash_G \mathsf{new}\ f(\vec a):B}
$$

These are `ctorE` and `construct`. As a call may, `new` may omit trailing
positions $\vec U$ whose contracts admit `undefined`: the construct step binds
`undefined` there, so the body entered is the one the padded list enters
(`bindParameters_pad`), and the source term keeps the actuals it writes. A
`new` with explicit type arguments, `new C<T>()`, names the instance of a
generic class it constructs: the producer proposes that instantiation, and it
is checked as an inferred one is ([DESIGN.md](DESIGN.md#modules-and-code-units)). No arrow meets a construct signature and no
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
read as an array, owning none of `ArrayProto`'s keys, by subsumption:

$$
\frac{\overline{f}\ \text{distinct}\qquad\forall i.\;\Gamma\vdash_G a_i:A_i
      \qquad\forall b\in\beta.\;\forall f\in\overline{f}.\;b\vDash f}
     {\Gamma\vdash_G\{\overline{f=a}\}:\mathsf{Ref}(\overline{f{:}A};\beta)}
$$

`read` and `write` name the field they act on and require it of the receiver's
contract. A contract constrains only the fields it names, so a receiver may
carry fields the rule never mentions — width subtyping is this openness, not a
separate rule. A read takes the field from the receiver's **named members**,
the invariant fields $\varphi$ and readonly views $\psi$ of a clause with one
record operand, a record's or a dictionary's, whose named members hold beside
its index views (`namedMembers`):

$$
\mathsf{named}(\mathsf{Ref}(\varphi;\psi;\ldots))=(\varphi;\psi)
\qquad
\mathsf{named}(\mathsf{Dict}(\varphi;\psi;\overline{D};\ldots))=(\varphi;\psi)
$$

$$
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c\quad\mathsf{named}(c)=(\varphi;\psi)\quad(f{:}A)\in\varphi}
     {\Gamma\vdash_G a.f:A}
\qquad
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi)
      \quad(f{:}A)\in\varphi\quad\Gamma\vdash_G a':A}
     {\Gamma\vdash_G a.f\leftarrow a':\mathsf{Null}}
$$

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

$$
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Dict}(\theta{:}A)\quad
      \Gamma\vdash_G k:K\quad K\equiv_G\mathsf{key}(\theta_k)\quad\theta_k\sqsubseteq\theta\quad
      U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a[k]:A\cup U}
$$

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

$$
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c\quad\mathsf{named}(c)=(\varphi;\psi)\quad(\kappa{:}A)\in\psi}
     {\Gamma\vdash_G a.\kappa:A}
\qquad
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi;\psi;\omega)\quad(\kappa{:}^{r}A)\in\omega
      \quad U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a.\kappa:A\cup U}
$$

$$
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Dict}(\varphi;\psi;\overline{D};\omega)\quad (\theta{:}A)\in\overline{D}
      \quad\theta\ni_!\kappa\quad U\equiv_G\mathsf{Undefined}}
     {\Gamma\vdash_G a.\kappa:A\cup U}
$$

A key one of the record's own-key bounds $b$ does not admit is not the
object's own, so its read continues at the prototype, which the record holds
under the reserved key at $P$ (`readProto`). For an array, $b$ excludes
`ArrayProto`'s keys, so every prototype member is read this way, whatever
further keys the array owns:

$$
\frac{\Gamma\vdash_G a:R\quad R\equiv_G\mathsf{Ref}(\varphi;\psi;\omega;\beta)\quad b\in\beta\quad b\nvDash\kappa\quad
      (\mathsf{proto}{:}P)\in\varphi\,\psi\quad P\equiv_G\mathsf{Ref}(\varphi';\psi';\ldots)\quad
      (\kappa{:}A)\in\varphi'\,\psi'}
     {\Gamma\vdash_G a.\kappa:A}
$$

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
writable index beside the optional `TZ`. A write to an optional field,
writable or readonly, is not typed, since the object's keys are fixed at
allocation; a readonly one grants no write in any case.

A fresh literal meets a dictionary, or a record whose optional fields it
leaves out, with no rule of its own: `alloc` types it at the record whose own
keys are bounded by exactly its names, and that record is below the target by
coverage through the bound ([`CoversKeys`, `CoversOptional`](POSITIVE-TYPES.md#records)).
No other key exists and the prototype key is not among them, so the object has
no prototype, lacks every key it does not write, and each field's contract
need only be within each index view, or equivalent to each writable index.
The literal may be empty, `{}`, and may write members the dictionary names:

$$
\frac{\vec k\ \text{distinct}\quad\Gamma\vdash_G e_i:A_i\quad
      G\vdash\mathsf{Ref}(\overline{k_i{:}A_i};\{\vec k\})\le D}
     {\Gamma\vdash_G\{\overline{k_i{:}e_i}\}:D}
$$

which is `alloc` followed by subsumption; the producer states the bounded
record as the literal's claim wherever its contract has an index or an
optional field. None of these rules grants a write capability to a readonly
dictionary.

$$
\frac{\Gamma\vdash_G t:A\quad\operatorname{check}(G,A,B,p)=\mathsf{true}}
     {\Gamma\vdash_G t:B}
$$

One object can carry both a field map and invocation code; the graph clause
$\mathsf{Callable}(\varphi;L)$ combines them. Four rules give it the same four
operations, and they are implemented and proved, not proposed: `makeCallable`
allocates it, typing each field's initializer and each signature's body exactly
as the two rules above do; `callCallable`, `readCallable` and `writeCallable`
then invoke, read and write it under the same premises as `app`, `read` and
`write`. Allocation and invocation remain distinct steps: creation allocates
the object and checks the bodies, without running them.

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
none. A store a tuple contract describes has no hole: an optional position is
absent only past the length (`listT`, *dense*), so iteration and spreads never
answer an `undefined` the positions do not hold. An index in bounds and an
arbitrary one differ, as do a mutable and a readonly array. A readonly store carries
element read capabilities: each location invariant implies the element type.
Writable stores require equality and are invariant; `setElem` requires a
writable store. The outer store field is also a view for a readonly array. `arrLit` allocates a store under the claimed tuple; `elem` reads a
required position named by a literal index, `elemOpt` an optional or rest
position, adding `undefined`, and `elemAny` any numeric index into a
homogeneous array, adding `undefined`; `setElem` writes a named position into
its location, or a fresh one the new store records, keeping the contract for
every alias; `len` reads the length. A write is typed only at an index no
greater than the required length, so it lands in bounds or appends and never
leaves a hole:

$$
\frac{\Gamma\vdash_G a:L\quad L\equiv_G\mathsf{list}(\tau)\quad
      \Gamma\vdash_G i:\mathsf{numLit}(k)\quad \tau(k)=A\quad
      k\le|\vec R_\tau|\quad \tau\ \text{writable}\quad \Gamma\vdash_G v:A}
     {\Gamma\vdash_G a[i]=v:L}\ \textsc{setElem}
$$

Writes at a greater index, or at one no contract names, and reads by a
non-literal index into a tuple, have no rule; a program appends with `push`.

A string owns its `length` and its code units ([semantics](SEMANTICS.md#operational-language),
"Strings"). `lenStr` reads the length of an operand whose every clause is a
string, and `elemStr` a code unit at any numeric index, a string or, past the
end or at a key that is not an index, `undefined`, whatever the literal:

$$
\frac{\Gamma\vdash_G a:S\quad\operatorname{Answers}_G(S,\mathsf{isStr},\mathsf{true})\quad N\equiv_G\mathsf{num}}
     {\Gamma\vdash_G\mathsf{lenOf}\;a:N}\ \textsc{lenStr}
\qquad
\frac{\Gamma\vdash_G a:S\quad\operatorname{Answers}_G(S,\mathsf{isStr},\mathsf{true})\quad
      \Gamma\vdash_G i:I\quad\operatorname{Answers}_G(I,\mathsf{isNum},\mathsf{true})}
     {\Gamma\vdash_G\mathsf{elemAt}\;a\;i:\mathsf{str}\cup\mathsf{undefined}}\ \textsc{elemStr}
$$

Any other member of a primitive is read through its wrapper's prototype. The
source read `x.k`, with `x` saved in a slot, lowers to a test of each
primitive shape its type holds, selecting that shape's read, and the object
read last (`dispatchTerm`):

$$
\mathsf{if}\ \mathsf{isStr}(x)\ \mathsf{then}\ r_{\mathsf{str}}\ \mathsf{else}\
\mathsf{if}\ \mathsf{isNum}(x)\ \mathsf{then}\ r_{\mathsf{num}}\ \mathsf{else}\ \cdots\ \mathsf{readAt}\;k\;x,
\qquad
r_s=\mathsf{readAt}\;k\;(\mathsf{makeAt}\;\mathsf{absent}\;[\mathsf{proto}]\;[P_s])
$$

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
classifies the operation, $\operatorname{op}(op,c,d)$ (`opResult`), where
$\mathsf{N}$ is `num` or `numLit`, $\mathsf{Z}$ is `bigint` or `bigintLit`,
$\mathsf{S}$ is `str` or `strLit`, and $\mathsf{P}$, the printable clauses
(`printableClause`), is $\mathsf N\cup\mathsf Z\cup\mathsf S$ with `bool`,
`boolLit`, `nul` and `undef`: every primitive but a symbol. $\mathsf{Pr}$
(`primitiveClause`) is $\mathsf P$ with `symbol`, and $\mathsf{O}$
(`identityClause`) the record clauses, `refs` or `dict`, with an invariant
field: their members are objects with a field location, whose identity
strict equality compares:

$$
\operatorname{op}(op,c,d)=\begin{cases}
\mathsf{bool} & op={\equiv},\ c\in\mathsf{Pr}\cup\mathsf O\ \text{or}\ d\in\mathsf{Pr}\cup\mathsf O\\
\mathsf{bool} & op\ \text{relational},\ c,d\in\mathsf N\cup\mathsf Z\ \text{or}\ c,d\in\mathsf S\\
\mathsf{str} & op={+},\ c\in\mathsf S,\ d\in\mathsf P\ \text{or}\ c\in\mathsf P,\ d\in\mathsf S\\
\mathsf{num} & op\ \text{arithmetic},\ c,d\in\mathsf N\\
\mathsf{bigint} & op\ \text{arithmetic},\ c,d\in\mathsf Z\\
\text{none} & \text{otherwise}
\end{cases}
$$

A bigint divisor, of `/` or `%`, that may be zero, or an exponent that may be negative, is
admitted: the operation then throws a `RangeError`, an outcome safety admits
([Design](DESIGN.md#throws)). $\operatorname{Operands}_G(op,A,B,r)$
requires both types of clause rows and every clause pair of $A$ and $B$ to
classify as $r$, and the result type must hold every value of the kind
($\operatorname{covers}$): the number, bigint or string family exactly, or both
Boolean literals:

$$
\frac{\Gamma\vdash_G a:A\quad\Gamma\vdash_G b:B\quad
      \operatorname{Operands}_G(op,A,B,r)\quad\operatorname{covers}_G(N,r)}
     {\Gamma\vdash_G a\mathbin{op}b:N}\ \textsc{arith}
$$

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
numeric family, and is refused on any other.

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

For branching, $\operatorname{Answers}_G(A,k,q)$ checks that every expanded
clause of $A$ gives the same known Boolean answer $q$ to test $k$, and that
$A$ is of clause rows, since a parameter row's members could be anything:

$$
\operatorname{Answers}_G(A,k,q)\iff
\forall i\in A.\;\mathsf{plain}_G(i)\ \land\
\forall\gamma\in\operatorname{expand}_G(A).\;\operatorname{tag}(k,\gamma)=q.
$$

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

$$
\operatorname{keys}(\kappa,\gamma)=
\begin{cases}
\mathsf{true} & \kappa\in\operatorname{present}(\gamma)\\
\mathsf{false} & \kappa\notin\operatorname{present}(\gamma),\ \exists K\in\operatorname{bounds}(\gamma).\ \neg K\ \text{admits}\ \kappa\\
\text{none} & \text{otherwise}
\end{cases}
\qquad
\operatorname{tag}(\mathsf{isArray},\gamma)=
\begin{cases}
\operatorname{keys}(\sigma,\gamma) & \gamma\ \text{a record or dictionary clause}\\
\mathsf{false} & \text{otherwise},\ \gamma\neq\mathsf{top}
\end{cases}
$$

$$
\operatorname{tag}(\mathsf{hasKey}(\kappa),\gamma)=
\begin{cases}
\operatorname{keys}(\kappa,\gamma) & \gamma\ \text{a record or dictionary clause}\\
\text{none} & \gamma\ \text{an arrow, callable or construct-signature clause}\\
\mathsf{false} & \text{otherwise},\ \gamma\neq\mathsf{top}
\end{cases}
$$

`keyAnswer_sound` gives each answer from the clause's meaning: a present key
is owned (`semWithArgs_owns`), and a bound's excluded key is not
(`ownKeysT_lookup`).

Other shape
tests have an answer determined by the clause's shape; numeric singleton
equality also examines its bits. A broad number clause has no fixed answer
to that equality, so it establishes neither outcome:

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
\mathsf{invoke}(\mathsf{obj}(\ell,\mathsf{closure}(1,\operatorname{close}^{2}_{\rho}(b))),r,[a])
\longrightarrow \operatorname{close}_{r::a::\rho}(b).
$$

The formal statement is `instantiate_beta`; environment entries must be closed.
This is the invocation step for an already allocated function object;
creation is a separate step. The same substitution law applies to `letE`.
Arrow membership requires an object with closed callable code, so every value in a
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

### Throwing

`throw a` has every type: it never produces a value, and a throw is an
outcome safety admits ([Design](DESIGN.md#throws)). Its operand is typed at a
type of its own, since it runs first:

$$
\frac{\Gamma\vdash_G a:A}{\Gamma\vdash_G\mathsf{throw}\ a:B}\ \textsc{throw}
$$

The soundness case composes `a`'s safety with the throw's context rule
(`bind` over `Tm.throw`) and closes with `thrown_safe`: the value `a` produces
is closed, as every member of a type is (`meaning_value`). Evidence names the
rule `throw` with the operand's derivation as its one premise; the producer
types a slot operand at the slot's type.

### Allocation from parts

$\mathsf{merge}_\delta(a,b)$ allocates the fields $a$'s object owns and, over
them, the own enumerable data properties $b$ has, less $\delta$
([SEMANTICS](SEMANTICS.md#operational-language)). Its type is a record every
pair of the operands' clauses gives ([Design](DESIGN.md#object-literals)):

$$
\frac{\Gamma\vdash_G a:A\quad\Gamma\vdash_G b:B\quad
      \operatorname{MergeOk}_G(\delta,A,B,R)}
     {\Gamma\vdash_G\mathsf{merge}_\delta(a,b):R}\ \textsc{merge}
$$

$\operatorname{MergeOk}_G(\delta,A,B,R)$ holds where $A$ and $B$ are of clause
rows and, for each clause $c_a$ of $A$ and $c_b$ of $B$, some clause
$\mathsf{Ref}(\varphi;\omega;\beta)$ of $R$ is given by them
(`ObjectMerge.MergeClause`): $c_a$ a record or dictionary, $c_b$ one too or a
clause of values owning no enumerable property (`null`, `undefined`,
Booleans, numbers, bigints, symbols); each field $(k{:}T)\in\varphi$ surely
given within $T$ by $c_b$, or by $c_a$ where whatever $c_b$ gives under $k$ is
within $T$; each optional field within its type on both sides, and then $c_a$
holding no prototype; each bound of $\beta$ admitting every key either side
may give. "Within" is label inclusion, whose meaning is a union's. The
soundness case evaluates the operands with `bind`, as `arith` does, and
closes with `ObjectMerge.merge_values_safe`, which takes the merge's step,
then the allocation's by `make_fields_rule`, giving each location the
contract its result key states, or its copied value for a key the result
does not state. Evidence names the rule `merge` with the two operands'
derivations; the search types a slot operand at the slot's type and tries
the requested type, then the pool's, for the result, coercing; extraction
proposes the clauses (`ObjectMerge.mergeResult`) and states them as hints.

### Checked control-flow graphs

`ControlFlow.lean` adds a finite control-flow graph over the existing expression
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
for statement control flow and the term form inside closure bodies and direct
proofs. It emits every continuation except plain `branch`, which remains
available to graphs written against the protocol directly.

A target contains its label and an optional slot map. These are executable
program data, shared by the machine and checker; evidence cannot supply a
different binding transfer. Numeric targets abbreviate an identity map. A bind
or `branchBind` map indexes the environment **after** pushing the result; effect
and ordinary branch maps index the unchanged incoming environment.

A node's **handler** is a target too: where a throw out of its expression
goes, the thrown value pushed as a `bind` pushes a value. A node without one
lets the throw end the run, in the state $\mathsf{raised}(v)$. The machine:

$$
\frac{h,t\ \text{raises}\ v}{h,\ \mathsf{eval}(t,\rho,k,\ell)\to h,\ \mathsf{at}(\ell,\mathsf{push}(v,\rho))}\ (\texttt{handle})
\qquad
\frac{h,t\ \text{raises}\ v}{h,\ \mathsf{eval}(t,\rho,k,\varnothing)\to h,\ \mathsf{raised}(v)}\ (\texttt{raise})
$$

Node evidence for a node with a handler supplies the type $T$ the thrown value
is bound at and the handler edge's certificate. `checkHandler` requires $T$ to
admit every value, one of its clauses being top (`admitsAll`), and the edge to
check against the target's claims under the facts that hold wherever the
expression throws, which are those of the node's entry that do not mention the
heap (`handlerFacts`: immutable values, alias and distinct links, shifted past
the thrown value's slot):

$$
\frac{\mathsf{top}\in\operatorname{expand}_G(T)\quad
      \operatorname{TargetOk}_G(C,\ T{:}\Gamma,\ \ell,\ \operatorname{handlerFacts}(K))}
     {\operatorname{HandlerOk}_G(C,\Gamma,K,\ell)}\ \textsc{handler}
$$

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

`Transition.det` proves determinism of this combined machine, a throw
included (`Raises_det`).
`accepted_no_stuck` proves that after any finite actual execution, the machine
has returned a typed value, ended by a throw of a closed value, or can take
another step. `accepted_result` proves
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
bodies. Boolean result refinement is proved as described below. A primitive fragment with parameters
is connected; broader source extraction remains integration work. The next section supplies
an in-memory certificate producer; [REQUEST-PROTOCOL.md](REQUEST-PROTOCOL.md)
describes its serialized consumer boundary. No graph-level completeness theorem is claimed here; the
program-evidence and edge-evidence completeness results above retain their
stated scope.

#### Refinement under an observed outcome

[BranchRefinement.lean](lean/Verification/Model/Programs/BranchRefinement.lean)
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
require ordinary subtyping, or, for a slot $k$ holding an object the tested
value was read from through field $f$ (a current read link at the dispatch,
`readFields`), subtyping from its field slice $F^{f}_{t,q}(\Gamma(k))$
(`fieldSlice`): the labels of $\Gamma(k)$ but those every clause of which is a
record fixing $f$, as an invariant field or a readonly view, at a type that
answers the tag $t$ with $\lnot q$. The common environment theorem is:

$$
\frac{
 \operatorname{EnvOk}_G(\Gamma,\rho,n{+}1,W)
 \quad \operatorname{HeapOk}(n{+}1,W,h)
 \quad o(\rho(i))
 \quad \forall (k,f)\in\mathit{fs}.\ h(\rho(k).f)=\rho(i)
 \quad \operatorname{ObservedCovers}_G(\Gamma,\Delta,i,o,m,\mathit{fs})
}{
 \operatorname{EnvOk}_G(\Delta,\operatorname{mapEnv}(m,\rho),n{+}1,W)
}.
$$

The field slice is sound one level up (`fieldSlice_sound`): the field's
location holds the read value, and a heap meeting the world holds at that
location a value of the field's type one level down (`field_value`), whose tag
answer is budget-independent. What it establishes is the object's label,
which its allocation fixes; it is not a claim about what the field holds
later, so writes and calls after the test do not undo it. A discriminated
union is this: `s.kind === "circle"` keeps the arms whose `kind` admits
`"circle"`.

An observation the tested slot's type rules out (`impossible`: a tag answer
every label of it contradicts, or a Boolean it does not hold) covers any
destination: no environment meets both, so the edge is never taken.
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
  Alternatively, a passed test naming one primitive family is covered by that
  family's clause in the destination, whatever the tested type, `unknown`
  included (`tagMember`, with the marker `subset`): every value `typeof`
  answers `"string"` for is a string. A more precise algorithm can implement
  the same contract without changing the edge or environment rule.

$$
\frac{\mathsf{tagHolds}(t,v)=\mathsf{true}\ \Rightarrow\ v\in\llbracket c\rrbracket\quad c\in\operatorname{expand}_G(B)}
     {A\preceq_{t=\mathsf{true}}B}\ \textsc{tag-member}
\qquad t\in\{\mathsf{isStr},\mathsf{isNum},\mathsf{isBigint},\mathsf{isSymbol},\mathsf{isUndef},\mathsf{isNul},\mathsf{isBool}\}
$$

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

#### Statement forms as graphs

The statement forms of [DESIGN.md](DESIGN.md#statement-forms) add no node
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
  block is compiled once per way out ([DESIGN.md](DESIGN.md#throws)): after a
  normal completion, before each `return` in the body or handler with the
  value held in a slot of its own, and after a throw with the thrown value
  held, ending in a node that throws it again. Where neither the body nor the
  handler can complete, the normal way leads to an unreachable node that
  loops on itself and states nothing.

## State

What is known about the heap and the environment as execution proceeds, layered
over both of the above: expression typing decides whether an operation is
admitted, the graph decides where its knowledge travels, and these rules decide
what it establishes.

### Current-content rules (semantic layer)

The finite [type and assertion syntax](POSITIVE-TYPES.md#state-assertion-grammar)
is defined alongside the ordinary type grammar. This section owns its rules.

These rules are proved in [HeapObservations.lean](lean/Verification/Model/Semantics/HeapObservations.lean)
and [HeapFacts.lean](lean/Verification/Model/Semantics/HeapFacts.lean).
[HeapExpressionRules.lean](lean/Verification/Model/Programs/HeapExpressionRules.lean)
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
drops all old facts and establishes the written value's predicate. `alloc` preserves shifted
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
union. It extends the $\Gamma(x)$ of the ordinary rules to the pair, is partial
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
\qquad
\frac{\Gamma\vdash_G\operatorname{alloc}(x):\operatorname{Ref}A
      \qquad(\Gamma;\Pi)(x)\ \text{undefined}\qquad x\in\operatorname{dom}\Gamma}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\operatorname{alloc}(x):\operatorname{Ref}A
  \dashv \Pi\;;\;\Sigma}
$$

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
than a judgment. Writing $\operatorname{pred}(A)$ for the primitive predicates a type
denotes — defined only when $A$ is primitive, so the premise also fails for a
reference or an arrow result:

$$
\frac{\Gamma\vdash_G\operatorname{read}(x):A\qquad\Gamma(x)=\operatorname{Ref}B}
{\Gamma;\Pi;\Sigma\vdash_G r\leftarrow\operatorname{read}(x):A
  \dashv \Pi\;;\;\Sigma,\{y\mapsto r\mid y\approx_\Pi x\}}
$$

$$
\frac{(x\mapsto R)\in\Sigma\qquad R\subseteq\operatorname{pred}(A)}
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

| Evidence                             | Guaranteed output in the result-pushed frame                                                                                                                                                                                             |
| ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Pure value or variable copy          | Preserve facts and links; copies establish slot equality and duplicate existing facts. Literals establish their exact result even when their supplied type is wider. Lambda bodies require ordinary typing, without captured heap facts. |
| Pure test or conditional             | Preserve existing facts and links, shifted past the result slot. Every evaluated subexpression must be syntactically pure; no new result-to-cell link is invented.                                                                       |
| Ordinary typed read                  | Preserve facts and record read links to the receiver and witnessed aliases, retaining its plain or callable descriptor; no prior current-content fact is needed. Its result has the supplied type.                                       |
| Observed read                        | Preserve facts and links; record the result's primitive predicate and its current read relationship. That set must fit the requested ordinary result type.                                                                               |
| Known immutable value                | Check the requested primitive type against a proved slot fact or the slot's ordinary primitive type.                                                                                                                                     |
| Allocation                           | Check ordinary creation evidence and scope for either descriptor, preserve old facts, add the fresh bag's initial contents where a checked value slot's are known, and its fields' distinctness from every record slot's. Closure code is not executed. |
| Write                                | Check ordinary write evidence (no old-content premise), discard all old cell facts, record new contents for the receiver and its witnessed aliases, and preserve immutable facts and slot equalities. Read links are discarded.          |
| Ordinary expression, including calls | Check ordinary evidence, discard cell facts and read links, preserving immutable facts and slot equalities.                                                                                                                              |

`typedRead_sound`, `read_sound`, `alloc_sound` and `write_sound` prove the four
rules above. None of them takes a premise about a cell's old contents, and the
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
[CallableEffectTests.lean](lean/Verification/Model/Tests/CallableEffectTests.lean)
checks that code with a delayed write preserves old contents during creation,
that descriptor changes and out-of-scope captures cannot reuse its evidence,
and that a saved read value remains precise across a subsequent call.
[CallableMutationTests.lean](lean/Verification/Model/Tests/CallableMutationTests.lean)
adds an actual mutating invocation: a closure captures a neutral bag and writes
`true` after a `false` read has been saved. The saved value still verifies as
`false`; a fresh read verifies as Boolean and executes to `true`, while a
requested `false` contract fails. Both plain and callable allocations follow
this path. Forged call outputs retaining old cell facts or read links are
rejected by the consumer. Exact execution proofs distinguish the changed heap
from the unchanged saved value.
[CallableReentryTests.lean](lean/Verification/Model/Tests/CallableReentryTests.lean)
checks an active function calling a callback that mutates its bag and reenters
that same function. A terminating inner callback ends the nesting. The outer
frame can return its saved `false` or reread the changed `true`; exact execution
proofs cover both choices and both bag descriptors. The graph producer and JSON
consumer accept the Boolean contracts and reject incompatible callbacks and
unjustified singleton contracts. Nested invocation uses the existing closure,
let-binding, and heap rules without a separate reentry mechanism.
[CallableOrderTests.lean](lean/Verification/Model/Tests/CallableOrderTests.lean)
checks effectful creation followed by invocation. The initializer writes a
captured bag and allocates an intermediate object before the callable is
allocated; the argument then overwrites the bag before the body reads it.
The exact execution and heap order are proved for both captured-object
shapes. A stuck initializer blocks argument effects, and a stuck argument
blocks the body. Effectful creation cannot reuse value-slot allocation,
ordinary function-creation, or purity evidence to retain stale heap facts.
The existing JSON pipeline checks the complete expressions.

`pureTerm` includes values, variables, tests of pure terms, and conditionals
whose condition and both arms are pure. It excludes calls, reads, writes and
allocation, including function creation. A checked creation effect separately
preserves old facts while allocating the function's bag; the body may have
effects because creation does not run it. `pure_step` and `pure_frame` prove:

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

Primitive result predicates are finite lists of null/undefined/Boolean
singletons, numeric singletons and the number family. `HeapKnowledge.check_sound` and `project_checked`
justify transfer and alias-preserving projection along executable slot maps.

[HeapExpressionTests.lean](lean/Verification/Model/Tests/HeapExpressionTests.lean)
uses the actual source type graph to check allocation, write, mapped transfer,
wide read and precise return, with negative tests for stale contents, invalid
storage writes, fabricated facts and changed expressions. The maintained graph checker carries the same postconditions in its state
invariant and checks every incoming edge, including back edges. External entry
requires empty knowledge; effect-only continuations drop result-slot facts.
[HeapGraphTests.lean](lean/Verification/Model/Tests/HeapGraphTests.lean) proves
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

[WriteRefinedRead.lean](lean/Verification/Model/Programs/WriteRefinedRead.lean)
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
_content predicate_ remains an impossible observation, not an absent one.

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

`CertificateProducer.lean` accepts an actual graph, its declared result type and
start label, and one `PointClaim` per node. Each claim fixes both the entry
context and the expression result type. These are annotations in this Lean
interface, not SKJS claim types. The source adapter supplies them for the supported
fragment; new source forms require the corresponding extraction obligations.

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

A derived class's constructor (`class D extends B`, its body
`s̄₁; super(ā); s̄₂`, `s̄₁` reading no `this`) is its base's construction,
bound to a name no source spells, then the class constructor's lowering
([DESIGN](DESIGN.md#modules-and-code-units), "Class members") whose
allocation is the allocation from parts copying it:

$$
\mathsf{class}(\vec x).\ \vec s_1\,;\ \mathsf{const}\ \textit{base} = \mathsf{new}\ B^{\circ}(\vec a)\,;\
  \mathcal{C}(\vec s_2,\ \varphi_0,\ \varnothing)
  \quad\text{with}\quad
  \mathcal{C}(\varepsilon,\varphi,A) = \{\texttt{[[proto]]}{:}\,D.\texttt{[[prototype]]},\ \ldots\textit{base},\ \varphi,\ \overline{f{:}\,\mathsf{undefined}}\}
$$

where $B^{\circ}$ is `B`'s constructor claimed also at the fresh instance it
allocates, its keys exact (`ctorE` checks its body at that signature too).
`D` without a constructor has JavaScript's implicit one,
`constructor(...args) { super(...args); }`: its parameters are $B$'s, at
their types, under names no source spells, and $\vec a$ is them. A class's
prototype object is allocated once, at its definition:

$$
D.\texttt{[[prototype]]} = \{\texttt{[[proto]]}{:}\,B.\texttt{[[prototype]]},\ \kappa_D{:}\,\mathsf{undefined},\ m{:}\,D.m,\ \ldots\}
$$

its own methods, linked to its base's under the prototype key, as
JavaScript's `D.prototype` is; $\kappa_D$, the class's key, is there where
`instanceof D` is written in the file, below. A prototype holding nothing
of its own that nothing tests is not allocated: `D`'s instances then hold
the nearest ancestor's (or none), and every read and test answers the same.
`super.m(ā)` is `B.m.call(this, ā)`, with `B.m` the closure `B`'s prototype
chain holds. So the allocation's keys are exact, and `D`'s declared type,
its own members and `B`'s, covers it through the prototype chain
([method coverage](POSITIVE-TYPES.md#clause-coverage), `CoversByProto`).

`e instanceof C`, with `C` an identifier TypeScript binds to a class the
file declares at its top level, evaluates $e$, then `C` (read as its
prototype object, which the class statement binds with it), then looks for
$\kappa_C = \texttt{[[}C\texttt{.prototype]]}$, the key only
$C.\texttt{[[prototype]]}$ owns, along $e$'s prototype chain:

$$
e\ \mathtt{instanceof}\ C\;\equiv\;\mathsf{let}\ x=e\ \mathsf{in}\ \mathsf{let}\ p=C.\texttt{[[prototype]]}\ \mathsf{in}\ \mathsf{hasKey}(\kappa_C)(x)
\qquad
\frac{\Gamma\vdash e:A\quad \Gamma\vdash C.\texttt{[[prototype]]}:P}
     {\Gamma\vdash e\ \mathtt{instanceof}\ C:\mathsf{boolean}}
$$

Any operand is admitted: $\mathsf{hasKey}$ answers `false` on a primitive,
as `instanceof` does (it throws only on its right operand). A tested
immutable variable is refined as by every tag test ([Guards](DESIGN.md#guards)).

An optional chain is the same derived form with the arms exchanged. The
parser writes `r?.x` and every link after it in the chain (`.b`, `[k]`,
`(a)`, `!`) as one `optional` node whose body applies those links to the
variable $\mathsf{chain}$ (`chainName`, spelled `?.`, which no source
identifier is), so a nullish receiver skips the rest of the chain, as
JavaScript's short-circuit does; a second `?.` in a chain tests the chain so
far, which is `undefined` where an earlier one skipped:

$$
r\,?.\,b\;\equiv\;\mathsf{let}\ \mathsf{chain}=r\ \mathsf{in}\ \mathsf{if}\ \mathsf{nullish}(\mathsf{chain})\ \mathsf{then}\ \mathsf{undefined}\ \mathsf{else}\ b,
\qquad
\frac{\Gamma\vdash r:A\quad T_{\mathsf{false}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash r\,?.\,b:\{\mathsf{undefined}\mid T_{\mathsf{true}}(A)\neq\emptyset\}\cup B}
$$

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

$$
\mathsf{typeof}\ e\;\equiv\;\mathsf{let}\ x=e\ \mathsf{in}\
\mathsf{if}\ \mathsf{isUndef}(x)\ \mathsf{then}\ \texttt{"undefined"}\ \mathsf{else}\
\mathsf{if}\ \mathsf{typeofObject}(x)\ \mathsf{then}\ \texttt{"object"}\ \mathsf{else}\ \cdots\
\mathsf{if}\ \mathsf{isSymbol}(x)\ \mathsf{then}\ \texttt{"symbol"}\ \mathsf{else}\ \texttt{"function"}
$$

in the order undefined, object, boolean, number, string, bigint, symbol. It
splits $x$ by `unionVar` as `??` does (`selectPlan`), so a label whose shape
is settled reaches one answer; its claim is `string`. A comparison of `typeof e`
with a shape's literal stays the one tag test ([shape predicates](DESIGN.md#shape-predicates)).

`key in o` evaluates the key, then the object, then asks whether the object
has the key. A string literal key is the tag test $\mathsf{hasKey}(\kappa)$ of
the object, which refines a tested immutable variable as every tag test does.
A key whose claim is a union of string singletons $\kappa_1\mid\cdots\mid\kappa_n$
dispatches on them, the last needing no test since the key is one of them
(`inKeysTerm`):

$$
k\ \mathtt{in}\ o\;\equiv\;\mathsf{let}\ y=k\ \mathsf{in}\ \mathsf{let}\ x=o\ \mathsf{in}\mathsf{if}\ \mathsf{strEq}(\kappa_1)(y)\ \mathsf{then}\ \mathsf{hasKey}(\kappa_1)(x)\ \mathsf{else}\ \cdots\mathsf{hasKey}(\kappa_n)(x)
$$

$$
\frac{\Gamma\vdash o:A\quad \forall\gamma\in\operatorname{expand}_G(A).\ \gamma\ \text{a record, dictionary, arrow or callable clause}
      \quad \kappa_i\notin\mathcal R}
     {\Gamma\vdash k\ \mathtt{in}\ o:\mathsf{boolean}}
$$

where $\mathcal R$ is the keys the model does not answer as JavaScript does
(`inKeyRefusal`, [DESIGN](DESIGN.md#guards)). The operand's clauses are
objects because `in` throws on a primitive, where the test would answer
`false`, and not a class value, whose static members are bound apart.

Logical AND and OR return an operand, as in JavaScript: the left one where its
truthiness decides, the right one elsewhere. For a left operand that is not a
Boolean they are the same derived form on the truthiness test:

$$
a\mathbin{\&\&}b\;\equiv\;\mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{if}\ \mathsf{truthy}(x)\ \mathsf{then}\ b\ \mathsf{else}\ x,
\qquad
a\mathbin{\Vert}b\;\equiv\;\mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{if}\ \mathsf{truthy}(x)\ \mathsf{then}\ x\ \mathsf{else}\ b,
$$

split by `unionVar` on $x$ (`selectPlan`, which `??` and default parameters
share): a label whose truthiness is settled selects its arm by `ifTag`, and
one that is not (a number, a string) takes both arms by `ifBool` on the test.
Writing $T_q(A)$ for the labels of $A$ that may answer $q$ (`tagSlice`):

$$
\frac{\Gamma\vdash a:A\quad T_{\mathsf{true}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash a\mathbin{\&\&}b:T_{\mathsf{false}}(A)\cup B}
\qquad
\frac{\Gamma\vdash a:A\quad T_{\mathsf{false}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash a\mathbin{\Vert}b:T_{\mathsf{true}}(A)\cup B}
$$

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

A block closure that does not return on every terminal arm completes, which in
JavaScript returns `undefined`; its body ends with $\mathsf{return}\
\mathsf{undefined}$ at the closing brace, so that the shapes above apply
unchanged, and the result claim must admit $\mathsf{Undef}$ (`void` is top). A
bare `return` is the same literal at its keyword.

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

A keyed access `a[k]` whose key is claimed at one string $s$ is the named
access of $\mathsf{str}(s)$, evaluated after `a` and `k`, and the read rules
above apply. A key claimed at one number $n$ names the property
$\mathsf{ToString}(n)$ (`numberToString`), as JavaScript's `ToPropertyKey`
converts it, where `a` is claimed only at records owning no array store
(`recordReceiver`); an array's number key is its store's element (`elemAt`):

$$
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c_1\cup\cdots\cup c_m\ \text{records without a store}\quad
      \Gamma\vdash_G k:\mathsf{Num}(n)}
     {a[k]\ \leadsto\ \mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{let}\ \_=k\ \mathsf{in}\ x.\mathsf{str}(\mathsf{ToString}(n))}
$$

([DESIGN, "Numeric property names"](DESIGN.md#numeric-property-names)).

### Patterns

A pattern binds names from one value, in pattern order, and has no rule of its
own: it is reads, a tag dispatch and lets. Write
$\Gamma\vdash p\Leftarrow(t{:}R)\dashv\Delta$ when binding pattern $p$ to the
value term $t$ reads at $R$ under $\Gamma$ extends the scope by $\Delta$
(`bindTarget` in the graph lowering, `closureBind` in a closure body). A name
binds the read; a nested pattern holds it in an anonymous slot and binds its
own elements over it:

$$
\frac{\Gamma\vdash t:R}{\Gamma\vdash x\Leftarrow(t{:}R)\dashv x{:}R}
\qquad
\frac{\Gamma\vdash t:A\quad
      \Gamma,\_{:}A,\Delta_{<i}\vdash p_i\Leftarrow(\mathsf{read}_{f_i}(\_){:}R_i)\dashv\Delta_i\ \ (i\le n)}
     {\Gamma\vdash\{f_1{:}p_1,\ldots,f_n{:}p_n\}\Leftarrow(t{:}A)\dashv\Delta_1,\ldots,\Delta_n}
$$

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
([DESIGN.md](DESIGN.md#patterns)). A pattern over a value that is not an array
is refused.

A default replaces a read that is `undefined`, and only then runs. With
$R'$ the read's labels told apart clause by clause (`byClause`: a label that
is a union row, such as a declared alias, is replaced by one label per
clause, the same values) and $T_q$ the tag slice:

$$
\frac{\Gamma\vdash t:R'\quad \Gamma,\_{:}R'\vdash d:D\quad
      \Gamma,\_{:}R'\vdash p\Leftarrow(\mathsf{if}\ \mathsf{isUndef}(\_)\ \mathsf{then}\ d\ \mathsf{else}\ \_\ {:}\ T_{\mathsf{false}}(R')\cup D)\dashv\Delta}
     {\Gamma\vdash (p=d)\Leftarrow(t{:}R)\dashv\Delta}
$$

(`tagBind` in a graph, `selectPlan` in a closure). The default is checked
where the earlier bindings are in scope and the later ones are not; a default
that names a later binding of its own declaration is refused by the parser,
since JavaScript throws there (the temporal dead zone) where the lowering
would read an outer binding of that name.

An array rest $\ldots p$ at index $s$ over $A$ whose store is one tuple of
$n$ required positions, whose length is exact (`listT`), is the fresh array of
the positions from $s$ on, claimed at the rest's span $C$ like an array
literal:

$$
\frac{\operatorname{Store}(A)=[A_0,\ldots,A_{n-1}]\quad
      \Gamma\vdash\mathsf{alloc}\{[\,]{:}\mathsf{arr}(\mathsf{elem}(\_,s),\ldots,\mathsf{elem}(\_,n{-}1))\}:C\quad
      \Gamma\vdash p\Leftarrow(\cdot{:}C)\dashv\Delta}
     {\Gamma\vdash[\ldots,\ldots p]\Leftarrow(\_{:}A)\dashv\ldots,\Delta}
$$

The rest of an array whose contract does not fix its length is a slice whose
length only the run knows: no list of reads, and the calculus has no slice
term, so it is refused. An object rest is refused too: it copies every
remaining own enumerable key of its source, which a record contract does not
bound, and an object's keys are fixed where it is allocated, so a copy of the
named fields would be another object than JavaScript's.

A statement `const p = e` holds $e$ in an anonymous slot for its one entry,
binds $p$ over it, and drops the slot before the next entry, which states
$\Delta$. An array assignment `[x_1, …, ...r] = e` is the same with each read
written to its mutable local at the local's storage contract. A parameter
written as a pattern or with a default binds a hidden name $h$, which the
caller's argument initializes, and the body starts with the pattern over it,
in parameter order:

$$
\mathsf{function}\ f(\ldots,p_i=d_i,\ldots)\,\{S\}\;\equiv\;
\mathsf{function}\ f(\ldots,h_i,\ldots)\,\{\ldots;\ \mathsf{const}\ p_i=h_i\ (\mathsf{default}\ d_i);\ \ldots;\ S\}
$$

where $h_i$'s type admits $\mathsf{Undef}$ when there is a default, so a
caller may omit it. A closure parameter's default stays the closure's own
(`parameterOrder`), and its pattern is a `destructBody` first in the body.

### Mutable bindings and module constants

A `let` binding and an assigned parameter lower to a private cell
([DESIGN.md](DESIGN.md#next-fragment-extension-mutable-locals-aimed-at-a-known-loop-failure)). Its
contract $C$ is fixed where it is declared; the initializer and every write
are checked against it (`storage-contract`), and a point claim for the name
describes the cell's current contents, which the
[current-content rules](#current-content-rules-semantic-layer) justify on every
incoming edge. The contract is:

$$
\operatorname{contract}(\mathtt{let}\ x{:}T=e)=T
\qquad
\operatorname{contract}(\mathtt{let}\ x=e)=
\begin{cases}
Q_{\mathit{next}}(x) & \text{the claim for } x \text{ at the entry of the next statement}\\
Q(e) & \text{no statement follows in its block}
\end{cases}
$$

with $Q(e)$ the claimed type of the initializer. A declaration ending its block
has no statement after it to read the binding, and the initializer meets its
own claim, so any choice every write is checked against is sound. The producer
proposes TypeScript's declared type, the initializer's type widened
(`let x = 1` stores $\mathsf{Num}$); `null`, `undefined` and `[]`
initializers have no declared type in TypeScript (an evolving `any`) and are
refused. A parameter $x{:}D$ that the body assigns (`assignsStmt`) has
contract $D$, the caller's value its initial contents.

A `let` without an initializer binds `undefined` where its declaration runs,
which is the derived form

$$
\mathtt{let}\ x{:}T;\quad\equiv\quad\mathtt{let}\ x{:}T\cup\mathsf{Undefined}=\mathtt{undefined}.
$$

Definite assignment is not an extra rule: a read at $T$ types only where the
cell's current contents are known to be in $T$, a fact a write of a $T$ value
establishes and a join keeps only when every incoming edge proves it. A
closure reads a captured cell at its contract, $T\cup\mathsf{Undefined}$,
since it may run before the write. Current contents are primitive predicates,
so a `let x: T;` of an object type `T` is read at $T\cup\mathsf{Undefined}$
after its assignments. Without an annotation there is no contract and the
parser refuses it.

A module constant $c$ bound to $e_c$ by the initialization unit is read by
the module's functions at

$$
\operatorname{type}(\mathtt{const}\ c{:}T=e_c)=T
\qquad
\operatorname{type}(\mathtt{const}\ c=e_c)=Q_{\mathit{init}}(e_c),
$$

the initialization unit's claim for its initializer. That unit checks
$\Gamma\vdash e_c:Q_{\mathit{init}}(e_c)$ where it binds $c$, exactly as it
checks an annotation, and a constant never changes, so the functions'
assumption is what the unit establishes (the composition argument is
[DESIGN.md](DESIGN.md#modules-and-code-units)'s, unchanged).

### Source closures and their annotations

A source closure `(x₁: D₁, …, xₙ: Dₙ): Rₛ => t` is checked at the arrows its
claim names, by the creation rule of [Callables](#typing-rules): each claimed
arrow $(R,\vec A,B)$ types the body at its own receiver, its first $n$
parameters and its result. The source adds two requirements. Each claimed
parameter is within the annotation's, $A_j\sqsubseteq_G D_j$ for $j\le n$
(`within`), and, where the source states a result, the body meets it at the
annotated signature (the `closure-result` obligation):

$$
\frac{\forall(R,\vec A,B)\in L.\;\bigl(\forall j\le n.\;A_j\sqsubseteq_G D_j\bigr)
        \land\;\Gamma,\mathit{this}{:}R,\vec x{:}\vec A_{\le n}\vdash_G t:B
      \qquad
      R_s\neq\bot\;\Rightarrow\;\Gamma,\mathit{this}{:}Q_s,\vec x{:}\vec D\vdash_G t:R_s}
     {\Gamma\vdash_G \bigl(\vec x{:}\vec D\bigr)\colon R_s\Rightarrow t\;:\;\bigwedge L}
$$

with $R_s=\bot$ for a closure whose result the source leaves out (the
Fragment's `result` is `null`) and $Q_s$ the receiver the source states (`top`
for an arrow). The premise over $L$ is the creation rule's, so leaving the
result out drops a requirement and no check: the result is the claim's, like
any expression's. A named closure passed where a callback is offered more
parameters, `xs.reduce(acc, null)`, is claimed where it is created at that
signature beside its own; its body is checked at each (`offersArity`). So is
one passed where a variadic callback is offered, `process.on(sig, shutdown)`
at `(...args: unknown[]) => void`, when its parameters are among the
signature's fixed ones: $L$ then holds that signature's fixed row
(`offerRows`), and each claimed parameter is within the annotation's as for
any row. A `void` result is $\top$, so a closure returning a promise meets it.
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
body at both, and `ctorE` the constructor's at both, so the instance it
allocates, holding the method as a field of the longer signature, meets $I$'s
member by `CoversByFunction`:

$$
\frac{\Gamma\vdash_G \lambda\vec x.t:\bigl((C;\vec Q\to B)\land(C;\vec Q\,\vec U\to B)\bigr)
      \quad\Gamma,m{:}F\vdash_G \{m{=}m\}:C\quad\Gamma,m{:}F\vdash_G \{m{=}m\}:I}
     {\Gamma\vdash_G \mathsf{class}\{m(\vec x)\{t\}\}:\mathsf{new}()\Rightarrow C\land\mathsf{new}()\Rightarrow I}
$$

with $F$ the method's claimed type. Nothing here is a new rule: the premises
are the creation rule, `alloc` and subsumption under each construct signature.

The constructor is offered the same way. Where the class value is expected at
$\mathsf{new}(\vec P\,\vec V)\Rightarrow I$ while its constructor binds
$\vec x{:}\vec D$ with $|\vec x|=|\vec P|$, the class value is claimed at
$\mathsf{new}(\vec P\,\vec V)\Rightarrow I$ beside
$\mathsf{new}(\vec D)\Rightarrow C$ (a resource class constructed with the
request's parameters it ignores: `{ add: Add }` at
`ResourceClass<Collections, Json>`, `new (params: Json) => Resource<Collections>`).
`ctorE` types the body at the first $|\vec x|$ parameters, $\vec P$, and the
source requires each within the constructor's annotation, as for a closure:

$$
\frac{\forall(\vec A,B)\in L.\;|\vec x|\le|\vec A|\;\land\;
        \bigl(\forall j\le|\vec x|.\;A_j\sqsubseteq_G D_j\bigr)\;\land\;
        U,\vec x{:}\vec A_{<|\vec x|},\Gamma\vdash_G b:B
      \qquad U,\vec x{:}\vec D,\Gamma\vdash_G b:C}
     {\Gamma\vdash_G \mathsf{class}(\vec x{:}\vec D)\{b\}:\bigwedge L}
$$

with $C$ the class's instance type, its own signature
$\mathsf{new}(\vec D)\Rightarrow C$ among $L$. A constructor needing more than
the offered parameters meets no such signature, and the value holding it is
refused: a class whose constructor calls its parameter's `toString` is not a
`new (params: Json) => Resource<C>`, as a Json object may own that key at any
Json (`invalid-sum-sound-binding-constructor.ts`).

### Universal parameter initialization

The direct generic certificate distinguishes value slots, cell identities, and
raw defaulted argument slots. An argument slot carrying contract `B` denotes
`⟦B⟧η ∪ undefT`; `B` may contain rigid parameters. It has no ordinary variable
or cell-read rule. `defaultE i d` is the only rule that consumes it:

```text
Γ(i) = argument(B)       Δ; Γ ⊢ d : B
────────────────────────────────────────────────────────────
Δ; Γ ⊢ if isUndefined(var i) then d else var i : B
```

`GenericCertificate.Proof.check_safe` proves this for every admissible rigid
assignment `η`. The undefined branch uses the initializer's proof; the other
branch has meaning `⟦B⟧η`. This does not assume `undefined ∉ ⟦B⟧η`.
`ClosureCertificate.inputs` distinguishes ordinary and defaulted inputs, and
`invocation_of_inputs` connects their denotations to the closure's actual
argument binding. The universal proof is required even if every observed call
supplies the argument. A `let` prologue then exposes each initialized value.
`CertificateJudgments.check_iff_Typed` includes this rule.

The source adapter also performs acyclic closure conversion for literal
closures capturing later parameters. `Fragment.parameterOrder` delays only
closure allocations, until their dependencies are initialized; no executing
initializer may read or expose a pending closure. Potentially effectful defaults
keep their relative order. A closure is allocated once and captures initialized
immutable parameters and unchanged outer cell identities. This preserves
sharing and observations up to renaming fresh locations. Cycles and pending
closure exposure are refused. This source-correspondence argument remains in
the trusted adapter; it is not claimed as a Lean proof about JavaScript.
The same schedule drives graph lowering and universal certificate construction.
No heap location changes its fixed world type.

## Callables

The callable fragment described below is implemented. The rest of
this section states the broader design and the rules it would add, in the terms of the rules above, so the
design can be read as a user of the verifier would read it: what can be claimed
about a value, what a claim commits to, and what the verifier will and will not
check. Where a fact below is already proved, the theorem is named; where it is
not, the sentence says so. [INTERSECTIONS.md](INTERSECTIONS.md) §4 points here
for the design of callable objects.

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
plain objects (`objAt fields absent`) and functions (`objAt fields (closure
arity b)`), where `fields` is the finite map from field names to the locations
they stand for, fixed at allocation. `CallCode` is a separate descriptor type;
its body is not a runtime value. `makeAt code names inits` takes one fresh
location per named field; `funE b` is the one-field case, giving a source
function a null-initialized bag — a function has no properties of its own, and
that one location is what gives it an identity to compare. `letE` binds without
allocation. Plain allocation and one-field function creation are abbreviations
of `makeAt`, with one congruence rule, one allocation step, and the shared
semantic proofs `make_rule` and `make_fields_rule`. `isFun` recognizes function objects and
`isRef` recognizes plain objects, both independently of the heap.

The implemented semantic slice is in
[CallableObjects.lean](lean/Verification/Model/Programs/CallableObjects.lean).
`arrowT` and `arrowsT` admit function objects; `bagT P` describes an object's
writable cell independently of its call slot; `callableT L P` combines both
contracts on the same value. `CodeSpec` checks invocation bodies separately
from object membership. `EnvOk.prepend` extends environments with ordered
parameter lists, and `HasTy.invocationSpec` derives a native call
contract from body derivations under the parameters the code takes and the
captured bindings. The signatures of this ordinary-closure creation rule offer
at least the descriptor's arity; optional calls and variadic creation use the
rules in [Expressions](#expressions). Creation evidence checks the arity with
`offersArity` and uses this general environment construction directly. Source functions and shared continuations now lower
to `funE`, and the certificate producer and consumer use its allocating typing
rule. A checked creation effect preserves existing heap knowledge without
executing the body. Allocation, application, bag reads and writes,
and overload conjunction have safety proofs. The graph clause
`callable first rest arrows variadic` combines a nonempty conjunction of bag
invariants with fixed and variadic call promises on one object. Normalization
merges the corresponding lists; structural
subtyping checks invariant bag coverage and arrow coverage separately, and can
forget properties to obtain `arrs`. The producer and consumer support
`makeCallable`, `callCallable`, `readCallable`, and `writeCallable` evidence.
[CallableGraphTests.lean](lean/Verification/Model/Tests/CallableGraphTests.lean)
runs an allocated overloaded object through aliasing, bag mutation, reading,
and invocation using produced evidence and a JSON roundtrip.

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
[CallableRecursiveTests.lean](lean/Verification/Model/Tests/CallableRecursiveTests.lean)
checks the recursive contract `R = callable(null | R; Boolean → Boolean)`:
a function is written into its own bag, read back, narrowed, and invoked.
A second graph captures the object before that write and calls the getter
afterward, exercising a higher-order result and a delayed heap read. Both graphs
use the existing JSON producer and consumer. The first has kernel-checked
certificate acceptance, safety at every budget, descriptor coherence for every
finite run, and an exact terminating execution. Independent recursive labels
can be related by cyclic subtype evidence, while invariant widening and an
unguarded nullable call are rejected. These are regressions over the existing
rules; no recursive-callable special case or additional semantic axiom is needed.
[CallableRecursionTests.lean](lean/Verification/Model/Tests/CallableRecursionTests.lean)
separately checks recursive invocation: a closure reads itself from a captured,
nullable cell and calls it after a function test. Allocation and a self-write
reach a five-step cycle from the empty heap. The test proves arbitrarily many
cycles, nontermination by determinism, safety at every budget, and descriptor
coherence. A small explicit certificate is checked in the kernel; a separate
JSON roundtrip exercises automatic production. An unguarded nullable call and
a recursive call with an incompatible argument are rejected. The safety
contract guarantees progress, not termination.
The existing
`refT` and graph reference clauses still mean plain objects. A callability-neutral
bag view can be expressed as `refs P Ps | callable P Ps []` using two graph
labels. `CallableConjunctions.neutral_iff` proves that this union is precisely
the bag conjunction on scoped values, whatever code they carry; it forgets
invocation promises without changing the object. `NeutralBagTests` supplies checked `unionVar` derivations
for reads and writes through this view. Proof search first tries a single
constructor view, then splits an explicitly union-typed receiver variable for
reads, writes, and calls, using the existing `unionVar` evidence. Every alternative
must check; a null alternative cannot be ignored. Both allocation shapes run
through the same read/write graph and JSON protocol without a runtime tag
branch. The view makes no invocation promise.
[CallableUnionTests.lean](lean/Verification/Model/Tests/CallableUnionTests.lean)
checks calls through unions of known signatures with different bags and result
types, including erased property views. Every alternative must accept the
actual argument and produce a result covered by the requested type. This does
not invent a signature from `typeof`, pick a successful alternative, or require
a common arrow label in the graph. The producer emits ordinary `unionVar`
evidence; the consumer and wire format are unchanged.
[SourceCallableUnionTests.lean](lean/Verification/Model/Tests/SourceCallableUnionTests.lean)
checks the corresponding source-closure path for unions of primitive-only
function signatures. Its direct recipe saves the callee and argument in order,
then checks each alternative at the saved callee slot and joins the signature
results. Expression obligations require no expression-search fuel. The complete
source consumer still checks supplied result claims, rejects an incompatible
alternative or nullable callee, and retains the external-object boundary.
Single-arrow call recipes keep their existing form.
Explicit normalized source claims also exercise unions of overloaded functions:
the applicable signature occurs at different positions in the two alternatives,
and changing from a null to a Boolean argument reverses those positions. Both
calls verify; discarding a possible result or omitting one alternative's applicable
signature fails. This validates the source adapter and independent consumer,
while SKJS's documented collapse of incomparable arrow intersections to `never`
still prevents these contracts from arriving as valid SKJS exports.
Null-guard regressions retain every callable alternative on the non-null arm
for both comparison polarities and operand orders. Calls on the null arm and
unjustifiably narrow results fail. The `guardedCallableUnion` TypeScript fixture
also runs through the parser, SKJS claim exporter, independent source consumer,
and annotated report pipeline. Report syntax groups arrow alternatives and
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
[SourceCellUnionTests.lean](lean/Verification/Model/Tests/SourceCellUnionTests.lean)
checks reads and writes through unions of locally allocated invariant cells
inside source closures. Reads join possible contents. Writes check the saved
RHS against every alternative, evaluate each operand once, and return that RHS
as the source assignment value. Direct recipes need no expression-search fuel.
A write accepted by only one alternative and an unjustifiably narrow read
claim fail the source consumer. Captured current-content assertions produce a
located obligation over the union of invariant contents; broad observations
verify, while narrowing to the allocation's initial value fails. The external-cell
parameter restriction remains in force. Statement-entry regressions cover nested
closures after writes, preserving named captures alongside anonymous evaluation
slots. An entry environment that narrows the captured storage contract fails its
own obligation even when its separate contents observation is provable.
Typed reads retain current heap
facts and read links when every alternative has the same invariant operand.
The regression keeps a known `false` fact about another cell across a neutral
read, then checks a singleton result from that cell through the JSON pipeline. Source export of a combined callable/property type covers one required `value`
field on a function.
Source integration also needs explicit property-presence/initialization rules:
the model's initial function bag does not establish a source `value` field.
Object parameters are admitted at their annotation: the interpretation of a
structural annotation as a plain data object is part of the caller contract,
as the arrow interpretation already was (DESIGN.md, the trust boundary). The
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

$$
\mathsf{object}(\ell,\delta),
$$

where $\ell$ is its identity and $\delta$ is an internal operation descriptor:

$$
\delta =
\left\langle
  \mathsf{properties}:\pi,\quad
  \mathsf{call}:\operatorname{Option}(\kappa),\quad
  \mathsf{construct}:\operatorname{Option}(\eta)
\right\rangle.
$$

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

$$
\mathsf{isFun}(\mathsf{object}(\ell,\delta))
\iff
\delta.\mathsf{call}\ne\mathsf{None},
$$

and source-level object equality compares identities:

$$
\mathsf{object}(\ell,\delta)
  ===
\mathsf{object}(\ell',\delta')
\iff
\ell=\ell'.
$$

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

$$
\begin{aligned}
&\operatorname{Call}(f,r,\bar a),\\
&\operatorname{Construct}(f,\bar a,n),\\
&\operatorname{Get}(o,k,r),\\
&\operatorname{Set}(o,k,v,r).
\end{aligned}
$$

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

$$
\operatorname{Get}(o,k)=H(o)[k].
$$

An object may have data properties, accessors, inherited properties, and
symbol-keyed properties. Property operations can invoke code; proxies can
intercept them. ECMAScript accordingly specifies property descriptors and
internal property operations separately from a simple field store. ([TC39][c1])

C\* should therefore distinguish two semantic assertions:

$$
\mathsf{OwnData}(o,k,A)
$$

for a particular kind of stored property, and

$$
\mathsf{Readable}(o,k,A)
$$

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

$$
\mathsf{Ctor}<:\mathsf{Fun}<:\mathsf{Obj}.
$$

The first inclusion reflects the ECMAScript invariant that an object with
`[[Construct]]` also has `[[Call]]`; it does **not** assert that ordinary
invocation succeeds. ([TC39][c6])

For callable contracts,

$$
\mathsf{Callable}(L;P)
=
\mathsf{Fun}
\cap \mathsf{Props}(P)
\cap \bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma).
$$

This is also the organizing equation of the implemented model, not just the
future object design. [SEMANTICS.md](SEMANTICS.md#one-meaning-for-callable-contracts)
states the indexed call promise precisely and maps each component to Lean.
Fixed and variadic signatures share that promise; code-specific binding rules
establish it at creation. Construction and receivers below remain planned
extensions. Quantified rest signatures use the same universal introduction
and instantiated call promises as fixed signatures.

For construction contracts,

$$
\mathsf{Constructible}(M)
=
\mathsf{Ctor}
\cap \bigcap_{\nu\in M}\mathsf{ConstructSpec}(\nu).
$$

A value usable both ways has their intersection. A property-only view drops the
call and construction requirements without asserting their absence.

The empty call family still means function shape with no supplied call
contract:

$$
\mathsf{Callable}([];P)
=
\mathsf{Fun}\cap\mathsf{Props}(P).
$$

This preserves the distinction between `CFunction` and `CUnknown` above:
knowing that a value is a function is different from merely not excluding
functions.

**Overloads.** Several call contracts are conjunctions of behavioural
obligations:

$$
\mathsf{CallSpec}(L)
\cap
\mathsf{CallSpec}(M)
=
\mathsf{CallSpec}(L\mathbin{+\!+}M).
$$

They are **not** assertions that a writable internal cell has two different
invariant content types. This is the law `TypeAlgebra.overload_append` already
proves for `arrowsT`.

Consequently, placing the implementation in the heap does not itself damage
overloads. The difficulty with A — boxing every function as an ordinary
reference — was typing the implementation through an ordinary writable
reference. A\* avoids that by separating the internal invocation mechanism from
source-level mutation.

**Generics and argument lists.** A call contract must be able to express a
quantified relationship, schematically

$$
\forall\bar X.\;
(R;\alpha)\Rightarrow B,
$$

where $R$ describes the receiver and $\alpha$ describes an argument list.

Quantification is needed for generic input/output relationships; argument-list
contracts handle optional and rest parameters. These are features of the
contract language, not new runtime callable shapes. TypeScript exposes both
generic signatures and these parameter forms. ([TypeScript][c5])

This means the complete account needs more than the finite families of
monomorphic arrows this document has so far. It needs a specified
quantification discipline and rules connecting those richer contracts to the
existing type fragment.

A first-order slice is in
[TypeParams.lean](lean/Verification/Model/Types/TypeParams.lean). The
`HasTy` rules are unchanged. Every constructor has a soundness lemma under a
rigid assignment `η`, including branches, callables and union split. Branch
and `typeof` tests require a non-parameter scrutinee. Instantiating and
applying `id<boolean>(true)` specializes the generic-identity theorem.
`extends` contributes assumptions to `Δ`; `SubP` is inclusion for every `η`
that satisfies `Δ`. `T extends boolean` yields `T ≤ boolean`, not `true ≤ T`.
Source extraction of `id<T>(x: T): T { return x }` is connected, as is
`type Id<T> = T` / `type Box<T> = { value: T }` via substitution,
`T extends boolean` as `T ≤ boolean`, and bodies that copy `T` through
annotated or inferred immutable `const` bindings and extra parameters. Calls to
generic declarations and other generic declaration bodies are not connected.

A separate executable slice connects local quantified closures to the scheme
rules below. One closure per containing function is checked under its rigid
binders and declared bounds. Its certified body may read immutable values or
captured cells, construct a nested closure, or call a callback. Every observed
call supplies a complete ground substitution checked as elimination evidence.
Those instantiations become fixed or variadic signatures for the surrounding graph. Final
acceptance additionally requires the universal certificate described next;
per-instance graph derivations cannot replace it.

**Executable rigid-body certificates.**
[GenericCertificate.lean](lean/Verification/Model/Types/GenericCertificate.lean)
implements proof constructors over the existing calculus. These extend the
certificate checker, not the calculus's runtime or semantic typing rules.
Write $\Delta;\Sigma\vdash p\leadsto e:A$ when a proof $p$ checks, reconstructing
term $e$ and direct type $A$. $\Delta$ contains rigid parameters and bounds;
$\Sigma$ describes runtime slots as either $\mathsf{value}(A)$ or
$\mathsf{cell}(A)$. The latter is a private location with fixed contract $A$,
not a source-visible value type.

The value and captured-cell rules are:

$$
\frac{\Sigma_i=\mathsf{value}(A)}
 {\Delta;\Sigma\vdash\mathsf{var}(i)\leadsto\mathsf{var}(i):A}
\qquad
\frac{\Sigma_i=\mathsf{cell}(A)}
 {\Delta;\Sigma\vdash\mathsf{read}(i)\leadsto\mathsf{read}(\mathsf{var}(i)):A}.
$$

There is no ordinary variable rule for a cell slot. The source lowering takes
its contract from the mutable declaration, never from a point-specific content
claim. Semantically,

$$
\llbracket\mathsf{value}(A)\rrbracket_\eta=\llbracket A\rrbracket_\eta,
\qquad
\llbracket\mathsf{cell}(A)\rrbracket_\eta=
\mathsf{bagT}[(\mathsf{valueField},\llbracket A\rrbracket_\eta)].
$$

Thus `bag_read` reads through the registered location in a satisfying heap;
it does not preserve a snapshot of its contents or change its world contract.

Nested closure construction and callback invocation have the rules:

$$
\frac{\Delta;\mathsf{value}(R)::\mathsf{value}(\bar A){+\!+}\Sigma\vdash p\leadsto b:B}
 {\Delta;\Sigma\vdash\mathsf{lambda}(R,\bar A,p)\leadsto
   \mathsf{make}(\mathsf{closure}(|\bar A|,b),\mathsf{null}):R;\bar A\to B}
$$

$$
\frac{\Delta;\Sigma\vdash p_f\leadsto f:\bar A\to B
 \qquad\Delta;\Sigma\vdash\bar p\leadsto\bar e:\bar C
 \qquad\Delta\vdash(\bar A\to B)\le(\bar C\to B)}
 {\Delta;\Sigma\vdash\mathsf{call}(p_f,\bar p)\leadsto
   \mathsf{call}(f,\bar e):B}.
$$

The arrow comparison enforces equal arity and contravariant argument
compatibility. `invocation_of_body` and `make_callable_rule` justify closure
construction, retaining the outer environment. `call_safe` checks the callee
and every effectful argument in future worlds before invocation. The existing
`let_rule` justifies immutable copies; `widen` applies the proved bounded
subtype relation. No inferred type or producer success flag is a premise.

`Proof.check_safe` proves these constructors safe for every admissible rigid
assignment satisfying $\Delta$, in every admissible world and satisfying heap.
For a quantified closure, `ClosureCertificate.check_safe` holds the captured
environment $\rho$ and world $W$ fixed while quantifying over assignments:

$$
\forall\eta\models\Delta.\quad
\mathsf{InvocationSpec}\bigl(|\bar A|,
 [(\llbracket\bar A\rrbracket_\eta,\llbracket B\rrbracket_\eta)],n,W,
 \mathsf{instantiate}(|\bar A|,\rho,b)\bigr).
$$

This is the universal invocation premise of scheme introduction, independent
of observed calls. `SourceClaimJson.checkJson_safe` requires it alongside the
enclosing graph's safety proof through exhaustive `CertifiedPlan` cases.

### Universal rest collection

Direct types include arrays and variadic signatures over rigid parameters:

$$
\begin{aligned}
\llbracket\mathsf{Array}(E)\rrbracket_\eta
 &= \mathsf{recT}[(\texttt{[]},
       \mathsf{listT}(\langle[],[],\mathsf{some}(\llbracket E\rrbracket_\eta),
                        \mathsf{false}\rangle))],\\
\llbracket(\bar P;E^*)\Rightarrow R\rrbracket_\eta
 &= \mathsf{restsT}[(\llbracket\bar P\rrbracket_\eta,
                     \llbracket E\rrbracket_\eta,\llbracket R\rrbracket_\eta)].
\end{aligned}
$$

`Array(E)` is an ordinary mutable array contract, not a frozen array or an
inference variable. The world's store contract is invariant. The direct
comparison currently requires identical element types; it never derives array
covariance from an upper bound on `E`.

The allocation premises of rest introduction are proved for arbitrary
admissible value families, not just ground graph labels: invocation collects
the store, and the body's first step wraps it (`wrapStore`):

$$
\frac{\forall a\in\bar a.\;a:\llbracket E\rrbracket_\eta}
 {[\bar a]:\mathsf{Store}(\llbracket E\rrbracket_\eta)}
\qquad
\frac{s:\mathsf{Store}(\llbracket E\rrbracket_\eta)}
 {\mathsf{makeAt}\;[\mathsf{store}]\;[s]:\mathsf{Array}(\llbracket E\rrbracket_\eta)}.
$$

`GenericCertificate.store_collect_safe` and `array_wrap_safe` supply the
indexed, heap-safe forms.
Together with a universal body derivation it yields:

$$
\frac{\forall\eta\models\Delta.\quad
  \rho:\Gamma_\eta\ ;\ xs:\mathsf{Array}(E_\eta),\bar x:\bar P_\eta
  \vdash b:R_\eta}
 {\forall\eta\models\Delta.\quad
  \mathsf{RestSpec}(|\bar P|,\bar P_\eta,E_\eta,R_\eta,n,W,
    \mathsf{instantiate}(|\bar P|+2,\rho,\mathsf{wrapStore}(b)))}.
$$

The same captured environment and world occur at every assignment.
`rest_invocation_of_inputs` proves this step; `ClosureCertificate.check_safe`
uses it for both generic declarations and local quantified closures.
`restsT_of_restSpec` then supplies the common behavioral promise. Rest binding
puts the store in slot zero and the receiver in slot one; fixed inputs and
captures follow. After the wrap, the checked body sees the array in slot zero
and the store, which it never reads, in slot one. Parameter defaults retain
their universal initialization obligations.

A direct call through a variadic callback uses a finite-arity consequence:

$$
\frac{f:(\bar P;E^*)\Rightarrow R}
 {f:(\bar P\mathbin{+\!+}\underbrace{[E,\ldots,E]}_{m})\Rightarrow R}
 \quad(m\geq0).
$$

`DirectObligation.variadic_fixed` proves that every actual list admitted by
this fixed view is admitted by the rest promise, including its licensed
omissions. The existing widening and call certificate rules then apply.
The direct subtype decision includes this rule and reflexivity of variadic
signatures; general variance between distinct variadic direct signatures is
not yet part of that decision relation. Ground graph subtyping has its own
broader signature-coverage rules. The decision-completeness theorems below
cover the extended declarative relation, not all semantic inclusions.

### Decision completeness of the direct checker

Declarative judgments state the direct checkers' contracts by rules, without
proof terms or fuel. Source checking is a decision procedure; certificate
completeness states existence of evidence, not a search procedure for it.

`CertificateJudgments.Typed ps Γ t A` types a calculus term over a slot
environment: primitive literals, variables and cell reads from their slots, subsumption along
`RigidJudgments.Sub`, immutable `let`, closures, and calls whose arguments
are each below the callable's parameters. `check_iff_Typed` proves, for
well-formed parameters,

$$
\bigl(\exists p.\;\mathsf{check}(\bar P,\Gamma,p) = (t, A)\bigr)
\quad\Longleftrightarrow\quad
\bar P;\Gamma \vdash t : A .
$$

Left to right needs no hypothesis (`Typed_of_check`). The reverse direction
constructs an accepted certificate from a derivation; `Typed.safe` composes
that direction with `Proof.check_safe`, so
every derivation is safe for every admissible assignment satisfying the bounds.

`SourceJudgments.HasTy c env b t` types a lowered source body — a variable,
a primitive literal, a write into a captured cell below its contract, a call
to a callable binding with each argument below its parameter, or a closure
claimed exactly as annotated with its body below its declared result — and
`SourceJudgments.Checked c env result stmts` types a declaration body: at each
statement the claimed environment has distinct names, exactly the scope's
names, and each claim above the established type; each initializer and the
return is claimed above its established type; a copy's binding type is its
annotation or its initializer's claim; the return's claim is below the
declared result; an expression statement's claim is checked and binds no
name; and a body that ends without a return returns `undefined`:

$$
\frac{\bar P\vdash\{\texttt{undefined}\}\le R}{\bar P;\Gamma\vdash[\,]:R}\;\textsc{done}
\qquad
\frac{\bar P;\Gamma\vdash e:A\quad\bar P;\Gamma\vdash\bar s:R}{\bar P;\Gamma\vdash e;\,\bar s:R}\;\textsc{effect}
\qquad
\frac{\Gamma(\mathit{pos})=(\bar A)\Rightarrow R\quad \bar P;\Gamma,\bar x:\bar A\vdash b:B\quad \bar P\vdash B\le R}
     {\bar P;\Gamma\vdash(\bar x:\bar A)\Rightarrow b:(\bar A)\Rightarrow R}\;\textsc{closure}
$$

where, for a closure the source leaves without a result annotation, $R$ is the
result of the closure's own claimed arrow, whose parameters must be exactly the
annotated ones (`GenericSource.lambdaResult`): the claim proposes the result
and the body is checked against it, as an annotation would be. The
certificate compiler emits `widen R` around such a body, an expression
statement as a `let` of an unnamed slot no source name reads, and the end of a
body as `lit undefined` widened to the declared result. `exprTyB_iff_HasTy` and
`bodyClaimsB_iff_Checked` prove that the pure checker decides both on
well-formed binders, both directions.

`GenericSource.check` is annotation lowering, then that pure checker, then the
signature check, then certificate generation. Lowering is the trusted
translation every annotation takes and is outside these judgments. The
certificate compiler is one for declarations and closures; a body the
judgment accepts and the proof language cannot express is refused by name.
Two such gaps are now closed: a returned call and a returned
primitive literal, both refused before, are certified, the literal through
`Proof.lit` under `GenericCertificate.Primitives`, the assumption that the
graph's first four rows are the primitives, which `FunctionPlan.certify`
establishes for every certified plan. Kernel guards in `SourceJudgments`
record both. This is not an end-to-end completeness theorem for
`GenericSource.check`: lowering, exact signature/site checks and certificate
generation are additional conditions. Captured-cell writes are still typed
by `HasTy.assign` but not expressible by `closureProof`. Certificate existence
also does not prove that OCaml inference finds a suitable substitution or that
graph proof search finds evidence.
Certificates are reconstructed in Lean on consumption; source-to-calculus
correspondence remains part of the stated trust boundary. These theorems prove
soundness of accepted certificates, not decision completeness of proof search.

**Effects and state.** The behavioural obligation must use the computation
semantics, not just a relation between input and output values. Schematically,

$$
\{\mathcal P\}\;
\operatorname{Call}(f,r,\bar a)
\;\{\mathsf{return}\ v.\mathcal Q;\;
    \mathsf{throw}\ e.\mathcal E\}.
$$

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
`makeCallable`, `callCallable`, `readCallable` and `writeCallable`, over the
$\mathsf{Callable}(\varphi;L)$ clause. Nothing below is in force.

The principal distinction is between checking an invocation implementation,
allocating an object carrying that implementation, and using the resulting
object through a contract.

#### Judgments and types

Write

$$
\Gamma\vdash_G t:A\;!E
$$

for a computation whose normal results have type $A$ and whose thrown values
have type $E$. This is a safety judgment, not a termination guarantee. The
annotation bounds exceptions, not mutation. The unannotated judgment
abbreviates $E=\bot$.

Assumptions in $\Gamma$ are stable under permitted heap evolution. Assertions
about current contents belong in the state judgment introduced below.

Call and construction signatures are, respectively,

$$
\sigma=(R;\alpha)\xrightarrow{E}B,
\qquad
\nu=(N;\alpha)\xRightarrow{E}B.
$$

Here $R$ constrains the supplied receiver, $\alpha$ constrains the actual
argument list, and $N$ constrains `new.target`. Construction signatures require

$$
N<:\mathsf{Ctor},
\qquad
B<:\mathsf{Obj}(\top_p).
$$

Argument-list contracts need not specify an exact arity. Parameter binding,
defaults, and destructuring are computations in the function's entry program.

Define the constructor views

$$
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
$$

$P$ is a property contract; $\top_p$ imposes no property requirement. In
particular,

$$
\mathsf{Calls}([])=\mathsf{Fun}.
$$

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

$$
\frac{\Gamma\vdash_G f:\mathsf{Callable}(L;P)}
{\Gamma\vdash_G f:\mathsf{Calls}(L)}
\qquad
\frac{\Gamma\vdash_G f:\mathsf{Callable}(L;P)}
{\Gamma\vdash_G f:\mathsf{Obj}(P)}.
$$

These change the available view, not the value. Neither allocates nor wraps.

**Constructor-Shape.** Construction implies function shape, but supplies no
successful ordinary-call contract:

$$
\frac{\Gamma\vdash_G f:\mathsf{Constructor}(M;P)}
{\Gamma\vdash_G f:\mathsf{Callable}([];P)}.
$$

**Sub.** The ordinary subsumption rule is

$$
\frac{
\Gamma\vdash_G t:A\;!E
\qquad G\vdash A<:B
\qquad G\vdash E<:F
}{
\Gamma\vdash_G t:B\;!F
}.
$$

**Call-Sub.** For unconditional call signatures,

$$
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
$$

Construction signatures have the corresponding variance in `new.target`,
arguments, normal results, and exceptions.

The intended intersection laws are

$$
\mathsf{Calls}(L)\cap\mathsf{Obj}(P)
=
\mathsf{Callable}(L;P),
$$

$$
\mathsf{Callable}(L;P)\cap\mathsf{Callable}(M;Q)
=
\mathsf{Callable}(L{+\!\!+}M;P\wedge Q).
$$

Here $P\wedge Q$ is a conjunction of property contracts. It is not a pointwise
intersection of writable-cell content types.

**Value-Meet.** Intersection introduction on an already obtained value is

$$
\frac{\Gamma\vdash_G v:A\qquad\Gamma\vdash_G v:B}
{\Gamma\vdash_G v:A\cap B}.
$$

Both premises concern the same value under compatible heap invariants.
Independently checking two allocations does not establish an intersection on
one allocated object.

#### Checking code and creating functions

Internal invocation descriptors are not source-level function values. Introduce
auxiliary judgments

$$
\Gamma\vdash_G^{\mathsf{call}}\kappa:L,
\qquad
\Gamma\vdash_G^{\mathsf{construct}}\eta:M,
\qquad
\Gamma\vdash_G^{\mathsf{init}}d:P.
$$

The first two check invocation programs. The third checks an initial property
layout and the invariants it establishes. Initializer expressions have already
been evaluated.

**Ordinary functions: a dynamic receiver.** For strict ordinary-function code,
the rule **Dynamic** is

$$
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
$$

The entry program $t$ includes parameter initialization and the normal-return
convention.

For non-strict functions, the entry program first performs the specified
receiver conversion. The supplied receiver and the body's `this` value must not
simply be identified. ECMAScript distinguishes strict, non-strict, and lexical
receiver binding.

**Arrow functions: a lexical receiver.** The rule **Lexical** is

$$
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
$$

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

$$
\frac{
\Gamma\vdash_G^{\mathsf{call}}\kappa:L
\qquad
\Gamma\vdash_G^{\mathsf{init}}d:P
}{
\Gamma\vdash_G
\mathsf{make}(\kappa,\mathsf{none},d):
\mathsf{Callable}(L;P)\cap\mathsf{NoCtor}
}.
$$

A callable with construction behaviour is introduced by **Make-Constructor**,

$$
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
$$

An ordinary non-callable object is introduced by **Make-Object**,

$$
\frac{\Gamma\vdash_G^{\mathsf{init}}d:P}
{\Gamma\vdash_G
\mathsf{make}(\mathsf{none},\mathsf{none},d):
\mathsf{Plain}(P)}.
$$

Every application of a make rule allocates one fresh object identity. There is
no rule with a construction descriptor but no call descriptor.

The first proposal's $\mathsf{attach}$ operation becomes a special case of
allocation. It is not the operation used to decorate a source function that
already exists.

#### Invocation, property calls, and extraction

**Call.** The ordinary application rule is

$$
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
$$

**Bare-Call.** For a bare call in the strict/module fragment,

$$
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
$$

**Method-Call.** A method call is lookup followed by invocation:

$$
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
$$

For effectful source expressions, the elaboration evaluates the base and key,
performs lookup, evaluates the arguments, and invokes the retrieved function
with the saved base as receiver. It neither reevaluates the base nor binds a
receiver during lookup.

Method extraction is only lookup. Consequently, extraction preserves the
receiver requirement in the function's contract; it does not transform that
contract into a bound-function contract.

#### Properties

Property contracts expose operation signatures. For example,

$$
P\vdash_G\mathsf{get}(k):(R;[])\xrightarrow{E}A
$$

states a contract for lookup at $k$, starting from an object satisfying $P$,
with a receiver in $R$.

The general rules are **Get** and **Set**:

$$
\frac{
\begin{gathered}
\Gamma\vdash_G o:\mathsf{Obj}(P)
\qquad\Gamma\vdash_G r:R\\
P\vdash_G\mathsf{get}(k):(R;[])\xrightarrow{E}A
\end{gathered}
}{
\Gamma\vdash_G\mathsf{get}(o,k,r):A\;!E
},
$$

$$
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
$$

Set returns an internal success flag. A strict source assignment throws on
failure and returns the assigned value on success. That differs from the
calculus's `write`, which returns $\mathsf{Null}$.

**Ordinary data properties.** For a stable, writable own-data-property
invariant, the reference-style rules are recovered as **Read-Cell** and
**Write-Cell**:

$$
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
$$

These apply to callables through Forget-Calls. The cell contract is invariant
and also protects the descriptor assumptions against unchecked deletion or
redefinition.

For a fresh property layout, **Init-Data** is

$$
\frac{\Gamma\vdash_G v:A}
{\Gamma\vdash_G^{\mathsf{init}}
[k\mapsto\mathsf{data}(v)]:
\{k:\mathsf{cell}(A)\}}.
$$

**Accessors.** An own getter is checked by **Init-Getter**:

$$
\frac{
\Gamma\vdash_G g:
\mathsf{Calls}([(R;[])\xrightarrow{E}A])
}{
\Gamma\vdash_G^{\mathsf{init}}
[k\mapsto\mathsf{accessor}(g,\mathsf{none})]:
\{\mathsf{get}(k):(R;[])\xrightarrow{E}A\}
}.
$$

Dually, a setter with call contract

$$
(R;[A])\xrightarrow{E}\top
$$

supplies a set contract returning $\mathsf{True}$ on normal completion: the
setter's returned value is discarded. These rules assume the corresponding
descriptor invariants; inherited lookup additionally requires the
prototype-chain obligations.

General accessors and proxies use Get/Set, not Read-Cell/Write-Cell.

An ordinary property named `call` or `apply` supplies no premise for Call.

#### Construction

**Construct.**

$$
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
$$

**New.** Ordinary `new` uses the constructor itself as `new.target`:

$$
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
$$

**Construction-Code.** The introduction rule checks the complete construction
program:

$$
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
$$

This program includes receiver allocation, prototype lookup, instance
initialization, and explicit-return handling. Derived constructors additionally
require `super` and initialization of `this`. Checking the source body as an
ordinary function returning $B$ is insufficient.

A contract proved only for ordinary `new` may restrict $N$ to the constructor's
own identity. It must not silently become a guarantee for arbitrary
`Reflect.construct` calls.

A class's ordinary-call descriptor can have the exception-aware signature

$$
(\top;\mathsf{Args})
\xrightarrow{\mathsf{TypeError}}\bot.
$$

Thus it has function shape without a successful ordinary-call contract.

#### Overloads, polymorphism, and binding

**Overloads.** The premises of Dynamic and Lexical check the same code against
every advertised signature before allocating one function object. Call selects
an applicable member. Forgetting members is subsumption; no writable
implementation cell is retyped.

**Generic signatures.** Let $S$ be a scheme, $\eta_0$ the assignment outside
its binders, and $\mathsf{Instance}_{G,P}(\eta_0,S,\eta)$ the closed,
bound-satisfying assignment relation defined in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md#quantified-scheme-layer). The exact
introduction rule **Call-Scheme-I**, implemented by `scheme_intro`, is

$$
\frac{
\mathsf{Invocable}(v)
\qquad
\forall\eta.\;
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
\Rightarrow
(\mathsf{Calls}(\mathsf{Sig}_{G,P,\eta}(S),n,W,v)
\land\mathsf{Rests}(\mathsf{RestSig}_{G,P,\eta}(S),n,W,v))
}{
\llbracket S\rrbracket^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
}.
$$

The value $v$, step index $n$, world $W$, and outer assignment $\eta_0$ are
outside the quantifier. The proof is therefore uniform in the binders, and
captured mutable cells retain the same invariant at every instantiation.
Fixed-signature elimination **Call-Scheme-E**, implemented by `scheme_elim`, is

$$
\frac{
\llbracket S\rrbracket^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
\qquad
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
}{
\mathsf{Calls}(\mathsf{Sig}_{G,P,\eta}(S),n,W,v)
}.
$$

For rest signatures, `scheme_rest_elim` gives the corresponding conclusion
$\mathsf{Rests}(\mathsf{RestSig}_{G,P,\eta}(S),n,W,v)$ from the same premises.

The executable source substitution $[\bar A/\bar X]$ constructs one such
$\eta$ only after its ground arguments and bounds have been checked. It selects
a signature of the same callable; it neither allocates a new value nor changes
the outer assignment. These are rules for quantified invocation contracts, not
unrestricted generalization of an effectful allocation expression.

[TypeSchemes.lean](lean/Verification/Model/Types/TypeSchemes.lean) realizes
these rules as `scheme_intro` and `scheme_elim`: one callable value and one
captured world satisfy every admissible assignment, while elimination selects a
signature only afterwards. The source checker admits the restricted local
closure form described above. Schemes do not become graph clauses; checked
eliminations become fixed or variadic graph signatures. Introduction requires the
independently reconstructed rigid-body certificate described above; it is not
yet serialized as a first-class scheme node in the graph evidence.

**Generic bodies.** A generic function's body is a graph request whose
binders are parameter rows $\vec p$: rows the graph's assignment interprets,
which no rule reads (a type holding one has no expansion). Acceptance does not
read the assignment (`Parametricity.accept_reassign`), so the rule
**Generic-Body** is the ordinary safety theorem at every reassignment:

$$
\frac{
\mathsf{accept}(G,R,P,\mathit{claims},C,s,\vec I)=\mathsf{true}
\qquad
\mathsf{EnvOk}_{G[\mathit{env}:=\eta]}(\vec I,\rho,n,W)
\qquad \mathsf{WorldAdm}(W)\qquad \mathsf{HeapOk}(n,W,h)
}{
\mathsf{SafeGraph}\bigl(P,\llbracket R\rrbracket^{\eta},n,W,h,\mathsf{at}(s,\rho)\bigr)
}
\quad\text{for every }\eta .
$$

One derivation, checked once, covers every instantiation of the binders: the
inputs and the result are read at the same $\eta$. The binders of a generic
class are those of the unit that declares it, the module's initialization
unit, so its constructor and methods are certified at every instantiation the
same way. Lean:
`Parametricity.accepted_at`, `RequestJson.verify_safe_at`,
`SourceExtraction.checkRequests_safe_at`.

**Bound functions.** The internal bound-call descriptor has the rule
**Bound-Code**:

$$
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
$$

Allocation gives this descriptor a fresh identity and its own properties. The
target's property contract is not copied.

For construction, a bound object $g$ forwards as

$$
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
$$

Its construction contracts must be checked against this program; the bound
receiver is not used as the constructed receiver.

Source `f.call`, `f.apply`, and `f.bind` remain property lookups followed by
calls. Specialization requires the retrieved operation to be the standard
intrinsic. Argument extraction and the prototype, name, and length operations
of the full binding algorithm are separately checked computations. Bound-Code
is not a blanket no-effect rule for `.bind`.

#### Stateful contracts

Use the additional judgment

$$
\Gamma\vdash_G
\{\Phi\}\ t\
\{z:B.\Psi\mid e:E.\Xi\}.
$$

It specifies normal and exceptional postconditions. The ordinary judgment is the
special case with no additional precondition or postcondition beyond type
safety and the ambient invariants. It is the exception-aware form of the
[Hoare typing above](#checked-expression-postconditions), whose $\Pi$ and
$\Sigma$ are one way of writing $\Phi$ and $\Psi$.

A stateful call signature is

$$
\sigma=
(r:R;\mathsf{argv}:\alpha)
\{\Phi\}
\Rightarrow
\{z:B.\Psi\mid e:E.\Xi\}.
$$

Contracts may refer to a distinguished $\mathsf{self}$ denoting the callable.
Let $\theta$ substitute the actual callable, receiver, and argument list for
these formal names. **Call-State** is

$$
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
$$

The corresponding introduction rule checks the entry body under $\Phi$ and
establishes $\Psi,\Xi$. Construction, lookup, and update have the same stateful
form.

Only facts supported by postconditions, stable invariants, or a justified frame
rule survive a call. A transient observation is not promoted into a permanent
callable or property type.

**Decoration.** A representative strong property-addition rule is

$$
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
$$

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

$$
\frac{
\Gamma\vdash_G f:\mathsf{Fun}
\qquad\Gamma\vdash_G h:\mathsf{Obj}(\top_p)
}{
\Gamma\vdash_G\mathsf{proxy}(f,h):\mathsf{Fun}
}.
$$

There is no rule automatically copying the target's signatures. A stronger
contract requires checking the dispatch program: revocation check, handler
lookup, and target or trap invocation. Those operations can change the
behaviour relative to the target.

For a callable revocable proxy $q$, the state rules include

$$
\Gamma\vdash_G
\{\mathsf{Revocable}(q)\}\mathsf{revoke}(q)
\{z:\mathsf{Undefined}.\mathsf{Revoked}(q)
\mid e:\bot.\bot\},
$$

$$
\Gamma\vdash_G
\{\mathsf{Revoked}(q)\}\mathsf{invoke}(q,r,\bar a)
\{z:\bot.\bot
\mid e:\mathsf{TypeError}.\top\}.
$$

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

$$
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
$$

The true branch gains shape, not an arbitrary signature. Graph slicing must
represent or safely approximate the refined views.

**Identity.** Object identity has the rule

$$
\frac{
\Gamma\vdash_G f:\mathsf{Obj}(\top_p)
\qquad
\Gamma\vdash_G g:\mathsf{Obj}(\top_p)
}{
\Gamma\vdash_G\mathsf{same}(f,g):\mathsf{Bool}
}.
$$

Its refinement postcondition is

$$
b\iff\operatorname{id}(f)=\operatorname{id}(g).
$$

Allocation additionally establishes freshness relative to identities existing
at entry. Subsumption establishes neither allocation nor freshness.

#### Async and generator callables

Their application uses Call. Their introduction needs additional computation
judgments, not additional callable-object representations.

What is implemented is weaker and trusted: `await` and an async body's returns
are calls of intrinsic values at declared signatures, and **Await**,
**Async-Return** and **Async-Complete** are instances of Call
([DESIGN.md, Async functions and await](DESIGN.md#async-functions-and-await)).
The judgments below remain the target that would discharge that trust.

An asynchronous entry judgment

$$
\Gamma,\mathsf{this}:R,\mathsf{argv}:\alpha
\vdash_G^{\mathsf{async}}
t:\mathsf{PromiseSpec}(B,E)
$$

must check entry and resumption, including parameter initialization, promise
resolution, thenable assimilation, rejection, and state invariants across
suspension. These are obligations of the asynchronous execution semantics.

Its introduction schema, **Async-Code**, is

$$
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
$$

This schema assumes the entry proof accounts for ordinary entry failures as
rejections; other synchronous failure paths must be advertised separately.
$\mathsf{PromiseSpec}$ constrains fulfillment and rejection, not eventual
settlement.

For generators, let $\Pi$ be a protocol describing operations and transitions,
including `next`, `throw`, and `return`. Then **Generator-Code** is

$$
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
$$

A protocol transition supplies a stateful contract for the corresponding
method. It must account for suspension, completion, and subsequent operations
on a completed generator.

These last two are module interfaces. Defining their premises requires an
async/coroutine logic; merely giving the names of those judgments does not
provide that logic.

#### A distinguishing instance

Let

$$
D=\mathsf{Obj}(\{n:\mathsf{cell}(\mathsf{Number})\}),
$$

$$
M=(D;[])\to\mathsf{Number},
\qquad
A=(\top;[])\to\mathsf{Number}.
$$

For a checked incrementing body, Dynamic gives $M$ to an ordinary method.
Lexical gives $A$ to an arrow capturing an instance of $D$.

After allocation, suppose

$$
m:\mathsf{Calls}([M]),
\qquad
a:\mathsf{Calls}([A]),
\qquad
o:D.
$$

Then

$$
\Gamma\vdash_G
\mathsf{invoke}(m,o,[]):\mathsf{Number},
$$

$$
\Gamma\vdash_G
\mathsf{invoke}(a,\mathsf{undefined},[]):\mathsf{Number}.
$$

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
