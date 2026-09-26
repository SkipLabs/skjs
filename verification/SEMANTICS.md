# Semantics

The stateful development in [Model](lean/Verification/Model)
provides the semantic foundation for the positive-type rules specified in
[POSITIVE-TYPES.md](POSITIVE-TYPES.md). This is the semantics used by the current verifier. [PROGRAM-TYPING.md](PROGRAM-TYPING.md) specifies the proved program
typing system and checked control-flow graphs. The
[source integration status](DESIGN.md#source-integration)
distinguishes the supported source fragment from model-only features.

## Operational language

`Calculus.lean` defines an untyped call-by-value language with a mutable heap.
The following is the original one-field kernel notation, not an exhaustive
constructor inventory (see `Tm` in `Calculus.lean` for the maintained syntax):

$$t ::= x_i\mid t\,t\mid\mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}
\mid\mathsf{obj}(\ell,c)\mid\mathsf{make}(c,t)\mid\mathsf{let}(t,t)
\mid\mathsf{read}(t)\mid\mathsf{write}(t,t)
\mid\mathsf{test}_k(t)\mid\mathsf{if}\;t\;t\;t.$$

Here $x_i$ is a variable, given as a de Bruijn position, $\ell$ a heap location,
and $k$ a shape test
drawn from $\{\mathsf{isNul},\mathsf{isUndef},\mathsf{isNullish},\mathsf{isBool},\mathsf{isRef},\mathsf{isFun}\}$.
The nullish test accepts null or undefined; the others recognize individual value shapes. Values are
the subset

$$v ::= \mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{obj}(\ell,c),$$

where $c ::= \mathsf{absent}\mid\mathsf{closure}(m,t)\mid\mathsf{variadic}(m,t)\mid\mathsf{bound}(f,r,\vec p)$ is a separate invocation
descriptor, the first two with a declared parameter count `m`. A closure body is
under `m + 1` binders: the receiver of the call in slot 0, then its parameters.
A variadic body has its rest store in slot 0, the receiver in slot 1, then `m`
parameters; its first step wraps the store into the array its rest parameter
names. `bound` is the forwarding descriptor `.bind` creates: the target, the
receiver and the argument prefix it saved, values that no field holds and no
write can reach. An argument list is not a value: which lists a rest
parameter's type admits is a separate contract on lists of values
([argument packs](POSITIVE-TYPES.md#argument-packs)).
`make c a` evaluates its initializer `a`, then appends that value
to the heap and returns `obj h.length c`, where `h.length` is the length
before appending.
`alloc a` abbreviates `make absent a`; `attach b a` abbreviates
`make (closure 1 b) a`; `funE b` abbreviates `make (closure 1 b) null`.
All three use the same constructor and the same allocation step, `Step.makeV`.
The closure body is not evaluated during creation. There is no bare lambda value.

Since that kernel, the values also include numbers (the bit pattern of the
double), strings, bigints $\mathsf{bigint}(i)$ with $i\in\mathbb Z$ (a bigint is
its integer, as a number is its double) and symbols $\mathsf{sym}(i)$ (a symbol
is its identity: distinct declarations are distinct symbols); an object's fields are keyed by property
keys $\kappa::=\mathsf{str}(s)\mid\mathsf{sym}(i)$; and the tests include
$\mathsf{isNum}$, $\mathsf{isStr}$, $\mathsf{isBigint}$, $\mathsf{isSymbol}$,
$\mathsf{isArray}$, $\mathsf{typeofObject}$, $\mathsf{hasKey}(\kappa)$, the singleton equalities of every primitive kind that carries a value
($\mathsf{numEq}(b)$ by `Number::equal`, $\mathsf{strEq}(s)$, $\mathsf{boolEq}(q)$,
$\mathsf{bigintEq}(i)$, each false on every other kind) and $\mathsf{truthy}$, JavaScript's `ToBoolean`:

$$
\mathsf{truthy}(v)=\mathsf{false}\iff v\in\{\mathsf{null},\mathsf{undefined},\mathsf{false},
\mathsf{num}(\pm0),\mathsf{num}(\mathrm{NaN}),\mathsf{str}(\texttt{""}),\mathsf{bigint}(0)\}
$$

(`numberTruthy`: a number is falsy where it equals zero or is not equal to
itself); every object, function, class, symbol and store is truthy. $\mathsf{isArray}$ holds of a
plain object owning the array store key $\sigma$, which no source property
names, so it holds of exactly the arrays, as `Array.isArray` does of
JavaScript's Array exotic objects:
$\mathsf{isArray}(\mathsf{obj}(\mathit{fs},\mathsf{absent}))\iff\sigma\in\operatorname{dom}\mathit{fs}$,
and false of every other value. $\mathsf{typeofObject}$ holds of
$\mathsf{null}$ and of an object without call code, which is where `typeof`
answers `"object"`: $\mathsf{typeofObject}(v)\iff v=\mathsf{null}\lor v=\mathsf{obj}(\mathit{fs},\mathsf{absent})$.
$\mathsf{hasKey}(\kappa)$ is `in`: it holds of an object owning the key
$\kappa$, whatever its code, or lacking it and holding under the prototype key
$\pi$ an object of which it holds, as far as the heap reaches, and of no other
value. It is the one test that reads the heap (`tagHoldsIn`, `keyInChain`):

$$
\mathsf{hasKey}_h(\kappa)(\mathsf{obj}(\mathit{fs},c))\iff\kappa\in\operatorname{dom}\mathit{fs}\ \lor\
  (\mathit{fs}(\pi)=\ell\land\mathsf{hasKey}_h(\kappa)(h(\ell)))
$$

bounded by the heap's length, so a chain the heap makes cyclic, which no
JavaScript object has, answers false. Keys are fixed at allocation and no
source writes a prototype, so its answer never changes. It is `in` for the
keys the lowering admits ([DESIGN](DESIGN.md#guards)); JavaScript's `in`
throws on a primitive. For $\kappa_C$, the key only class `C`'s prototype
object owns, it is `instanceof C`: an object along whose chain that
prototype is, and `false` of a primitive, as JavaScript's `instanceof`
answers. Where the object owns the key or holds no prototype
(`protoFree`) the answer is the heap-free $\kappa\in\operatorname{dom}\mathit{fs}$
(`tagHoldsIn_of_protoFree`), which is what a type's answer states. A closure descriptor records which invocation its code
admits, $\mathsf{closure}(m,t,\mathit{kind})$ with
$\mathit{kind}\in\{\mathsf{call},\mathsf{construct}\}$: JavaScript gives a
function object `[[Call]]` and `[[Construct]]` separately, an arrow has only
the first and a class only the second. A plain call dispatches only call code
(`dispatch` refuses construct code), and $\mathsf{new}\,f(\vec a)$ is its own
term, which evaluates the callee, then the actuals left to right, and runs only
construct code, with `undefined` for the receiver:

$$
\frac{h,f\to h',f'}{h,\mathsf{new}\,f(\vec a)\to h',\mathsf{new}\,f'(\vec a)}
\qquad
\frac{f\ \text{a value}\quad a_1,\ldots,a_{i-1}\ \text{values}\quad h,a_i\to h',a_i'}
     {h,\mathsf{new}\,f(\vec a)\to h',\mathsf{new}\,f(\vec a[i:=a_i'])}
$$

$$
\frac{\vec a\ \text{values}}
     {h,\mathsf{new}\,\mathsf{obj}(\mathit{fs},\mathsf{closure}(m,b,\mathsf{construct}))(\vec a)
      \to h,\mathsf{bind}_m(\vec a,\mathsf{undefined},b)}
$$

(`constructL`, `constructArg`, `constructV`), where $\mathsf{bind}_m$ is the
same parameter binding a call uses, missing actuals `undefined`. The step
relation stays deterministic (`Step_det`). What a construct signature promises
is in [the clause's meaning](POSITIVE-TYPES.md#functions-and-classes):
the construct step's result is safe at the signature's result, one level below
the budget, as a call's body is.

**Allocation from parts.** $\mathsf{merge}_\delta(a,b)$ (`Tm.merge`)
evaluates $a$, then $b$ (`mergeC1`, `mergeC2`), then reads, in the heap as it
is, the fields $a$'s object owns but the array store $\sigma$, and the own
enumerable data properties $b$ has, less the keys in $\delta$, and steps to
the allocation of both, $b$'s over $a$'s:

$$
\frac{\mathsf{own}_h(v_a)=P\quad\mathsf{data}_h(v_b)=Q}
     {h,\ \mathsf{merge}_\delta(v_a,v_b)\to h,\ \mathsf{makeAt}(\mathsf{absent},\ P\lhd(Q\setminus\delta))}\ (\texttt{mergeV})
$$

where $\mathsf{own}_h(\mathsf{obj}(\mathit{fs},\mathsf{absent}))$ is each key of
$\mathit{fs}$ but $\sigma$ at its value (the first entry of a key, as a read
finds it); $\mathsf{data}_h(\mathsf{obj}(\mathit{fs},\mathsf{absent}))$ is each
string key of $\mathit{fs}$ but $\sigma$ and $\pi$ at its value, then, for an
array, each element under its index's decimal spelling; $\mathsf{data}_h$ of
$\mathsf{null}$, $\mathsf{undefined}$, a Boolean, a number, a bigint or a symbol
is empty; and $P\lhd Q$ keeps $P$'s entries whose key $Q$ lacks, then $Q$'s
(`mergeParts`, `ownAll`, `ownData`, `mergeData`). A value the heap lacks, or a
term that is not a value there, reads as `undefined`, so the step never
depends on one (`heapVal`). The step is stuck on any other value, a string
or a function. It allocates nothing itself; the `makeAt` it steps to does, as
a literal's. Symbol-keyed fields are not read ([DESIGN](DESIGN.md#object-literals)).

**Binary operators.** $a\mathbin{op}b$ (`Tm.arith`) evaluates $a$, then $b$
(`arithC1`, `arithC2`), then takes one step where the operator answers for the
two values, or throws where JavaScript throws, and is stuck otherwise:

$$
\frac{\mathsf{binop}(op,v_1,v_2)=v}{h,\ v_1\mathbin{op}v_2\to h,\ v}\ (\texttt{arithV})
\qquad
\frac{\mathsf{binopThrows}(op,v_1,v_2)}{h,\ v_1\mathbin{op}v_2\to h,\ \mathsf{throw}\ \mathit{err}}\ (\texttt{arithThrow})
\qquad op\in\{+,-,*,/,\%,{*}{*},\mathbin{\hat{}},<,\le,>,\ge,\equiv\}.
$$

$\mathsf{binop}$ is JavaScript's operation on the operand kinds it models;
$\mathsf{binopThrows}$ is where JavaScript throws with no code of the
program's run first, and $\mathit{err}$ the error object (`thrownError`, an
object without fields, standing for the `TypeError` or `RangeError`
instance). Neither answers where JavaScript converts through code or
coercions the calculus does not have:

| Operands | Arithmetic ($+,-,*,/,\%,{*}{*},\hat{}$) | Relational ($<,\le,>,\ge$) |
| --- | --- | --- |
| two numbers | the IEEE-754 double operation; ${*}{*}$ is `Number::exponentiate` (C's `pow`, but NaN for a NaN exponent and for a base of magnitude 1 to an infinite power); $\hat{}$ is exclusive or after `ToInt32` on both; $\%$ is `Number::remainder`, exact: $n-d\cdot q$ for $q$ the quotient truncated toward zero, with $n$'s sign (so `-4 % 2` is $-0$), NaN for a NaN or infinite $n$ or a NaN or zero $d$, and $n$ itself for an infinite $d$ or a zero $n$ | the IEEE order: false when either is NaN, the two zeros equal |
| two bigints | the integer operation; $/$ truncates toward zero and $\%$ is the remainder it leaves, with the dividend's sign; throws for $/$ or $\%$ by $0$ and ${*}{*}$ by a negative exponent (a `RangeError`) | the integer order |
| a number and a bigint | throws (a `TypeError`) | the exact order of the double's rational value and the integer; false when the number is NaN, an infinity beyond every integer |
| two strings | $+$ concatenates; others none | lexicographic over UTF-16 code units, a proper prefix less |
| a string and a number, bigint, Boolean, `null` or `undefined`, either order | $+$ concatenates the string with $\mathsf{str}$ of the other, in operand order; others none | none |
| a symbol and a primitive, either order | throws (a `TypeError`: `ToString` or `ToNumeric` of a symbol) | throws |
| anything else | none | none |

Strict equality $\equiv$ (`===`, `Arith.eq`; `strictEquals`) answers a Boolean
where JavaScript's `IsStrictlyEqual` needs no identity the model lacks:

$$
v_1\equiv v_2=\begin{cases}
\mathsf{sameValue}(v_1,v_2) & v_1\ \text{or}\ v_2\ \text{a primitive}\\
\mathit{fs}_1=\mathit{fs}_2 & v_i=\mathsf{objAt}(\mathit{fs}_i,c_i),\ \mathit{fs}_1\neq[\,]\ \text{or}\ \mathit{fs}_2\neq[\,]\\
\text{none} & \text{two objects without fields, two stores}
\end{cases}
$$

$\mathsf{sameValue}$ is false across kinds, `Number::equal` on two numbers
(NaN equals nothing, the zeros each other), and equality of the string, the
bigint, the Boolean or the symbol, `null` and `undefined` each only to itself.
An object value is the locations of its fields, which only its allocation
creates, fresh (`makeV`): two objects with a field are one object exactly when
their locations are. Two objects without a field (two closures, two empty
records) would be the same value here though JavaScript tells them apart, so
they have no answer, and the typing rule refuses them. Strict equality converts nothing, so it never
throws ($\mathsf{binopThrows}$ is false for $\equiv$).

$\mathsf{str}(v)$ (`primString`) is JavaScript's `ToString` of a primitive
other than a symbol, which runs no code: a string is itself, `true`, `false`,
`null` and `undefined` their names, a bigint its decimal integer with a leading
`-` when negative, and a number `Number::toString` in radix 10
(`numberToString`): `NaN`, `Infinity` with its sign, `0` for both zeros, and
otherwise the fewest decimal digits $s$ whose value $s\cdot10^{d}$ rounds to
the double, the one closest to it where several have that length (the even one
on a tie, as the specification's note recommends and engines do), written
plainly up to 21 integer digits, as `0.` and up to six zeros below one, else
in exponent form `d.ddde±x`. A symbol converts by throwing a `TypeError`,
which $+$ with it does (`binopThrows`), and an object through its own
`toString`/`valueOf`, which is code: $+$ with one is stuck.

So the operation never computes on a value it would convert through code or a
coercion it does not define: a string compared with a number, a Boolean in
arithmetic and an object (whose `valueOf` is code) all leave the term stuck,
which the typing rule rules out. The unary operators are this one with a
constant right operand of the operand's family ([source
forms](PROGRAM-TYPING.md#judgments-and-constructor-views)): $-x=x*(-1)$, $+x=x*1$
and $\sim x=x\mathbin{\hat{}}(-1)$, exact on doubles (a sign flip, the identity,
`ToInt32` complemented) and on integers alike. Lean: `binop`, `arithBits`, `remBits`,
`bigintArith`, `doubleIntOrder`, `utf16Units`, `primString`, `numberToString`
(`Semantics/Calculus.lean`); the values it gives are checked against node's for
the edge cases, and `numberToString` for 300 pseudo-random doubles and short
decimals besides, in `Tests/SourceExtractionTests.lean`.

**Strings.** A string owns its `length` and its index properties, and
`lenOf` and `elemAt` read them as they read a store's:

$$
\frac{}{h,\ \mathsf{lenOf}\;\mathsf{str}(s)\ \to\ h,\ \mathsf{num}(|\mathit{units}(s)|)}\ (\texttt{lenStr})
\qquad
\frac{}{h,\ \mathsf{elemAt}\;\mathsf{str}(s)\;\mathsf{num}(b)\ \to\ h,\ \mathit{codeUnitAt}(s,b)}\ (\texttt{elemStr})
$$

where $\mathit{units}(s)$ is $s$'s UTF-16 code units (`utf16Units`) and
$\mathit{codeUnitAt}(s,b)$ is the one-unit string at the array index $b$
denotes (`indexOfBits`, so `-0` is index 0) below the length, and
`undefined` at any other number: past the end, negative, fractional, NaN or
infinite, JavaScript finds no own property and the realm's `String.prototype`
and `Object.prototype` own no numeric key. A model string is a sequence of
Unicode scalar values, as Lean's `String` is, so half of a surrogate pair has
no string of its own: it reads as U+FFFD (`unitString`), where JavaScript
yields the lone half. This is the one place the model's strings differ from
JavaScript's; the fragment computes on a string only by equality, order,
length and these reads, and both are strings of one code unit.

Every other member of a primitive is its wrapper prototype's: JavaScript's
`ToObject` makes a wrapper whose `[[Prototype]]` is the realm's
`String.prototype` (`Number.prototype`, `BigInt.prototype`,
`Boolean.prototype`), and the read continues there. The calculus writes that
wrapper as it is: a fresh object owning only `[[proto]]`,
$\mathsf{makeAt}\;\mathsf{absent}\;[\mathsf{proto}]\;[P]$ with $P$ the realm's
prototype, from which `readProto` reads the member. No step is added.

`make_rule` proves heap and world extension once, with a result obligation for
the fresh object's descriptor. `alloc_rule` and `attach_rule` specialize that
proof to plain reference and callable contracts.

[ObjectCoherence.lean](lean/Verification/Model/Semantics/ObjectCoherence.lean)
proves the separate identity invariant. An append-only ghost registry records
each allocation's descriptor. Every object occurrence in terms, closure bodies,
and heap cells agrees with that registry; an already allocated closure has no
free variables other than its argument. Substitution therefore preserves its
descriptor. `step_preserves` follows the existing `Step` relation and proves that
reads, writes, calls, and allocation preserve coherence, including heap cycles.
The registry is proof data, not an additional runtime heap.

[GraphCoherence.lean](lean/Verification/Model/Semantics/GraphCoherence.lean)
lifts this to the existing graph execution, including saved environments and
slot maps. The graph consumer checks `sourceTerm` on every node, forbidding
embedded runtime identities even inside unselected branches and empty-overload
bodies. `accepted_closed_coherent` covers every finite prefix of an accepted
closed invocation. External invocations preserve a supplied coherent heap and
environment, with all pre-existing descriptors unchanged. This theorem is
separate from semantic type safety: arbitrary raw terms and the unrestricted
semantic families do not themselves impose a global registry.

`Val` abbreviates `Tm`, so worlds, heaps and the step relation all speak
about the same objects. `letE a b` is an explicit binding: it evaluates `a`,
then substitutes the resulting value into `b` in one step without changing the
heap. Only `b` is under the new binder. `HasTy.letE`, source lowering, and the
certificate producer and consumer all use that constructor. `Step_det` proves
that a term and heap have at most one successor.

A read of a named property on an object with no such own field continues at
the object's prototype, when it has one: the reserved key `protoField` holds
it, no source name spells it, and one step turns the read into the same read
of the prototype (`Step.readProto`, `Step.indexProto` for a computed key).
Without a prototype the read steps to `undefined` (`Step.readMissing`,
`Step.indexMissing`); a present field still reads its heap location. A computed
key is converted by `ToPropertyKey` first, where it runs no code: a string is
its own key, a symbol its identity, and a number the key its `ToString`
spells, so `o[1]` reads `o["1"]` (`propertyKey`); `indexAt` on any other key
is stuck:

$$
\mathsf{key}(\mathsf{str}\,s)=\mathsf{str}(s)\qquad
\mathsf{key}(\mathsf{sym}\,i)=\mathsf{sym}(i)\qquad
\mathsf{key}(\mathsf{num}\,x)=\mathsf{str}(\mathsf{ToString}(x))
\qquad
\frac{\mathsf{key}(v)=k\quad\mathit{fs}(k)=l\quad h(l)=u}
     {h,\ \mathsf{indexAt}\;(\mathsf{obj}(\mathit{fs},c))\;v\ \to\ h,\ u}
$$

and `indexProto`, `indexMissing` as `readProto`, `readMissing` at
$\mathsf{key}(v)$:

$$
\frac{\mathit{fs}(k)=\varnothing\quad\mathit{fs}(\mathsf{proto})=l\quad h(l)=p}
     {h,\ \mathsf{readAt}\;k\;(\mathsf{obj}(\mathit{fs},c))\ \to\ h,\ \mathsf{readAt}\;k\;p}
\qquad
\frac{\mathit{fs}(k)=\varnothing\quad\mathit{fs}(\mathsf{proto})=\varnothing}
     {h,\ \mathsf{readAt}\;k\;(\mathsf{obj}(\mathit{fs},c))\ \to\ h,\ \mathsf{undefined}}
$$

The semantic index view `dictViewT K A` requires the object to have no
prototype and every *present* field under a key the class `K` admits (every
string key, the canonical numeric ones, or every symbol key: `IndexKeys`,
[POSITIVE-TYPES](POSITIVE-TYPES.md#records)) to have a stored contract implying
`A` at lower budgets. This is guarded
and admissible even when `A` is recursive, and it grants no write permission.
`empty_bool_dict_missing` witnesses the distinction: an empty object satisfies
the Boolean dictionary view, while a read of any key yields `undefined`, which
is not Boolean. An arbitrary indexed read therefore needs a result including
`undefined`. The positive graph has a `dict` clause whose operands are guarded
recursive labels, and the checked covering rule can compare dictionary views.
The source parser and OCaml producer lower inline index annotations into that
clause. A key the clause names as a field or view is read at that member's
contract by `read` or `readView`, whose premise `namedMembers` accepts a
dictionary's named members as a record's. Any other named key read uses the
proved `readDict` rule, through an index whose class surely admits the key; a
computed key uses `indexAt`, which evaluates the receiver before the key and
then reads the selected field (or `undefined` if it is absent). The proved
`indexDict` rule checks the key at the key clause of a class within the
index's (`string`, `number` or `symbol`; a number's key is canonical numeric,
`numeric_admits_number`). Both reads carry `undefined` in their result. This path reaches the same certified
source acceptance theorem as other expressions. A fresh literal is a
dictionary through its exact own keys: `alloc` bounds them among the literal's
names (`ownKeysT_slots`), and a record so bounded, with no prototype key among
them, meets an index view whose contract every field's is within, and a
writable index equivalent to every field's (`covers_keys_sound`); an existing
open record, which may hold further keys, meets neither. A mutable index
signature lowers to a writable index contract `dictCellT K A`, whose present
fields under keys of `K` have contracts agreeing with `A` rather than implying
it, and covering keeps it invariant. Imported recursive declarations remain outside the source fragment.

Term and descriptor equality use explicit structural comparisons, each returning
a kernel-checked `Decidable` result and recurring only on strict subterms. This
keeps certificate equality executable for list-valued
applications: Lean's `DecidableEq` deriving handler does not support nested
mutually recursive types. The comparisons inspect every constructor field,
including descriptor arity.

Two different things are named here, and both run through the whole development.
A **binding** lives in the environment $\rho$; a **location** $\ell$ is an address
in the heap $h$. This is the usual store/heap pair of an ML-style operational
semantics. A binding may *hold* an object: $\rho(x)=\mathsf{obj}(\ell,c)$. Below,
$\ell$ abbreviates the plain-object value $\mathsf{obj}(\ell,\mathsf{absent})$.
A function object carries closure code at the same kind of heap identity;
[callable contracts](PROGRAM-TYPING.md#callables) additionally constrain that code.

Because the calculus is nameless, a binding is really a de Bruijn position, and
the implementation calls it a **slot**: environments are lists, and pushing a
value renumbers everything already there. Rules in these documents write names
for bindings anyway, which reads better and matches the source they describe.
The two views agree, and `shift_holds` is the theorem that says so: renumbering
on a push preserves every fact. Positions surface again only where something
genuinely carries them — a certificate's binding transfer, and the wire format.

Assertions are attached to bindings, because bindings are what a checker can
name; locations arise only during execution and never appear in a program. So
$x\mapsto R$ is not a claim about $x$'s value but about the
location that value *is*: there exist $\ell$ and $v$ with $\rho(x)=\ell$,
$h(\ell)=v$ and $v\in R$. That one indirection is where aliasing enters, and it
is why the checked rules have
[no frame rule](PROGRAM-TYPING.md#the-reference-operations): two names can hold
the same location, and no assertion can say they do not.

Two of these forms are deliberately outside the typing judgment. A location
arises only at run time and takes its contract from the world, never from a
typing rule. A shape test is typed only in the guard of a conditional, by
`ifTag`; it has no standalone rule. The source fragment uses a singleton test
for a strict comparison with a singleton operand, the nullish test for `??` and
for `== null`, and strict equality $\equiv$ for any other strict comparison. Every test is total on values.

Substitution operates on closed substituted values. `Bindings.lean` supplies
scope and simultaneous closing substitution, including its beta law. The program
typing theorem uses semantic environments of closed values; its closed-program
interface explicitly checks scope.

## One meaning for callable contracts

The core equation is a behavioral promise, shared by fixed signatures, rest
signatures, overloads and callable objects. Let $R_c$ be the receiver family,
$\mathcal A$ describe the admitted lists of actual values and $R$ the result
family. Then

$$
f\in\mathcal F(R_c,\mathcal A,R)(n,W)\iff
\operatorname{Invocable}(f)\ \land\
\forall j<n,\ U\succeq W{\downarrow}j,\ h,r,\vec v.\;
\begin{aligned}
&\operatorname{WorldAdm}(U)\land\operatorname{HeapOk}(j,U,h)
 \land r\in R_c(j,U)\land\operatorname{Values}(\vec v)\land\mathcal A(j,U,\vec v)\\
&\quad\Longrightarrow\exists t.\;
 \operatorname{Invoke}(f,r,\vec v,t)\land\operatorname{Safe}(R,j,U,h,t).
\end{aligned}
$$

This is `Invocable` together with `Safety.Promise`. The receiver is not an
actual: it changes no arity, optional position or rest, and $\mathcal A$
never sees it. A plain call passes `undefined`; a method call, the object the
method was read from; `.call`, its first argument. A signature indifferent to
its receiver states top. Weakening is contravariant in $R_c$ as in each
domain: a function that ignores its receiver meets any receiver requirement,
and one that reads its receiver cannot be widened to accept arbitrary ones. `Invoke` dispatches the
saved code and yields a term; `Safe` describes its execution, including any
allocation, mutation or further call. The call spends a step before using
this lower-budget guarantee. Safety permits nontermination. Neither the
contract nor the equation requires a particular parameter-binding descriptor.

An imported interface method `m(P): R` is lowered to a writable `m` field
whose function contract is $\mathcal F(I,P,R)$, where $I$ is the containing
interface's recursive graph node. Thus a call through `value.m` passes the
required $I$ receiver; copying the function and calling it plainly passes
`undefined` and cannot use that promise. This uses the same field and call
rules as an explicitly function-valued property. It is a client contract
relative to the imported declaration, not a proof of the method's implementation.
It is stronger than TypeScript's structural method declaration: a method body
may depend on implementation-private state and fail when called with another
structurally matching receiver. A checked implementation or an explicit external
assumption must establish this promise before any imported runtime value is
claimed to inhabit the interface.

This supplies the call component of the existing
[callable-object equation](PROGRAM-TYPING.md#types-describe-behaviour-not-internal-storage):

$$
\mathsf{Callable}(L;P)=\mathsf{Fun}\cap\mathsf{Props}(P)
  \cap\bigcap_{\sigma\in L}\mathsf{CallSpec}(\sigma).
$$

Here `Invocable` supplies function shape, `propsT` supplies the field
requirements, and `Promise` supplies each call specification. The same value
must satisfy every conjunct; neither overloads nor generic instantiation
allocate a replacement function or choose a new storage contract.

All the callable uses build on this equation:

- A fixed signature uses `ArgsShort`: written actuals meet their corresponding
  domains, and each omitted trailing domain admits `undefined`. A rest
  signature uses `ArgsRest`: its fixed domains admit the first actuals as a
  fixed signature's do, and the actuals past them, as one argument list, are
  at its rest contract, a predicate on lists (`ArgFam`); an element rest
  admits any number at its element. `callsT` and `restsT` conjoin `Promise` over
  their respective signature lists.
- Overloads conjoin promises on **one value**. The `arrs L S` clause combines
  fixed and variadic promises; either list may be empty. Thus compatible
  fixed and variadic contracts overlap. Their syntax does not divide runtime
  functions into disjoint type shapes.
- A callable object's field contract is intersected with these same promises:
  `callable P Ps L S` means `propsT P Ps ∩ callsT L ∩ restsT S`.
  Reads and writes use the fixed world contracts of the fields; invocation
  uses the call promises on that same object. Returning, passing or capturing
  a callback simply uses this family as a result, domain or environment type.
- Quantification requires the same value, in the same world, to satisfy the
  promises at every admissible binder assignment. `TypeSchemes.schemeT`
  universally quantifies the conjunction of instantiated `callsT` and `restsT`;
  its shape condition is `Invocable`, even when no assignment satisfies the
  bounds. The executable universal certificate covers both fixed and rest
  descriptors. `T[]` denotes invariant array storage under the same assignment,
  and each invocation allocates its rest store with that contract.
- Contract weakening follows `Promise.weaken`: admit fewer argument lists
  and weaken the result. Fixed-to-variadic coverage is not generally valid
  from a fixed contract alone, since it promises nothing about longer lists.
  A concrete ordinary closure can nevertheless have stronger behavior.

The [typing rules](PROGRAM-TYPING.md#expressions) build creation and
application rules on this meaning. `InvocationSpec` and `RestCalls.RestSpec`
are code-specific introduction premises. `callsT_of_invocationSpec` and
`restsT_of_restSpec` turn them into the behavioral contracts above. The older
unary `arrowT`, `arrowsT` and fixed-code `codeCallsT` remain specialized
semantic lemmas for ordinary closure code; they are not the graph's definition
of all function values. `callsT_of_arrowsT` embeds that specialized guarantee.

## Argument-list preparation

Applications use `invoke f r args`: the callee, the receiver, the ordered
actuals. `call f args` abbreviates `invoke f undefined args`, and `app f a` the
singleton call; neither is a second form of call. Substitution, scope checking,
capture instantiation and object-name traversal visit the receiver, the entire
list and every code descriptor, including a `bound` descriptor's saved values.
`CallArguments.Frame` keeps the callee, the receiver and ordered arguments
separate from invocation.

`Prepare` evaluates the callee, then the receiver, then processes arguments from
left to right.
`Step.callArg` requires earlier arguments to be values. A `spread` is not a
value: `Step.callSpread` consumes its ready store before any later argument
can step, replacing holes with `undefined`. Splicing can change list length;
`ArgStep.length_preserved` applies to an individual operand reduction, not to
all preparation. `prepare_deterministic` and `call_step_iff` connect preparation
and invocation to the deterministic term machine. A ready frame has value
operands; readiness alone does not establish callability or typing.

Ordinary code uses `parameters n args` to pad missing positions with
`undefined` and discard extra positions after their effects have occurred.
`bindParameters` substitutes the receiver in slot 0 and these values after it,
without allocating. Variadic code uses
`bindRest`: fixed positions are padded in the same way, while `args.drop n`
becomes a fresh rest store. Padding never enters the rest store. Dispatch
itself leaves the heap unchanged; the yielded term allocates the store with
the ordinary store step, and the body wraps it into an array with the
prototype it captured, as an array literal is allocated. These operational distinctions
are independent of the contracts callers use.

A `bound` descriptor dispatches without binding anything: `Step.callBound`
turns `invoke (bound f r₀ p⃗) r a⃗` into `invoke f r₀ (p⃗ ++ a⃗)`, dropping the
receiver `r` it was given. `bound_ignores_receiver` states that the yielded term
is the same whatever `r` is, and `rebind_keeps_receiver` that binding a bound
function forwards to it, which forwards with the first saved receiver.
`callsT_bound` proves the residual contract: a target meeting
$(R_t, \vec P \mathbin{+\!\!+} \vec D, R)$ with a saved receiver in $R_t$ and a
saved prefix in $\vec P$ gives an object meeting $(R_c, \vec D, R)$ for any
$R_c$, and `restsT_bound` the same for a variadic target, whose residual keeps
its rest, when the rest admits the prefix's values past the fixed positions in
front of any pack it admits, as an element rest does. There is no forwarding wrapper closure: construction and
`new.target` are not modelled, and a bound function has no own fields.

`.apply` is a source lowering onto these steps, not a new preparation: it saves
the target, the receiver and the list, then reads the list's length and each
index in order with the ordinary store operations, then invokes the target with
those elements. It never iterates the list, so it shares the prepared actual
list with ordinary calls but not the spread's operation.

`callsT_invoke` obtains safe dispatch from a behavioral promise.
`ProgramTyping.call_safe` first evaluates the callee and composes effectful
arguments using `bind_list` and `FutureSafe`. `ArgsT_transfer` preserves saved
value types as the budget decreases and the world extends. Variadic calls
add `RestCalls.spread_parts_safe` and `call_elim_rest`; source lowering copies
a spread's elements at its evaluation point when later operands run code.
The copy preserves element values, including object references, rather than
merely saving the source array's identity.

`callsT_adm`, `restsT_adm` and the corresponding congruence lemmas establish
world monotonicity and guardedness of both domains and results. The
source/calculus correspondence remains the documented trusted-adapter
boundary; these theorems establish safety of the extracted program.

Worlds have different types at different budgets. Consequently, “the type is
just the intersection of its approximations” is not a complete standalone
account of membership. The proved subtype soundness theorem quantifies over
every budget, matching world, and value; no quotient of worlds or all-budget
observational equivalence is assumed.

## Computations and recursive types

`Safe A 0 W h e` imposes no obligation. At a positive budget, either `e` is a
value belonging to `A`, or it throws a closed value, or it can step with one
budget spent, preserving heap satisfaction in an admissible extension of the
truncated world. This is partial correctness/safety, not termination, and a
throw is an outcome, as a value is: a type says what a value is, never that
none is thrown ([Design](DESIGN.md#throws)).

**Throws.** `throw a` (`Tm.throw`) evaluates `a` (`throwC`), then throws its
value. A term *throws* $v$ (`Raises t v`) when `throw v`, $v$ a value, is in
evaluation position: under exactly the contexts the step relation evaluates
in, one constructor per congruence rule of `Step`:

$$
\frac{v\ \text{a value}}{\mathsf{throw}\ v\ \text{raises}\ v}
\qquad
\frac{t\ \text{raises}\ v}{E[t]\ \text{raises}\ v}
\qquad
E ::= [\,]\ a\mid f\,[\,]\mid\mathsf{let}([\,],b)\mid\mathsf{read}([\,])\mid v\mathbin{op}[\,]\mid\cdots
$$

A throwing term is not a value, does not step, and throws one value
(`raises_not_val`, `raises_no_step`, `Raises_det`), so evaluation stays
deterministic. No step propagates a throw: the context closure is the
predicate, and a handler, where there is one, catches it
([graphs](PROGRAM-TYPING.md#checked-control-flow-graphs)). The safety
predicate:

$$
\mathit{Safe}(A)(n{+}1,W,h,t)\iff
\bigl(t\in A(n{+}1,W)\ \lor\ \exists v\ \text{closed}.\ t\ \text{raises}\ v\bigr)\ \lor\
\exists W',h',t'.\ h,t\to h',t'\land\ldots\land\mathit{Safe}(A)(n,W',h',t')
$$

Every composition lemma takes, beside its context's step rule, the context's
throw rule (`bind`, `bind_list` with `ArgRaises`, `ctx_bind`,
`HeapObservations.bind`); `thrown_safe` makes a throwing term safe at every
type. `SafePost` is the same with no postcondition on a throw: the facts it
states describe the heap a value is produced in.

`SafeGraph` is the same predicate one level up, for the machine that runs a
control-flow graph rather than a single term. Its states are

$$s ::= \mathsf{at}(p,\rho)\mid\mathsf{eval}(t,\rho,k,x)\mid\mathsf{done}(v)\mid\mathsf{raised}(v),$$

where $p$ is a program point (a node label, not a location), $\rho$ an
environment of closed values, $k$ a
[continuation](PROGRAM-TYPING.md#checked-control-flow-graphs) and $x$ the
node's handler, if it has one. Entering a node
instantiates its term against $\rho$; the term then steps as usual; a value meets
the node's continuation, which either finishes the run or moves to the next label
with a transformed environment; a throw goes to the handler, the thrown value
bound, or without one ends the run in $\mathsf{raised}(v)$. `SafeGraph P T n W h s`
says that at a positive budget the state is $\mathsf{done}(v)$ with $v\in T$,
or $\mathsf{raised}(v)$ with $v$ closed, or it can take one
graph transition, spending a budget and preserving heap satisfaction in an
admissible future, and remain safe there. `Safe` is the special case with no
graph. Starting a graph means starting at $\mathsf{at}(p,\rho)$ for the entry
point and the input environment.

`CallableConjunctions.objectsT` combines invariant field requirements and
fixed call promises on one value. `PositiveNormalization.sem` intersects it
with `restsT` for the graph's `callable first rest arrows variadic` clause.
The plain `arrs arrows variadic` clause carries the same call promises without
field requirements. Normalization concatenates both kinds of signature and
retains invariant field operands. Checked creation establishes field storage
and code obligations separately; calls, reads and writes use the corresponding
part of the same object's contract. The common function equation above governs
all these call obligations.

A guarded operator consults recursive operands only below the current budget.
Its approximation tower stabilizes at every finite observation level, and the
diagonal is a fixed point. `Tower.lean` supplies that construction for graph
interpretations. It does not require monotonicity of the recursive operand, so
negative occurrences in function domains are permitted when guarded. This is
not a greatest-fixed-point construction on unindexed sets of values.

The type graph is a finite system of guarded positive formulas. Normalization
preserves the entire interpretation operator, hence also its recursive fixed
point. No cycle is unfolded during normalization. See the grammar and equations
in [POSITIVE-TYPES.md](POSITIVE-TYPES.md).

## Current-content assertions and postconditions

The [assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) defines the
notation and its separation from ordinary types. This section gives its meaning.

A world records a location's persistent storage contract, while a heap records
its current contents. Both a true heap and a false heap can satisfy the same
Boolean world. A point claim `{ value: B = R }` combines the invariant reference
with a current-content predicate:

$$
\operatorname{Obs}(h,\ell,R)
\equiv \exists v.\ h(\ell)=v \land R(v),
\qquad
\operatorname{ObservedRef}(B,R,n,W,h,\ell)
\equiv \operatorname{Ref}(B)(n,W,\ell)\land\operatorname{Obs}(h,\ell,R).
$$

`ObservedRef` in [HeapObservations.lean](lean/Verification/Model/Semantics/HeapObservations.lean)
is used with `HeapOk(n,W,h)`. For primitive predicates this requires the contents
to satisfy both the storage invariant and the observation. Consequently
`{ value: true = false }` is inconsistent in a satisfying heap at every positive
budget. The raw predicate without `HeapOk` does not enforce that connection;
the invariant check is vacuous at budget zero. Giving the conjunction meaning
does not require a syntactic subtype relation between `R` and `B`.

The right side of `=` is a predicate, not an initializer or a future-read promise.
Null/undefined/Boolean and numeric predicates are supported, including the
whole number family and exact numeric singletons. These assertions are duplicable facts, not exclusive write
permissions. This is a chosen plain-cell interpretation, not a theorem equating
SKJS's internal types with heap assertions.

### What is asserted, and what a heap change can touch

The finite assertion layer records three forms, and they divide on one question:
does the form mention the heap?

$$
\begin{aligned}
x=R&\equiv\rho(x)\in R,
  &&\text{a variable satisfies a primitive predicate}\\
x=y&\equiv\rho(x)=\rho(y),
  &&\text{two variables hold the same value}\\
x\mapsto R&\equiv
  \exists\ell\,v.\;\rho(x)=\ell\land h(\ell)=v\land v\in R,
  &&\text{the cell }x\text{ names satisfies }R\\
x\mapsto y&\equiv
  \exists\ell.\;\rho(x)=\ell\land h(\ell)=\rho(y),
  &&\text{that cell holds the value of }y
\end{aligned}
$$

Two relations, each taking a finite primitive-predicate disjunction or a variable on the right.
The [predicate vocabulary](POSITIVE-TYPES.md#state-assertion-grammar) includes
numeric singletons and the whole number family.
The $=$ atoms mention only $\rho$; the $\mapsto$ atoms mention $h$ as well, and
that is the only difference that matters. $x=R$ abbreviates membership in the
disjunction of predicates in $R$. For constant predicates this is a disjunction
of equalities; the numeric-family predicate also admits any numeric value.
Write $\Pi$ for a list of them. The last two mention $h$ as
well. Write $\Sigma$ for a list of those. Both are read as the conjunction of
their atoms and extended with a comma, exactly as $\Gamma$ is; neither carries
ownership or disjointness, and the atoms are duplicable, so there is no
separating conjunction to write.

That division is the whole state discipline. No write and no call can disturb
$\Pi$, because nothing in $\Pi$ speaks about the heap: two copied references remain
the same location after any write, and a constant a variable is equal to does not
change when a cell does. Everything in $\Sigma$ is a claim about the heap as it is
now, so a write to an unknown location or a call to an unknown function can
falsify any of it. Allocation is the exception that proves it: a fresh cell
cannot be one an existing fact names, so allocation preserves both. The
checked `allocated` rule applies to both plain and callable objects through
`make`, with a known initializer slot. Typed reads also use one proof for both
kinds of bag and retain their actual descriptor in the read links. Closure
bodies may mutate when called; allocating their code does not execute them.

`ValueHolds` and the alias branch of `HeapLinks.Holds` interpret $\Pi$;
`HeapFacts.Holds` and the read branch interpret $\Sigma$. The implementation stores
them as three lists — cell facts, value facts, and links carrying an `alias`
flag — so the links list straddles the division: the flag is what says which side
a link is on. [Program typing](PROGRAM-TYPING.md#the-reference-operations) states
the rules over $\Pi$ and $\Sigma$; the
[assertion grammar](POSITIVE-TYPES.md#state-assertion-grammar) owns the notation
for what a source claim may say.

`SafePost T Q n W h e` strengthens `Safe T n W h e`: at a positive-budget final
value it additionally requires `Q h e`; its step case uses exactly the same
operational step, truncated-world extension, admissibility and heap satisfaction.
At budget zero it is true. The `postcondition` theorem proves `Q` for an actual
terminating execution observed with one remaining level; divergence is permitted.
`erase` yields ordinary safety, and `forget` embeds ordinary safety with `Q = True`.

[HeapObservationTests.lean](lean/Verification/Model/Tests/HeapObservationTests.lean)
proves the important counterexamples. `observation_not_a_value_type` excludes
representing current contents by a heap-independent value family.
`observation_does_not_narrow_invariant` gives a Boolean cell currently true that
is not `Ref true`. `callback_counterexample` supplies an inhabited heap and an
ordinarily typed captured writer that destroys the true observation. Thus an
ordinary arrow cannot promise preservation of captured current contents.

[Program typing](PROGRAM-TYPING.md#current-content-rules-semantic-layer) specifies
the operation and composition rules using this predicate;
[Design](DESIGN.md#current-content-assertions) owns the graph-integration plan.

## What the checked development establishes

- `Rules.lean` gives the operational rules for functions, application, heap
  operations, shape testing and branching, including an application-context
  composition rule.
- `Examples.lean` checks negative recursive function types, closures surviving
  alias writes, and a composed program that allocates, mutates and reads back a
  changed boolean. It also rejects a stuck function.
- `ProgramTyping.lean` proves safety by induction on syntactic typing derivations.
  `ProgramTypingTests.lean` combines overload dispatch, captured state, an alias
  write and checked overload subsumption in one program.
- `ProgramCertificates.lean` checks finite program evidence and proves acceptance
  equivalent to closed-program derivability. The same example has executable
  evidence and obtains safety from its successful check.
- `PointClaims.lean` checks supplied environment claims against individual incoming
  edges, proves environment transfer, and composes checked computations through
  such claims.
- `ControlFlow.lean` enumerates every actual node and outgoing edge, handler
  edges included, then proves global safety, no stuck execution, typed returns
  and closed throws, including cyclic graphs. It reuses expression steps and
  adds explicit dispatch, transfer and handler steps.
- `PositiveNormalization.lean` and `PositiveGraphs.lean` prove finite and
  recursive normalization preservation.
- `PositiveRules.lean` defines declarative subtype rules and proves their
  semantic soundness.
- `PositiveCertificates.lean` proves checker soundness and certificate
  completeness for those rules, and transports accepted subtyping through
  normalization to computation subsumption.

The certificate theorem says **derivable iff some finite certificate is
accepted**. It does not assert completeness for every inclusion true in the
semantic model, automatic proof search, or that exported point invariants
already contain all necessary subtype evidence.

## Two retained design constraints

`ModelBoundaries.lean` preserves counterexamples that constrain future rules.

First, unrestricted arrow-result distribution fails:

```text
(A → B) & (A → C) ≤ A → (B & C)
```

An allocating function can satisfy the two arrows using different invariant
choices for a new cell. Requiring a single result-world interpretation is
stronger. The maintained combination rule uses a proved conservative shape
condition instead.

Second, eventual incompatibility of nested reference contracts cannot justify
collapsing their arrow results to bottom at every finite index. A concrete
cyclic heap and constant function witness the failure. This is a limitation of
that indexed semantic inclusion, not evidence of a program accepted unsafely.

These counterexamples are regression tests for the model's laws. They do not
require keeping separator searches or a second subtyping implementation.

## Remaining scope

The bounded source adapter and graph consumer are connected; their guarantees
are described in [Program typing](PROGRAM-TYPING.md) and the
[request protocol](REQUEST-PROTOCOL.md). This does not prove source-to-graph
correspondence. Source current-content claims are connected to graph checkpoints;
graph-backed closure bodies remain integration work. Type parameters, bounded polymorphism, and general
difference/negation require further syntax and sound rules; definability of
quantification over semantic families alone is not a generics result.
Rigid parameters, substitution on the identity and `Ref T` aliases (source
`type Id<T> = T` and `type Box<T> = { value: T }`), and the
identity function at every `T` are in
[TypeParams.lean](lean/Verification/Model/Types/TypeParams.lean).
Receivers follow the strict rule only: sloppy code's global-object substitution
and primitive boxing, `super` and home objects, construction and `new.target`,
and a bound function's reflective properties (`name`, `length`) are later
obligations, not approximated by the strict rule.
The intended path is the
[operation-level contracts, then a small first-order fragment](DESIGN.md#semantic-contracts-for-skjs-operations).
[Design](DESIGN.md#later-feature-gates) owns the feature roadmap and priorities.
