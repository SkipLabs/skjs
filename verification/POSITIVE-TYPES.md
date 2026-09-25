# Positive types

This document specifies the types the verifier uses: how a type graph is
written, what each type means, how conjunctions are normalized, which
subtyping rules hold, and how a subtyping certificate is checked. Lean proves
three things about them:

1. normalization preserves meaning;
2. every subtyping rule is sound;
3. the certificate checker accepts exactly the derivable inclusions.

The indexed model that gives the types their meaning is in
[SEMANTICS.md](SEMANTICS.md). How programs are typed with them is in
[PROGRAM-TYPING.md](PROGRAM-TYPING.md). [State assertions](#state-assertion-grammar),
which combine types with facts about the current heap, are a separate layer at
the end.

**Notation.** A meaning is a family $X_n(W,v)$: at level $n$ and world $W$,
value $v$ is a member. A lower level is a weaker observation; "below the
level" means at every $j<n$. Throughout, $\Delta$ is a finite table of subtype
obligations, and $\Delta(A,B)$ says the pair $(A,B)$ is in it. Each section
ends with a "Lean:" line naming the definitions and theorems behind it.

## Types and clauses

A graph maps **labels** to bodies. A label names a whole type, never part of
one, and every operand inside a body is itself a type. So the syntax has two
levels. A **type** is a finite union of labels:

$$A ::= \bot\mid i\mid A\lor A.$$

A **clause** constrains one value shape. A body is a positive formula over
clauses, and a **normal body** is a union of clauses:

$$
P ::= \bot\mid c\mid P\lor P\mid P\land P,
\qquad
N ::= \bot\mid c\mid N\lor N.
$$

The clauses, with what each denotes:

| Clause | Denotes |
| --- | --- |
| `top` | every closed value; membership grants no operation |
| `nul`, `undef` | exactly null; exactly undefined |
| `bool`, `boolLit b` | true or false; exactly $b$ |
| `num`, `numLit x` | any number; exactly the number with bit pattern $x$ |
| `str`, `strLit s` | any string; exactly $s$ |
| `bigint`, `symbol` | any bigint; any symbol (opaque identities) |
| `refs` | a plain object under record contracts, readonly views, optional fields and methods ([Records](#records)) |
| `dict` | a `refs` object whose present string keys also meet readonly index contracts |
| `list` | an array under one or more tuple contracts ([Arrays](#arrays)) |
| `arrs` | a function meeting fixed and variadic call signatures ([Functions and classes](#functions-and-classes)) |
| `callable` | a function that is also an object with record contracts |
| `ctors` | a class meeting construct signatures |
| `pack` | no value: a family of argument lists ([Argument packs](#argument-packs)) |

The **shape** of a clause is the kind of value it admits: null, boolean,
plain object (`refs`, `dict`), function (`arrs`, `callable`), undefined,
number, string, array, bigint, symbol, class or argument list. A value has
exactly one shape, and `top` has none.

Singletons sit below their primitive: $\mathsf{boolLit}\,b\le\mathsf{bool}$,
$\mathsf{numLit}\,x\le\mathsf{num}$, $\mathsf{strLit}\,s\le\mathsf{str}$.

Lean: `Clause`, `semWithArgs`, `shape`, `valueShape`
(`Types/PositiveNormalization.lean`).

### Records

A record operand maps **property keys** to types. A key is a string or a
symbol, and the two spaces are disjoint:

$$
\kappa ::= \mathsf{str}(s)\mid\mathsf{sym}(n),\qquad
\varphi ::= \overline{\kappa{:}A}.
$$

A `refs` clause
$\mathsf{Ref}(\varphi_0\land\cdots\land\varphi_m;\,\psi;\,\omega;\,\mu;\,\beta)$ carries
invariant operands $\varphi_i$, readonly views $\psi$, optional fields
$\omega$, methods $\mu$ and own-key bounds $\beta$. Write $\ell$ for the object
$\mathsf{obj}(\mathit{flds},\mathsf{absent})$ and $c_j\equiv T_j$ for "the
location's contract and $T$ agree below the level". Then

$$
\begin{aligned}
\llbracket\mathsf{Ref}(\vec\varphi;\psi;\omega;\mu;\beta)\rrbracket_n(W,v)
&\iff \textstyle\bigwedge_i\mathsf{rec}(\varphi_i)\land
      \mathsf{view}(\psi)\land\mathsf{opt}(\omega)\land\mathsf{meth}(\mu)\land
      \bigwedge_{K\in\beta}\mathsf{own}(K),\\
\mathsf{own}(K)_n(W,v)&\iff v=\ell\land\forall\kappa\in\mathrm{dom}(\mathit{flds}).\;\kappa\in K,\\
\mathsf{rec}(\overline{\kappa{:}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}T).\;\exists l,c.\;
      \mathit{flds}(\kappa)=l\land W(l)=c\land c_j\equiv T_j,\\
\mathsf{view}(\overline{\kappa{:}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}T).\;\exists l,c.\;
      \mathit{flds}(\kappa)=l\land W(l)=c\land c_j\subseteq T_j,\\
\mathsf{opt}(\overline{\kappa{:}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}T).\;
      (\mathit{flds}(\kappa)=\varnothing\Rightarrow\mathit{flds}(\mathsf{proto})=\varnothing)\\
&\qquad\land\forall l.\;\mathit{flds}(\kappa)=l\Rightarrow\exists c.\;W(l)=c\land c_j\equiv T_j.
\end{aligned}
$$

- **Invariant fields.** Every operand constrains the **same object**. Operands
  naming one key constrain one location, whose single stored contract agrees
  with each of them. They are not several cells, and they are not replaced by
  one contract at the intersection of their types. A plain reference cell is
  $\mathsf{Ref}\,\{\mathsf{value}{:}A\}$.
- **Views** only read: the location's contract implies the view's type, so a
  view grants no write.
- **Optional fields** constrain a key only where the object has it. A read
  gives $T$ or undefined, so an object lacking an optional key has no
  prototype, whose members the read would otherwise reach. No rule writes one,
  since an object's keys are fixed at allocation.
- **Methods** are host-relative members: read from the object and invoked on
  it, they behave as typed
  ([DESIGN.md](DESIGN.md#method-members-are-host-relative)). A member $m$ has
  fixed signatures $(\vec P\to B)$ and variadic ones $(\vec P,\ldots Q)\to B$,
  none with a receiver. With $\mathsf{on}_v(m)$ the member's signatures, each
  with $v$ as the one receiver it admits,

  $$
  \mathsf{meth}(\mu)_n(W,v)\iff\forall m\in\mu.\;\exists l,c.\;
    v=\ell\land\mathit{flds}(m.\mathsf{key})=l\land W(l)=c\land
    \forall j<n,\ U\sqsupseteq W|_j,\ u.\;c_j(U,u)\Rightarrow u\in\mathsf{on}_v(m)_j(U).
  $$

  The implication is claimed only in worlds extending the current one: in an
  unrelated world the object's locations need not hold their contracts, and no
  method reading them could be safe.

- **Own-key bounds** say which keys the object may have. Records are open, so
  only a bound says a key is absent, and so that a read of it continues at
  the prototype. An array bounds its own keys to its store and its prototype,
  which it holds as a readonly view under the reserved key. Keys are fixed at
  allocation, so a bound holds in every world.

A `dict` clause adds readonly **index contracts** $\overline{D}$: the object
has no prototype, and every present field under a string key, named or not,
has a contract implying each $D$. The object may lack a key, so an arbitrary
indexed read has type $D\mid\mathsf{undefined}$. Index contracts are guarded through the world, so a
recursive graph can contain `JsonObject = { readonly [key: string]: Json | null }`.

Lean: `refsT`, `viewT`, `optT`, `dictViewT`, `ownKeysT` (`Types/Types.lean`), `methodT`,
`onHost` (`Types/MethodMembers.lean`). The heap facts behind invariant
operands (`adm`, `congr_below`, `operands_agree`, `read_all`, `write_first`,
`cyclic_inhabited`) are in `Types/ReferenceConjunctions.lean`: a read meets
every operand, and writing a value at the first operand preserves every
alias's contract.

### Arrays

An array is a value $\mathsf{arr}(\vec l)$ over a list of element locations.
A `list` clause holds one or more **tuple contracts** $\tau$, each with
required positions $\vec R$, optional positions $\vec O$, an optional rest
$E$, and a readonly flag. An array meets a contract when its length is within
the contract's bounds and each present element's location has a contract that
agrees with the position's type, or, for a readonly contract, implies it.
Every contract of the clause constrains the same array.

Lean: `listT`, `SlotContract` (`Types/Types.lean`).

### Functions and classes

A call signature is $(Q;\vec P)\to B$: a receiver $Q$, parameters $\vec P$ and
result $B$. It describes the calls a caller may write: invoked with a receiver
in $Q$ and actuals in $\vec P$ at every future world and satisfying heap below
the level, the function is safe at $B$. A call may pass fewer actuals when
the missing parameters admit undefined. A signature indifferent to its receiver has receiver `top`. A
variadic signature $(Q;\vec P,\ldots P')\to B$ takes the actuals past $\vec P$
as one [argument pack](#argument-packs) at $P'$.

- `arrs L S` is a function meeting every fixed signature in $L$ and every
  variadic one in $S$. With both lists empty it is any function with closed
  invocation code.
- `callable φ⃗ L S` is additionally a plain object under the invariant record
  operands $\vec\varphi$. It has no views, optional fields or methods.
- `ctors L S` is a class, whose code is construct-only. A construct signature
  $\vec A\Rightarrow B$ says that `new` with actuals in $\vec A$ steps to a
  term safe at $B$ one level below; a variadic one takes a pack as its rest.

$$
\llbracket\mathsf{Ctors}\,\overline{(\vec A,B)}\rrbracket_k(W,v)
\iff\mathsf{Constructible}(v)\land\forall(\vec A,B),\,j<k,\,
   U\sqsupseteq W|_j,\,\mathit{heap}\models_j U,\,\vec a\in\vec A.\;
\exists t.\;\mathsf{new}\,v(\vec a)\to t\land t\in\mathsf{Safe}_j(B)(U,\mathit{heap}).
$$

No class is callable and no function is constructible, so `ctors` meets
neither `arrs` nor `callable`.

Lean: `callsT`, `restsT` (`Semantics/Safety.lean`), `objectsT`
(`Types/CallableConjunctions.lean`), `ctorsT`, `ctorRestsT`, `ConstructsTo`.

### Argument packs

An **argument pack** type states which argument lists a rest parameter
admits. An argument list is not a runtime value: a `pack` clause has no value
members, and its meaning is a family of lists. It holds tuple contracts
$\tau_0,\ldots,\tau_m$ as `list` does, and $\mathsf{pos}_\tau(i)$ is the type
the contract states for index $i$: $R_i$, then $O_{i-|\vec R|}$, then $E$ past
both, if any. A list fits a contract when its length is within the bounds and
each value is, **at the current level**, a member at its position:

$$
\begin{aligned}
\llbracket\mathsf{Pack}(\tau_0\land\cdots\land\tau_m)\rrbracket^{\mathsf{args}}_k(W,\vec v)
&\iff\textstyle\bigwedge_i\mathsf{fits}(\tau_i)_k(W,\vec v),\\
\mathsf{fits}(\tau)_k(W,\vec v)&\iff|\vec R|\le|\vec v|\ \land\
   (E=\varnothing\Rightarrow|\vec v|\le|\vec R|+|\vec O|)
   \land\ \forall i.\;\mathsf{pos}_\tau(i)=A\Rightarrow v_i\in A_k(W).
\end{aligned}
$$

Grouping evaluated arguments is not an execution step, so membership is at the
level of the actuals. The call or constructor whose rest it is supplies the
guard, and allocating the rest array consumes a level. A type's argument lists
are those of its pack clauses, or a pack parameter's assigned list family
([Parameter and scheme rows](#parameter-and-scheme-rows)).

Lean: `clauseArguments`, `Tuple.position`, `ArgumentContracts.Fits`,
`graphArguments`.

## Parameter and scheme rows

A label is one of three kinds of **row**:

- a **clause row** means the union of its clauses;
- a **parameter row** means what the graph's assignment `env` gives it. The
  assignment is a mixed family over values and argument lists; a row's kind
  selects the component: values for a value binder, lists for a pack binder;
- a **scheme row** $(\vec p;\Sigma;\beta;\Sigma_\ldots)$ means one function
  meeting its signatures at every reassignment of its binders $\vec p$, which
  are parameter rows, within their bounds $\beta$.

With $\eta$ an assignment and
$\llbracket A\rrbracket^\eta=\bigcup_{i\in A}\llbracket i\rrbracket^\eta$, the
denotation is the guarded fixed point of

$$
\llbracket i\rrbracket^\eta=
\begin{cases}
\eta(i) & i\ \text{a parameter row},\\[2pt]
\bigl\{\,v\;\bigm|\;\mathsf{Invocable}(v)\land\forall\vec X.\;
  \mathsf{Bounded}_n(\vec X)\Rightarrow
  v\in\mathsf{Calls}(\Sigma^{\eta'})\cap\mathsf{Rests}(\Sigma_\ldots^{\eta'}),\
  \eta'=\eta[\vec p\mapsto\vec X]\,\bigr\}
  & i\ \text{a scheme row},\\[2pt]
\textstyle\bigcup_{c\in G(i)}\llbracket c\rrbracket^\eta & i\ \text{a clause row},
\end{cases}
$$

where $\Sigma^{\eta'}$ reads each signature's types at $\eta'$. $\vec X$
ranges over admissible mixed families, one per binder, and
$\mathsf{Bounded}_n(\vec X)$ says each bounded binder's family is below its
bound, in both components, at every level under $n$, the bound read at the
scheme's own $\eta$. A variadic signature's rest may be a binder: a **pack
parameter**, instantiated at a pack type and bounded by one.

Reading bounds below $n$ keeps the fixed point contractive; the
approximations are non-expansive in the assignment (`QInv`), which gives
admissibility. The type meanings are read at the graph's assignment:
$\llbracket A\rrbracket_G=\llbracket A\rrbracket^{G.\mathit{env}}$ for values
(`meaning`) and its list component for argument lists (`argMeaning`). No check
reads `env`, so every theorem proved for all graphs holds at every
reassignment. A member of a scheme row meets each instance's signatures
(`scheme_elim`), and a function meeting them at every instantiation is a
member (`scheme_intro`). Without scheme rows and pack binders this is the
parametric semantics `denoteP` (`qDenote_no_schemes`).

Only clause rows have clauses. A type holding a parameter or scheme row has no
expansion, so no rule that reads a clause (`Represents`, `Answers`, the atoms
of heap knowledge) applies to it.

Lean: `qDenoteWithArgs G (mixedParameters G)`, `Bounded`, `instanceTWithArgs`,
`instanceRestsWithArgs` (`Types/PositiveGraphs.lean`,
`Types/QuantifiedGraphs.lean`); `mixedValues`, `mixedArgs`, `meaning`,
`argMeaning` (`Types/PositiveRules.lean`).

## Conjunction and normalization

Normalization rewrites a body into a normal body. It is disjunctive normal
form: it pushes $\land$ down through $\lor$ until every conjunction joins two
clauses,

$$
\begin{aligned}
\operatorname{nf}(\bot)&=\bot,&\operatorname{nf}(c)&=c,\\
\operatorname{nf}(P\lor Q)&=\operatorname{nf}(P)\lor\operatorname{nf}(Q),\\
\operatorname{nf}(P\land Q)&=\textstyle\bigvee\{\,c\land d\;\mid\;
   c\ \text{a clause of}\ \operatorname{nf}(P),\
   d\ \text{a clause of}\ \operatorname{nf}(Q)\,\}.
\end{aligned}
$$

So everything reduces to the conjunction of two clauses:

- `top` is the unit: $\mathsf{top}\land c=c$.
- Clauses of **different shapes** meet as $\bot$: no value has two shapes.
- **Primitives** follow their lattice: $c\land c=c$, a singleton meets its
  primitive as the singleton, and two different singletons meet as $\bot$.
- **Structured clauses of one shape concatenate their operands.** No
  computation is needed, since the result is again a clause:

$$
\begin{aligned}
\mathsf{Ref}(\vec\varphi;\psi;\omega;\mu;\beta)\land\mathsf{Ref}(\vec\varphi';\psi';\omega';\mu';\beta')
 &=\mathsf{Ref}(\vec\varphi\,\vec\varphi';\psi\psi';\omega\omega';\mu\mu';\beta\beta'),\\
\mathsf{arrs}(L;S)\land\mathsf{arrs}(M;T)&=\mathsf{arrs}(LM;ST),\qquad
\mathsf{Ctors}\,L\land\mathsf{Ctors}\,M=\mathsf{Ctors}\,(LM),\\
\mathsf{List}\,\vec\tau\land\mathsf{List}\,\vec\tau'&=\mathsf{List}\,(\vec\tau\,\vec\tau'),\qquad
\mathsf{Pack}\,\vec\tau\land\mathsf{Pack}\,\vec\tau'=\mathsf{Pack}\,(\vec\tau\,\vec\tau').
\end{aligned}
$$

  `refs` with `dict` gives a `dict` holding both; two `dict` clauses also
  concatenate their index contracts. `callable` with `callable` concatenates
  record operands and signatures; `callable` with `arrs` adds the signatures
  and keeps the record operands.

Nothing is distributed through an operand or a result. This is structural, not
a choice: an operand is a type, already normal, so there is no formula below
to normalize. That is also why guardedness survives untouched. For example,

$$
\mathsf{Ref}\,A\land(\mathsf{Ref}\,B\lor\mathsf{nul})
\quad\longmapsto\quad\mathsf{Ref}\,A\land\mathsf{Ref}\,B.
$$

Incompatible invariant contracts are kept, not replaced by $\bot$.
$\mathsf{Ref}\,\mathsf{nul}\land\mathsf{Ref}\,\mathsf{bool}$ has a member at
level zero, though none above; a nested analogue has a member at level one in
a satisfying cyclic heap. Both are checked examples, so rewriting such clauses
to $\bot$ would be unsound.

Lean: `meet`, `meetLists`, `normalize`, `normalize_sound`
(`Types/PositiveNormalization.lean`).

### Recursive normalization

A formula graph is normalized label by label, $\operatorname{nf}(G)(i)=\operatorname{nf}(G(i))$.
Labels occur only inside operands, so recursion stays guarded, nothing is
unfolded and no label is allocated. A finite graph stays finite, although DNF
can grow a body exponentially; no growth control is implemented.
`normalize_sound` proves the normal form means exactly the formula, for every
value and argument-list interpretation of the operands, level, world and
value.

Nothing in the current pipeline invokes the normalizer. The
[request grammar](REQUEST-PROTOCOL.md#request-fields) has no conjunction above
the clause level, so every graph reaching the consumer is normal by
construction. A formula graph is checked through its normalization
(`checkSource`).

## Subtyping

Subtyping is proved in three layers: **clause coverage** relates one source
clause to one target clause under a table $\Delta$; a **core** judgment checks
a whole table at once, which handles recursion; the **structural** rules add
union inclusion, transitivity and the scheme rules.

### Clause coverage

$\Delta;S\vdash c\sqsubseteq d$ says clause $c$ of source type $S$ is covered
by target clause $d$. Every clause is covered by `top`; identical primitives,
and a singleton by its primitive, are covered trivially; different shapes are
never covered. `refs` covers only `refs`, and `dict` only `dict`. Write
$\Delta^{\pm}(A,B)$ for $\Delta(A,B)\land\Delta(B,A)$.

**Records.** With $\Phi=\varphi_0\cdots\varphi_m$ the source's invariant
operands, each target component is found in the source:

$$
\frac{\begin{array}{c}
\forall j,\,(\kappa{:}B)\in\varphi'_j.\;\exists(\kappa{:}A)\in\Phi.\;\Delta^{\pm}(A,B)\qquad
\forall(\kappa{:}B)\in\psi'.\;\exists(\kappa{:}A)\in\Phi\,\psi.\;\Delta(A,B)\\
\forall(\kappa{:}B)\in\omega'.\;\exists(\kappa{:}A)\in\Phi\,\omega.\;\Delta^{\pm}(A,B)\qquad
\Delta;S\vdash(\Phi\,\psi;\mu)\sqsubseteq_{\mathsf{meth}}\mu'\qquad
\forall K'\in\beta'.\;\exists K\in\beta.\;K\subseteq K'
\end{array}}
{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi'_0\cdots\varphi'_k;\psi';\omega';\mu';\beta')}
$$

An invariant field needs an equivalent invariant field. A view is met by any
field whose type is within it. An optional field is met by a required or
optional field of the same key with an equivalent type; a required field is
never met by a view or an optional field, since neither says the key is
present. Fields the target does not name are not compared: records are open.
A bounded target needs a source bound within it (`CoversBounds`). A `dict`
target also needs each index contract within some source index contract.

**Methods.** A target method $m$ is covered by a source method of the same
key, or by a function the source holds under that key whose receiver the
source type $S$ is within:

$$
\frac{m'\in\mu\quad m'.\mathsf{key}=m.\mathsf{key}\quad
      \forall(\vec Q\to D)\in m.\;\exists(\vec P\to B)\in m'.\;\Delta(\vec Q,\vec P)\land\Delta(B,D)}
     {\Delta;S\vdash(\Phi\,\psi;\mu)\sqsubseteq_{\mathsf{meth}}m}
$$

$$
\frac{(m.\mathsf{key}{:}F)\in\Phi\,\psi\quad F\equiv\mathsf{arrs}(L;\ldots)\quad
      \forall(\vec Q\to D)\in m.\;\exists(Q_0;\vec P)\to B\in L.\;
      \Delta(S,Q_0)\land\Delta(\vec Q,\vec P)\land\Delta(B,D)}
     {\Delta;S\vdash(\Phi\,\psi;\mu)\sqsubseteq_{\mathsf{meth}}m}
$$

Here $\Delta(\vec Q,\vec P)$ pairs the lists position by position and needs
equal lengths (`Domains`). Receivers of two members are not compared: both
are the host. Variadic member signatures are covered likewise, the target's
extra fixed parameters taken into the source's rest.

**Arrays and packs.** A `list` target contract is covered by a source
contract with as many required and optional positions, each position within
the target's, and equivalent to it when the target is writable; a writable
target needs a writable source, so no location is retyped. Mutable arrays are
therefore invariant.

A pack contract $\tau$ is covered by $\tau'$ when $\tau'$ admits every list
$\tau$ admits: the target requires no more positions; a target without a rest bounds the source's length;
and each source position's type is within the target's, covariantly, since a
pack holds values, not locations. Past both contracts' fixed positions every
index reads the rests, so the positions up to
$N=\max(|\vec R|+|\vec O|,\,|\vec R'|+|\vec O'|)$ decide all:

$$
\frac{\begin{array}{c}
|\vec R'|\le|\vec R|\qquad
E'=\varnothing\Rightarrow E=\varnothing\land|\vec R|+|\vec O|\le|\vec R'|+|\vec O'|\\
\forall i\le N.\;\mathsf{pos}_\tau(i)=A\Rightarrow\exists B.\;\mathsf{pos}_{\tau'}(i)=B\land\Delta(A,B)
\end{array}}
{\Delta\vdash\tau\sqsubseteq_{\mathsf{pack}}\tau'}
\qquad
\frac{\forall\tau'\in\vec\tau'.\;\exists\tau\in\vec\tau.\;\Delta\vdash\tau\sqsubseteq_{\mathsf{pack}}\tau'}
     {\Delta\vdash\mathsf{Pack}\,\vec\tau\sqsubseteq\mathsf{Pack}\,\vec\tau'}
$$

So `[number, string]` is within `(number | string)[]` and `[number]` within
`[number, string?]`, while `number[]` is within no bounded tuple.

Lean: `CoversFields`, `CoversViews`, `CoversOptional`, `CoversMethods`, `CoversBounds`,
`CoversSig`, `CoversByFunction`, `CoversTuple`, `CoversPack`,
`covers_arguments_sound`.

### Function and class coverage

`arrs` is covered by `arrs`, and `callable` by `arrs` (forgetting its record
operands) or by `callable` (covering the operands as invariant fields). The
reverse, from `arrs` to `callable`, needs evidence of the record operands and
has no rule.

Each target fixed signature $(Q;\vec C)\to D$ must be **derived** from the
source's signatures $L$ and variadic signatures $S$ by the judgment
$\Delta;L,S\vdash(Q;\vec C)\Rightarrow D$:

$$
\frac{(Q_0;\vec A)\to B\in L\quad\Delta(Q,Q_0)\quad\Delta(\vec C,\vec A)\quad
      (B=\bot\lor\Delta(B,D))}
     {\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsc{source}
\qquad
\frac{s\in S\ \text{takes}\ (Q;\vec C)\ \text{into its rest, result within}\ D}
     {\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsc{rest}
$$

$$
\frac{}{\Delta;L,S\vdash(\bot;\vec C)\Rightarrow D}\ \textsc{emptyRecv}
\qquad
\frac{\bot\in\vec C}{\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsc{empty}
$$

$$
\frac{\Delta;L,S\vdash(Q;\vec C\,A\,\vec C')\Rightarrow D\quad
      \Delta;L,S\vdash(Q;\vec C\,A'\,\vec C')\Rightarrow D}
     {\Delta;L,S\vdash(Q;\vec C\,(A\lor A')\,\vec C')\Rightarrow D}\ \textsc{union}
\qquad
\frac{\Delta;L,S\vdash(Q;\vec C)\Rightarrow D\quad\Delta;L,S\vdash(Q';\vec C)\Rightarrow D}
     {\Delta;L,S\vdash(Q\lor Q';\vec C)\Rightarrow D}\ \textsc{recvUnion}
$$

$$
\frac{\Delta;L,S\vdash(Q;\vec C)\Rightarrow B\quad\Delta;L,S\vdash(Q;\vec C)\Rightarrow B'\quad
      \forall i\in B,k\in B'.\;\mathsf{compatible}_G(i,k)\Rightarrow\Delta(\{i\},D)}
     {\Delta;L,S\vdash(Q;\vec C)\Rightarrow D}\ \textsc{combine}
$$

`union` splits one parameter's union, `recvUnion` the receiver's. `combine`
uses two source signatures at once: the call's result meets both results, so
it is in some label $i$ of $B$ and some label $k$ of $B'$ that can share a
value. $\mathsf{compatible}_G(i,k)$ holds when some clause of $i$ and some
clause of $k$ have the same shape, or either has `top` or is not a clause
row. It is sufficient, not an exact test of joint inhabitation, and repeated
combination can use any number of source signatures.

Each target variadic signature is covered by a source variadic signature with
a receiver at least as wide, fixed parameters at least as wide (the target's
extra ones taken into the source's rest), a rest at least as wide and a result
at most as wide; or by a fixed source signature when the target's rest is one
**exact tuple** $\mathsf{Pack}(\vec E)$, with no optional position and no
rest. An exact tuple holds its actuals at their positions at the current
level, so they are at the fixed signature's parameters whatever the
positions' types:

$$
\frac{Q'=\mathsf{Pack}(\vec E)\ \text{exact}\quad\Delta(Q,Q_0)\quad
      \Delta(\vec C\vec E,\vec A)\quad\Delta(B,D)}
     {\Delta\vdash(Q_0;\vec A)\to B\ \sqsubseteq\ (Q;\vec C,\ldots Q')\to D}
$$

**Classes.** A construct signature $\vec C\Rightarrow D$ is covered by a
source one $\vec A\Rightarrow B$ with $\Delta(\vec C,\vec A)$ and
$\Delta(B,D)$. A variadic one is covered by a variadic source one with as many fixed
parameters, each at least as wide, a rest at least as wide and a result at most as
wide, or, when its rest is an exact tuple, by a fixed one as above. So a class
taking a number meets `new (...params: [number]) => M`.

Lean: `CallArrow`, `CallArrow.sound`, `Domains`, `RestFixed`, `RestCovers`,
`FixedCallsPack`, `FixedCoversPack`, `mixed_pack_exact`, `fits_exact`,
`compatible`.

### Core tables

A core judgment $G\vdash_c S\le T$ needs a finite table $\Delta$ containing
$(S,T)$ in which every entry $(A,B)$ satisfies three conditions:

1. **Same kind.** $A$ and $B$ are both value types or both argument-list
   types. A pack clause has argument kind, every other clause and every scheme
   has value kind, a parameter keeps its declared kind, and the empty type has
   either. So value `top` cannot discharge a pack edge, even though a pack's
   value meaning is empty.
2. **Opaque rows.** Every parameter or scheme row of $A$ appears in $B$, or
   $B$ holds `top`.
3. **Coverage.** Every split part of every clause of $A$ is covered by some
   clause of $B$, with $A$ as the source type.

$$
\frac{(S,T)\in\Delta\qquad
      \forall(A,B)\in\Delta.\;
      \mathsf{SameKind}(A,B)\land\mathsf{Opaque}(A,B)
      \land\forall a\in\mathsf{split}(\mathsf{cl}_G(A)).\;\exists b\in\mathsf{cl}_G(B).\;
      \Delta;A\vdash a\sqsubseteq b}
     {G\vdash_c S\le T}
$$

Here $\mathsf{cl}_G(A)$ lists the clauses of $A$'s clause rows.
**Splitting** replaces a `bool` clause by `boolLit true` and `boolLit false`
and leaves every other clause alone. It preserves meaning, so it adds no power
beyond the model; it lets one source clause be discharged by several target
clauses while coverage stays clause to clause. So
$\mathsf{bool}\le\mathsf{true}\lor\mathsf{false}$ and
$\mathsf{bool}\le\mathsf{bool}$ are derivable, and
$\mathsf{bool}\le\mathsf{true}$ is not.

Every cyclic premise occurs under an operand, so the table is sound by
induction on the level; the induction also supplies the source-type premise a
method covered by a function needs.

Lean: `Core`, `Valid`, `SameKind`, `Opaque`, `splitClause`,
`splitClause_sem`, `source_sem`, `Core.mixed_sound`.

### Structural rules

`Sub` closes the core judgment under union inclusion and transitivity:

$$
\frac{G\vdash_c S\le T}{G\vdash S\le T}
\qquad
\frac{\forall i\in S.\ i\in T}{G\vdash S\le T}
\qquad
\frac{G\vdash S\le U\quad G\vdash U\le T}{G\vdash S\le T}.
$$

Reflexivity and invariance under reordering or duplicating union labels
follow (`Sub.refl`, `Sub.congr`). Transitivity composes completed proofs, not
unchecked back-references in a table.

Three more rules read scheme rows. They turn on which **parameter rows a row
depends on**. A free-variable certificate $V$ on a domain $D$ assigns each
$i\in D$ a set $V(i)$ of parameter rows, with $D$ closed under what its rows
read (a clause row its operands, a scheme row its signature types), such that

$$
i\ \text{a parameter row}\Rightarrow i\in V(i),\qquad
l\in\mathsf{reads}_G(i)\Rightarrow V(l)\subseteq V(i)\cup\mathsf{binders}(i),
$$

where $\mathsf{binders}(i)$ is empty unless $i$ is a scheme row, so a scheme's
own binders are not free in it. A row means the same at two assignments that
agree on $V(i)$.

Lean: `FreeOk`, `agree_freeWith`, `mixed_respectsFree`.

#### Instances of a scheme row

An instance is checked by a finite **instance table** of entries
$(i,\kappa,T)$: under the context $\kappa$, row $i$ means type $T$. A context
maps the binders in scope to what they stand for: an instance type, or, under
a scheme mapped to another, that scheme's binder. Binder rows are shared
between scopes (a generic method of a generic type reuses a few binder rows so
that the graph stays finite), and the context tells the scopes apart. Writing
$\kappa(A)$ for the image of a type, each entry is one of:

- $i$ a parameter row and $T=\kappa(i)$, or $T=\{i\}$ when $\kappa$ does not
  name $i$, with $T$ of $i$'s declared kind;
- **rigid**: $T=\{i\}$ and $\kappa$ names no row of $V(i)$;
- $i$ a clause row, $T=\{j\}$, $j$ a clause row, and $G(j)=G(i)[\kappa]$;
- $i$ the scheme row $(\vec q;\Sigma';\beta';\Sigma'_\ldots)$, $T=\{j\}$, $j$
  the scheme row $(\vec r;\Sigma'[\kappa'];\beta'[\kappa];\Sigma'_\ldots[\kappa'])$
  with $|\vec r|=|\vec q|$, $\vec r$ distinct parameter rows of matching kinds
  and $\kappa'=\kappa[\vec q\mapsto\vec r]$, provided no free row of $i$
  outside $\kappa$'s domain, and no row free in an image $\kappa(p)$ for
  $p\in V(i)$, is in $\vec r$ (no capture).

The table is checked when its rows lie in a domain with a free-variable
certificate and every entry is one of these. Then, for every entry and every
pair of assignments related by its context on its row's free rows, the row on
the left means $T$ on the right, in both components. With
$\kappa_0=\vec p\mapsto\vec\theta$ for a scheme's binders and instance types,
the instance assignment and the graph's are related by $\kappa_0$ by
construction:

$$
\frac{\begin{array}{c}
i\ \text{a scheme row}\ (\vec p;\Sigma;\beta;\Sigma_\ldots)\quad
|\vec\theta|=|\vec p|\quad
\forall p.\;\theta_p:\mathsf{kind}(p)\quad
\forall(p,B)\in\beta.\;\theta_p\subseteq B\lor G\vdash_c\theta_p\le B\\
\text{a checked table}\quad
T\equiv_G\mathsf{arrs}(L;M)\quad
\forall\tau\in L.\;\exists\sigma\in\Sigma.\;\tau=\sigma[\kappa_0]\quad
\forall\tau\in M.\;\exists\sigma\in\Sigma_\ldots.\;\tau=\sigma[\kappa_0]
\end{array}}
     {G\vdash\{i\}\le T}\ \textsc{inst}
$$

The same tables relate two lowerings of one type that differ only in which
binder rows their schemes use, as a producer's copy of `Promise<number>` and
the annotation's may. With the empty context each row means its image:

$$
\frac{\text{a checked table}\quad
      \forall l\in S.\;(l,\emptyset,U_l)\ \text{its entry for}\ l\ \land\ U_l\subseteq T}
     {G\vdash S\le T}\ \textsc{table}
$$

A type below a scheme's signatures with the binders opaque is below the
scheme, provided none of its free parameter rows is a binder:

$$
\frac{j\ \text{a scheme row}\ (\vec p;\Sigma;\beta;\Sigma_\ldots)\quad
      U\equiv_G\mathsf{arrs}(\Sigma;\Sigma_\ldots)\quad
      \forall l\in S.\;l\in D\land V(l)\cap\vec p=\emptyset\quad
      G\vdash S\le U}
     {G\vdash S\le\{j\}}\ \textsc{gen}
$$

`gen` is sound because $S$ means the same at any two assignments that differ
only on $\vec p$, and every rule of `Sub` holds at every assignment: the
premise $G\vdash S\le U$, derived once, holds at each instantiation.

Lean: `entryOk`, `TableOk`, `instKinds`, `substitutionKind`,
`mixed_assignment_substitution`, `table_row_mixed`, `Sub.inst`, `Sub.table`,
`Sub.gen`, `Sub.mixed_sound`, `Sub.sound`, `Sub.args_sound`.

## Certificates

A certificate is an explicit proof tree, checked without a semantic oracle or
unbounded search. It has six forms, one per `Sub` rule:

| Form | Carries |
| --- | --- |
| `core` | the finite table and, for each fixed signature to derive, its derivation |
| `subset` | nothing: union inclusion is decided |
| `trans` | an intermediate type and a proof on each side |
| `inst` | the instance table, the instance types, the table's domain and free-variable certificate |
| `table` | the table, its domain and free-variable certificate |
| `gen` | a domain holding the type, its free-variable certificate, the type stating the scheme's signatures, and a proof of inclusion in it |

All six are accepted. `CertificateProducer` never emits `trans`: that
restricts search, not the accepted language, and a certificate written by
another producer may use it.

The checker is sound and complete for the rules:

$$
G\vdash S\le T\quad\Longleftrightarrow\quad
\exists p.\;\operatorname{check}(G,S,T,p)=\mathsf{true}.
$$

This is not completeness for every inclusion true in the model. Composed with
rule soundness, a checked certificate is a semantic inclusion:

$$
\operatorname{check}(G,S,T,p)=\mathsf{true}
\Longrightarrow
\forall n,W,v.\;
\llbracket S\rrbracket_G(n,W,v)\Rightarrow
\llbracket T\rrbracket_G(n,W,v),
$$

and likewise for argument lists. `accepted_subsumption` transports a
computation-safety judgment from $S$ to $T$; the typing theorem that uses it
is in [PROGRAM-TYPING.md](PROGRAM-TYPING.md).

Lean: `checkClause`, `checkCore`, `check_sound`, `check_complete`,
`derivable_iff_checked`, `accepted`, `accepted_subsumption`
(`Types/PositiveCertificates.lean`).

## State-assertion grammar

Point claims can combine ordinary types with facts about the current execution
state. The following notation describes the finite assertion layer; it does
not add constructors to the type grammar. Let $x$ and $y$ name environment
slots, $A$ be a type, and $R$ a finite disjunction of primitive predicates:

$$
\begin{aligned}
a &::= \mathsf{null}\mid\mathsf{undefined}\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{Number}\mid\mathsf{numLit}(b),\\
R &::= \{a_1,\ldots,a_k\}\quad(k\geq 0),\\
J &::= \top\mid x:A\mid x=R\mid x=y\mid x\mapsto R\mid x\mapsto y\mid J\land J.
\end{aligned}
$$

| Assertion | What it states |
| --- | --- |
| $x:A$ | The value of $x$ belongs to $A$ at the current world and level. |
| $x=R$ | $x$ satisfies one of the predicates in $R$. A statement about the environment, so no heap change can falsify it. |
| $x=y$ | $x$ and $y$ hold the same value, the same location when they hold references. Again untouched by heap changes. |
| $x\mapsto R$ | The cell $x$ names currently holds a value satisfying $R$. It does not change that location's contract. |
| $x\mapsto y$ | The cell $x$ names currently holds the value of $y$. A write or a call can falsify this. |
| $\top$, $J_1\land J_2$ | No requirement, or both. Conjunction asserts no ownership or disjointness. |

$=$ speaks only about the environment, $\mapsto$ about the heap as well; that
division decides which facts survive a step, and
[Program typing](PROGRAM-TYPING.md#the-reference-operations) states the rules
over it. Despite the notation there is no separating conjunction and no
ownership: the facts are duplicable, and $\mapsto$ does not claim the cell is
unaliased.

An empty predicate list is an impossible predicate, not an absent assertion.
There is no assertion disjunction, negation or quantifier: the union within
$R$ gives alternatives for one value, not correlated alternatives between
slots. `Number` means any number and `numLit(b)` exactly that bit pattern;
singletons imply `Number`, not conversely. Predicates on nested references are
outside this vocabulary.

The notation used in source claims is an abbreviation:

$$
x:\{\mathsf{value}:B=R\}
\quad\equiv\quad
x:\mathsf{ref}(B)\ \land\ x\mapsto R,
$$

where $\mathsf{ref}(B)$ is the plain cell $\mathsf{Ref}\,\{\mathsf{value}{:}B\}$.
On the right of `=`, `true` denotes $\{\mathsf{true}\}$ and `boolean` denotes
$\{\mathsf{true},\mathsf{false}\}$. So `{ value: boolean = true }` combines
`ref(boolean)` with a current-cell fact. It is neither `ref(true)` nor a type
that can appear inside operands; forgetting the cell fact leaves
`ref(boolean)`.

The implementation stores these conjunctions as a context $\Gamma$ plus
`HeapKnowledge.Knowledge`: cell facts (`HeapFacts.Holds`), immutable-value
facts (`HeapKnowledge.ValueHolds`) and read/equality links (`HeapLinks.Holds`,
whose `alias` flag distinguishes timeless slot equality from a current read).
A source expression assertion uses its evaluated result in place of $x$.
[Semantics](SEMANTICS.md#current-content-assertions-and-postconditions)
defines heap observations,
[Program typing](PROGRAM-TYPING.md#checked-expression-postconditions) the
checked rules and fact transfer, and
[Source claims](SOURCE-CLAIMS.md#current-content-assertions) the wire
encoding.

## Related layers

### Rigid inclusion

Direct types are a rigid name, ground graph labels, or a callable over direct
types. Inclusion under declared bounds, `RigidJudgments.Sub ps a b`, has four
rules: a rigid name is below itself; it is below whatever its declared bound
is below; ground label lists are compared by inclusion; and a callable is
below another when the other's parameters are each below its own and its
result is below the other's. The chain rule carries transitivity.
`Sub.refl` holds for every type, and `Sub.sound` proves the judgment
semantically sound on its own.

`Ty.leUnder` is the executable relation, a fuelled walk. For well-formed
parameter lists (distinct names, every rigid bound naming an earlier
parameter, every bound ground or rigid), `leUnder_iff_Sub` proves

$$
\mathsf{leUnder}(\bar P, a, b) = \mathsf{true}
\quad\Longleftrightarrow\quad
\bar P \vdash a \le b .
$$

`SourceJudgments.parametersOf_wellFormed` proves every list the source checker
builds is well formed, and `Sub_of_leUnder` needs no hypothesis. A parameter
bounded by a deep callable once exposed insufficient fuel:
`RigidJudgments.counterexample_derivable` is the derivation, and two kernel
guards record that the repaired fuel, which also pays for each parameter's
bound, accepts it.

#### Planned completeness extension: callable upper bounds

Well-formedness excludes callable bounds. This matches the current source
bound parser and simplifies the proof; it is not a design restriction or
evidence that completeness fails. `Sub.sound` and `Ty.leUnder_sound` already
cover callable bounds; what is unproved is that the walk accepts every
derivable inclusion with them.

The plan: extend well-formedness to acyclic callable bounds whose rigid
references, including those inside parameter and result types, name earlier
binders; prove a sufficient fuel bound, or replace the walk with an algorithm
whose termination measure accounts for entering bounds and reversing at
callable parameters; then extend `leUnder_iff_Sub` and the bound parser. This
is expected to need no change to the declarative rules, but that is not a
theorem. Recursive bounds are a separate extension and must not be admitted by
removing the restriction or adding fuel.

### Quantified scheme layer

Quantified local callables also form a layer outside the graph.
`TypeSchemes.schemeT` denotes one callable meeting its signatures at every
admissible assignment, while keeping the same captured world and field
contracts. The source slice checks one local closure under rigid binders and
their bounds, then compiles each checked ground elimination to fixed or
variadic graph signatures. For a scheme $S$, outer assignment $\eta_0$ and
assignment $\eta$,

$$
\begin{aligned}
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
\;\overset{\mathrm{def}}{\Longleftrightarrow}\;&
\mathsf{ClosedAssign}_P(\eta)
\land\mathsf{Satisfies}_{G,P}(\eta,S.\mathsf{bounds})
\land\forall i\notin S.\mathsf{binders}.\;\eta(i)=\eta_0(i),\\
\llbracket S\rrbracket^{\mathsf{scheme}}_{G,P,\eta_0}(n,W,v)
\;\overset{\mathrm{def}}{\Longleftrightarrow}\;&
\mathsf{Invocable}(v)\land\forall\eta.\;
\mathsf{Instance}_{G,P}(\eta_0,S,\eta)
\Rightarrow
\mathsf{Calls}(\mathsf{Sig}_\eta(S))\land\mathsf{Rests}(\mathsf{RestSig}_\eta(S)).
\end{aligned}
$$

The quantifier is inside membership of one $v$ at one $n,W$, so it cannot be
witnessed by a different closure per call. The last conjunct of `Instance`
keeps every non-binder meaning, including those the captured environment uses,
fixed across instantiations. Scheme rows are the graph form of the same idea
for generic methods ([Parameter and scheme rows](#parameter-and-scheme-rows)).

Lean: `TypeSchemes.lean`, `TypeParams.lean`, `Source/GenericSource.lean`,
`Source/GenericAlias.lean`.

## Limits

- The clause language has no negation or difference, and no surface `extends`
  language.
- Subtyping is sound and the checker complete for the rules; the rules are not
  complete for the model. For example, incompatible invariant contracts are
  never recognized as empty.
- `compatible` is a shape test, not a test of joint inhabitation.
- Rigid inclusion is complete only for well-formed bounds, which exclude
  callable bounds.
- Normalization has no growth control, and no verified compiler from textual
  type syntax to graphs exists.
- Generic methods are still receiver-quantified signatures, not host-relative
  scheme members.

## Lean files and validation

- `Types/ReferenceConjunctions.lean`, `Types/MethodMembers.lean`
- `Types/PositiveNormalization.lean`, `Types/PositiveGraphs.lean`,
  `Types/QuantifiedGraphs.lean`
- `Types/PositiveRules.lean`, `Types/PositiveCertificates.lean`
- `Tests/PositiveNormalizationTests.lean`

All under `lean/Verification/Model/`. Tests cover distribution, cross-shape
elimination, retained incompatible contracts, nested constraints, cyclic
normalization and checking, domain splitting, three-signature combination, and
rejection of invented constraints and false bottom claims. `lake -d
verification/lean build` checks the whole library; it contains no `sorry` or
custom axioms. `check_sound` uses `propext`; `check_complete` uses `propext`
and `Quot.sound`; semantic soundness also uses `Classical.choice`.
