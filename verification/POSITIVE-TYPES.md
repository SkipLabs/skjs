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
obligations, and $\Delta(A,B)$ says the pair $(A,B)$ is in it or that every
label of $A$ is a label of $B$: a type is within any type listing its labels,
which needs no row (`Rel`). Each section
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
| `dict` | a `refs` object whose present string keys also meet readonly and writable index contracts |
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
$\omega$, methods $\mu$ and own-key bounds $\beta$. An optional field
$\kappa{:}^{r}T$ carries a mode $r\in\{\mathsf{w},\mathsf{ro}\}$: writable or
readonly. Write $\ell$ for the object
$\mathsf{obj}(\mathit{flds},\mathsf{absent})$, $c_j\equiv T_j$ for "the
location's contract and $T$ agree below the level", $c_j\subseteq T_j$ for
"the contract implies $T$ below the level", and $c_j\sqsubseteq^{r}T_j$ for
$c_j\equiv T_j$ when $r=\mathsf{w}$ and $c_j\subseteq T_j$ when $r=\mathsf{ro}$
(`SlotContract`, as a tuple position's mode). Then

$$
\begin{aligned}
\llbracket\mathsf{Ref}(\vec\varphi;\psi;\omega;\mu;\beta)\rrbracket_n(W,v)
&\iff \textstyle\bigwedge_i\mathsf{rec}(\varphi_i)\land
      \mathsf{view}(\psi)\land\mathsf{opt}(\omega)\land\mathsf{meth}(\mu)\land
      \bigwedge_{b\in\beta}\mathsf{own}(b),\\
\mathsf{own}(b)_n(W,v)&\iff v=\ell\land\forall\kappa\in\mathrm{dom}(\mathit{flds}).\;b\vDash\kappa,\\
\mathsf{rec}(\overline{\kappa{:}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}T).\;\exists l,c.\;
      \mathit{flds}(\kappa)=l\land W(l)=c\land c_j\equiv T_j,\\
\mathsf{view}(\overline{\kappa{:}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}T).\;\exists l,c.\;
      \mathit{flds}(\kappa)=l\land W(l)=c\land c_j\subseteq T_j,\\
\mathsf{opt}(\overline{\kappa{:}^{r}T})_n(W,v)
&\iff v=\ell\land\forall(\kappa{:}^{r}T).\;
      (\mathit{flds}(\kappa)=\varnothing\Rightarrow\mathit{flds}(\mathsf{proto})=\varnothing)\\
&\qquad\land\forall l.\;\mathit{flds}(\kappa)=l\Rightarrow\exists c.\;W(l)=c\land c_j\sqsubseteq^{r}T_j.
\end{aligned}
$$

- **Invariant fields.** Every operand constrains the **same object**. Operands
  naming one key constrain one location, whose single stored contract agrees
  with each of them. They are not several cells, and they are not replaced by
  one contract at the intersection of their types. A plain reference cell is
  $\mathsf{Ref}\,\{\mathsf{value}{:}A\}$.
- **Views** only read: the location's contract implies the view's type, so a
  view grants no write.
- **Optional fields** constrain a key only where the object has it: a
  writable one as an invariant field does, a readonly one (`readonly k?: T`)
  as a view does, so a readonly optional field is a view that may be absent.
  A read gives $T$ or undefined, so an object lacking an optional key has no
  prototype, whose members the read would otherwise reach. No rule writes one,
  since an object's keys are fixed at allocation.
- **Methods** are host-relative members: read from the object and invoked on
  it, they behave as typed
  ([DESIGN.md](DESIGN.md#method-members-are-host-relative)). A member $m$ has
  fixed signatures $(\vec P\to B)$ and variadic ones $(\vec P,\ldots Q)\to B$,
  none with a receiver. With $\mathsf{on}_v(m)$ the member's signatures, each
  with $v$ as the one receiver it admits, and $\mathsf{holds}_k(A)$ the
  objects holding key $k$ at a location whose contract implies $A$ below the
  level,

  $$
  \mathsf{holds}_k(A)_n(W,v)\iff\exists l,c.\;
    v=\ell\land\mathit{flds}(k)=l\land W(l)=c\land
    \forall j<n,\ U\sqsupseteq W|_j,\ u.\;c_j(U,u)\Rightarrow u\in A_j(U),
  $$

  a member is where JavaScript's lookup finds its key: on the object, or,
  when the object lacks the key, on the object its prototype location holds:

  $$
  \mathsf{meth}(\mu)_n(W,v)\iff\forall m\in\mu.\;
    \mathsf{holds}_{m.\mathsf{key}}(\mathsf{on}_v(m))_n(W,v)\lor
    \bigl(m.\mathsf{key}\notin\mathit{flds}\land
      \mathsf{holds}_{\mathsf{proto}}(\mathsf{holds}_{m.\mathsf{key}}(\mathsf{on}_v(m)))_n(W,v)\bigr).
  $$

  The prototype's member is invoked on $v$, the object the read began at. The
  implication is claimed only in worlds extending the current one: in an
  unrelated world the object's locations need not hold their contracts, and no
  method reading them could be safe.

- **Own-key bounds** say which keys the object may have. Records are open, so
  only a bound says a key is absent, and so that a read of it continues at
  the prototype. A bound $b$ is $\mathsf{among}\,K$, own keys among $K$, or
  $\mathsf{outside}\,N$, no own key in $N$; it **admits** a key accordingly,
  $\mathsf{among}\,K\vDash\kappa\iff\kappa\in K$ and
  $\mathsf{outside}\,N\vDash\kappa\iff\kappa\notin N$ (`KeyBound.admits`), and
  $\beta$ **excludes** $\kappa$, $\beta\nvDash\kappa$, when some $b\in\beta$
  does not admit it (`Excludes`). A fresh literal's own keys are among its
  fields'. An array owns no key its prototype provides,
  $\mathsf{outside}\,N$ with $N$ `ArrayProto`'s keys: whatever else it owns,
  a read of one of those continues at the prototype, which it holds as a
  readonly view under the reserved key. An array may own further keys, as
  Skip's runtime marks the arrays it manages with a hidden symbol key
  ([DESIGN.md](DESIGN.md#the-array-prototype)). Keys are fixed at allocation,
  so a bound holds in every world.

A `dict` clause adds readonly **index contracts** $\overline{D}$: the object
has no prototype, and every present field under a string key, named or not,
has a contract implying each $D$. The object may lack a key, so an arbitrary
indexed read has type $D\mid\mathsf{undefined}$. It also adds **writable
index contracts** $\overline{C}$, a mutable index signature's: every present
string-keyed field's contract agrees with each $C$, as an invariant field's
does. A writable index is also listed among the readonly ones, which is what
reads use. With $\mathit{flds}(\mathsf{proto})=\varnothing$ in both,

$$
\begin{aligned}
\mathsf{dictView}(D)_n(W,v)&\iff v=\ell\land\forall s,l.\;\mathit{flds}(\mathsf{str}(s))=l\Rightarrow
  \exists c.\;W(l)=c\land c_j\subseteq D_j,\\
\mathsf{dictCell}(C)_n(W,v)&\iff v=\ell\land\forall s,l.\;\mathit{flds}(\mathsf{str}(s))=l\Rightarrow
  \exists c.\;W(l)=c\land c_j\equiv C_j.
\end{aligned}
$$

The calculus adds no key to an existing object; that TypeScript lets code
holding a mutable dictionary add keys at $C$ is a trust assumption
([DESIGN.md](DESIGN.md#writable-string-index-signatures)). Index contracts are guarded through the world, so a
recursive graph can contain `JsonObject = { readonly [key: string]: Json | null }`.

Lean: `refsT`, `viewT`, `OptionalField`, `optT`, `SlotContract`, `dictViewT`, `dictCellT`, `KeyBound`, `ownKeysT` (`Types/Types.lean`), `methodT`,
`memberT`, `holdsAt`, `onHost` (`Types/MethodMembers.lean`). The heap facts behind invariant
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
Every contract of the clause constrains the same array. An array meeting a
contract is **dense**: no element below its length is a hole.

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

A label is one of four kinds of **row**:

- a **clause row** means the union of its clauses;
- a **parameter row** means what the graph's assignment `env` gives it. The
  assignment is a mixed family over values and argument lists; a row's kind
  selects the component: values for a value binder, lists for a pack binder;
- a **scheme row** $(\vec p;\Sigma;\beta;\Sigma_\ldots)$ means one function
  meeting its signatures at every reassignment of its binders $\vec p$, which
  are parameter rows, within their bounds $\beta$;
- a **meet row** $p\sqcap\vec c$ means the values the assignment gives the
  value parameter row $p$ that are also in the clauses $\vec c$: the
  intersection of a type parameter with ground types, `V & DepSafe`.
  [Instances](#instances-of-a-scheme-row) give it its meaning at each
  instance, and [DESIGN.md](DESIGN.md#binders-met-with-ground-types) says how
  it is lowered.

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
\eta(p)\cap\textstyle\bigcup_{c\in\vec c}\llbracket c\rrbracket^\eta & i\ \text{the meet row}\ p\sqcap\vec c,\\[2pt]
\textstyle\bigcup_{c\in G(i)}\llbracket c\rrbracket^\eta & i\ \text{a clause row},
\end{cases}
$$

where $\Sigma^{\eta'}$ reads each signature's types at $\eta'$. $\vec X$
ranges over admissible mixed families, one per binder, and
$\mathsf{Bounded}_n(\vec X)$ says each bounded binder's family is below its
bound, in both components, at every level under $n$, the bound read at the
scheme's own $\eta$. A variadic signature's rest may be a binder: a **pack
parameter**, instantiated at a pack type and bounded by one. A meet row reads
its parameter as a parameter row does and its clauses' operands under their
guards as a clause row does, so it keeps the fixed point contractive; a pack
parameter's value component is empty, so a meet row names a value one.

Reading bounds below $n$ keeps the fixed point contractive; the
approximations are non-expansive in the assignment (`QInv`), which gives
admissibility. The type meanings are read at the graph's assignment:
$\llbracket A\rrbracket_G=\llbracket A\rrbracket^{G.\mathit{env}}$ for values
(`meaning`) and its list component for argument lists (`argMeaning`). No check
reads `env`, so every theorem proved for all graphs holds at every
reassignment. A member of a scheme row meets each instance's signatures
(`scheme_elim`), and a function meeting them at every instantiation is a
member (`scheme_intro`). Without scheme rows, meet rows and pack binders this
is the parametric semantics `denoteP` (`qDenote_no_schemes`).

Only clause rows have clauses. A type holding a parameter, scheme or meet row
has no expansion, so no rule that reads a clause (`Represents`, `Answers`, the
atoms of heap knowledge) applies to it. A meet row is below its parameter and
below its clauses, but no rule reads it as either: instance tables relate it
to other types, and at an instance it is a clause row.

Lean: `qDenoteWithArgs G (mixedParameters G)`, `Bounded`, `instanceTWithArgs`,
`instanceRestsWithArgs`, `NormalGraph.meets`, `NormalGraph.plain_iff` (`Types/PositiveGraphs.lean`,
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
\mathsf{Ref}(\varphi_0\,\vec\varphi;\psi;\omega;\mu;\beta)\land\mathsf{Ref}(\varphi'_0\,\vec\varphi';\psi';\omega';\mu';\beta')
 &=\mathsf{Ref}((\varphi_0\varphi'_0)\,\vec\varphi\,\vec\varphi';\psi\psi';\omega\omega';\mu\mu';\beta\beta'),\\
\mathsf{arrs}(L;S)\land\mathsf{arrs}(M;T)&=\mathsf{arrs}(LM;ST),\qquad
\mathsf{Ctors}\,L\land\mathsf{Ctors}\,M=\mathsf{Ctors}\,(LM),\\
\mathsf{List}\,\vec\tau\land\mathsf{List}\,\vec\tau'&=\mathsf{List}\,(\vec\tau\,\vec\tau'),\qquad
\mathsf{Pack}\,\vec\tau\land\mathsf{Pack}\,\vec\tau'=\mathsf{Pack}\,(\vec\tau\,\vec\tau').
\end{aligned}
$$

  The two first invariant operands are joined into one. A value has one
  own-field map, so one operand naming the fields of two says exactly what
  the two say, $\mathsf{rec}(\varphi\varphi')=\mathsf{rec}\,\varphi\cap
  \mathsf{rec}\,\varphi'$ (`recT_append`, `flatten`); and the read rules find
  a named field in the first operand, so a meet's fields are read as a
  record's (`{ readonly a: boolean } & { readonly b: number }` reads `b`).
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

A clause whose bounds exclude a key it says the object owns has no member at
any level: the key is at a location of the object, and no key of the object
is excluded. Such a clause is dropped from a meet (`Clause.consistent`,
`semWithArgs_consistent`):

$$
\mathsf{consistent}(\mathsf{Ref}(\vec\varphi;\psi;\omega;\mu;\beta))\iff
\forall\kappa\in\mathrm{dom}(\vec\varphi\,\psi).\;\forall b\in\beta.\;b\vDash\kappa,
\qquad
\operatorname{nf}(P\land Q)=\textstyle\bigvee\{\,e\in c\land d\;\mid\;\mathsf{consistent}(e)\,\},
$$

and likewise for `dict`. So an array with an own `map`, `number[] & { map:
number }`, whose bound excludes the key its record operand names, normalizes
to $\bot$, and an intersection lowering to $\bot$ is refused rather than
verified vacuously; an array with a key no prototype member has, such as
`[number, number] & Managed`, is kept.

Lean: `meet`, `Clause.consistent`, `meetLists`, `normalize`, `normalize_sound`
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
never covered. `dict` is covered by `dict`, and by `refs`, forgetting its
index contracts (below); `refs` covers `refs`, and `dict` through an own-key
bound (below). Write
$\Delta^{\pm}(A,B)$ for $\Delta(A,B)\land\Delta(B,A)$.

**Records.** With $\Phi=\varphi_0\cdots\varphi_m$ the source's invariant
operands, each target component is found in the source:

$$
\frac{\begin{array}{c}
\forall j,\,(\kappa{:}B)\in\varphi'_j.\;\exists(\kappa{:}A)\in\Phi.\;\Delta^{\pm}(A,B)\qquad
\forall(\kappa{:}B)\in\psi'.\;\exists(\kappa{:}A)\in\Phi\,\psi.\;\Delta(A,B)\\
\forall(\kappa{:}^{r'}B)\in\omega'.\;\mathsf{opt}_\Delta(\Phi;\psi;\omega;\beta)(\kappa{:}^{r'}B)\qquad
\Delta;S\vdash(\Phi\,\psi;\mu)\sqsubseteq_{\mathsf{meth}}\mu'\qquad
\forall b'\in\beta'.\;\beta\vdash b'
\end{array}}
{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi'_0\cdots\varphi'_k;\psi';\omega';\mu';\beta')}
$$

An invariant field needs an equivalent invariant field. A view is met by any
field whose type is within it. An optional field is met by a **slot** of the
source of the same key, an invariant field (mode $\mathsf{w}$), a view (mode
$\mathsf{ro}$) or an optional field (its own mode), whose type is within the
target's; a writable target also needs a writable slot of an equivalent type,
so no location is retyped. Or it is met by own-key bounds excluding both its
key and the prototype key: the object lacks the key and has no prototype, so a
read is `undefined`. With $\mathsf{slots}(\Phi;\psi;\omega)$ the source's
fields at $\mathsf{w}$, views at $\mathsf{ro}$ and optional fields,

$$
\mathsf{opt}_\Delta(\Phi;\psi;\omega;\beta)(\kappa{:}^{r'}B)\iff
\bigl(\exists(\kappa{:}^{r}A)\in\mathsf{slots}(\Phi;\psi;\omega).\;
  (r'=\mathsf{w}\Rightarrow r=\mathsf{w}\land\Delta(B,A))\land\Delta(A,B)\bigr)\lor
\beta\nvDash\kappa\land\beta\nvDash\mathsf{proto}.
$$

Where the object lacks the key, only an optional slot or a bound allows it, and
each says the object has no prototype. A required field is never met by a view
or an optional field, since neither says the key is present. Fields the target
does not name are not compared: records are open, so a record that does not
name an optional field's key may hold it at any type and does not cover it.
A bounded target's bounds follow from the source's (`CoversBound`,
`CoversBounds`): every key the source's bounds let the object own, each target
bound admits. An $\mathsf{outside}$ target needs each of its keys excluded; an
$\mathsf{among}$ target needs a source $\mathsf{among}$ bound each of whose
keys the target lists or the source excludes:

$$
\beta\vdash\mathsf{outside}\,N'\iff\forall\kappa\in N'.\;\beta\nvDash\kappa,\qquad
\beta\vdash\mathsf{among}\,K'\iff\exists\,\mathsf{among}\,K\in\beta.\;
  \forall\kappa\in K.\;\kappa\in K'\lor\beta\nvDash\kappa.
$$

So a fresh array object, own keys among its store and prototype, is an array,
own keys outside `ArrayProto`'s; and an array type is covered by another with
the same exclusion. A `dict` target also needs each readonly index contract within some source one, and each writable index contract equivalent to a writable source one, so a mutable dictionary is invariant and a readonly one is never mutable:

$$
\frac{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')\quad
      \forall D'\in\overline{D'}.\;\exists D\in\overline{D}.\;\Delta(D,D')\quad
      \forall C'\in\overline{C'}.\;\exists C\in\overline{C}.\;\Delta^{\pm}(C,C')}
     {\Delta;S\vdash\mathsf{Dict}(\Phi;\psi;\overline{D};\overline{C};\omega;\mu;\beta)\sqsubseteq
      \mathsf{Dict}(\varphi';\psi';\overline{D'};\overline{C'};\omega';\mu';\beta')}
$$

A dictionary is covered by a record whose members its own cover, as a
record's are; the record states no index, so the dictionary's index contracts
are forgotten. So `Serializable<Todo>`, a `Todo` whose every key holds `Json`,
is a `Todo`:

$$
\frac{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')}
     {\Delta;S\vdash\mathsf{Dict}(\Phi;\psi;\overline{D};\overline{C};\omega;\mu;\beta)\sqsubseteq
      \mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')}
$$

A record covers a `dict` through an own-key bound (`CoversKeys`): its own keys
are among some $\mathsf{among}\,K\in\beta$, where $K$ lists no prototype key, so the object has no
prototype; and every key of $K$ is a source field or view within each target
index view, and an invariant field equivalent to each writable index. No other
key exists, so this is what a fresh literal, whose own keys are exactly its
fields, needs to be a dictionary. The named members are compared as a
record's:

$$
\frac{\begin{array}{c}
\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq\mathsf{Ref}(\varphi';\psi';\omega';\mu';\beta')\qquad
\mathsf{among}\,K\in\beta\qquad\mathsf{proto}\notin K\\
\forall\kappa\in K.\;\bigl(\forall D'\in\overline{D'}.\;\exists(\kappa{:}A)\in\Phi\,\psi.\;\Delta(A,D')\bigr)\land
\bigl(\forall C'\in\overline{C'}.\;\exists(\kappa{:}A)\in\Phi.\;\Delta^{\pm}(A,C')\bigr)
\end{array}}
{\Delta;S\vdash\mathsf{Ref}(\Phi;\psi;\omega;\mu;\beta)\sqsubseteq
      \mathsf{Dict}(\varphi';\psi';\overline{D'};\overline{C'};\omega';\mu';\beta')}
$$

A record without such a bound, or whose bound admits a key it does not
name, may hold further keys at any type, and covers no index; so does an
array, whose bound only excludes keys.

**Methods.** A target method $m$ is covered by a source method of the same
key, by a function the source holds under that key whose receiver the source
type $S$ is within, or, when a key bound of the source excludes the key, by
such a function its prototype holds:

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

$$
\frac{\begin{array}{c}
\beta\nvDash m.\mathsf{key}\quad(\mathsf{proto}{:}P)\in\Phi\,\psi\quad
      (m.\mathsf{key}{:}F)\ \text{a field or view of}\ P\quad(F,L,M)\in\kappa\\
      \forall(\vec Q\to D)\in m.\;\exists(Q_0;\vec P)\to B\in L.\;
      \Delta(S,Q_0)\land\Delta(\vec Q,\vec P)\land\Delta(B,D)
\end{array}}
     {\Delta;\kappa;S\vdash(\Phi\,\psi;\mu;\beta)\sqsubseteq_{\mathsf{meth}}m}
$$

The third reads the member through the prototype, as the meaning does. Its
function type is a **known row** $(F,L,M)$ of $\kappa$: a row $F$ whose values
meet the arrows $L$, $M$, proved outside the table. For an array, $F$ is a
generic member of `ArrayProto` and $L$ its instance at the array's element
type, with the array as receiver: `Array.prototype[Symbol.iterator]` at
`number` covers `Iterable<number>`'s member. Each premise that names $\kappa$
passes it on unchanged.

Here $\Delta(\vec Q,\vec P)$ pairs the lists position by position and needs
equal lengths (`Domains`). Receivers of two members are not compared: both
are the host. Variadic member signatures are covered likewise, the target's
extra fixed parameters taken into the source's rest.

**Arrays and packs.** A writable `list` target contract is covered by a
writable source contract with as many required and optional positions, each
position equivalent to the target's (`CoversShape`): no location is retyped,
so mutable arrays are invariant. A readonly target only reads each element
present at its position's type, so it is covered as a pack is, below
(`CoversTuple`): an element's location has the contract of its source
position, which reads within the target position's type, and the list's
length lies within the target's bounds:

$$
\frac{\tau'\ \text{writable}\quad\tau\ \text{writable}\quad|\vec R|=|\vec R'|\quad|\vec O|=|\vec O'|\quad
      \forall i.\;\Delta^{\pm}(\mathsf{pos}_\tau(i),\mathsf{pos}_{\tau'}(i))}
     {\Delta\vdash\tau\sqsubseteq_{\mathsf{list}}\tau'}
\qquad
\frac{\tau'\ \text{readonly}\quad\Delta\vdash\tau\sqsubseteq_{\mathsf{pack}}\tau'}
     {\Delta\vdash\tau\sqsubseteq_{\mathsf{list}}\tau'}
$$

So `[number, number]` is a `readonly (Json | null)[]`, and meets `Json`
(`sum-tuple-value.ts`, `tuple-readonly-array.ts`), while it is not a
`number[]`, which TypeScript accepts though a write through it could append
past the tuple (`invalid-tuple-array.ts`).

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

Lean: `CoversFields`, `CoversViews`, `optionalSources`, `Excludes`, `CoversOptional`, `CoversKeys`, `covers_keys_sound`, `CoversMethods`, `CoversBound`, `CoversBounds`,
`CoversSig`, `CoversByFunction`, `CoversShape`, `CoversTuple`, `CoversPack`,
`covers_readonly_sound`, `covers_tuple_sound`, `covers_arguments_sound`.

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
$\Delta(B,D)$. One with a `never` parameter admits no actual list, so its
promise is vacuous and any class meets it; the results are still compared,
as TypeScript compares them. This is how `ResourceClass<C, never>` holds a
class whatever its constructor takes (`ArgsT_mem`):

$$
\frac{(\vec A\Rightarrow B)\in L\quad\Delta(\vec C,\vec A)\ \lor\ \bot\in\vec C\quad\Delta(B,D)}
     {\Delta\vdash\mathsf{Ctors}(L)\sqsubseteq(\vec C\Rightarrow D)}
$$ A variadic one is covered by a variadic source one with as many fixed
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
      \Delta;\kappa;A\vdash a\sqsubseteq b}
     {G;\kappa\vdash_c S\le T}
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

A premise $\Delta(A,B)$ also holds, with no entry, when every label of $A$ is
one of $B$'s: the meaning of a label list is the union of its labels', so the
induction needs no step for it (`mixed_subset`). A record below an interface
then needs no row relating each of its fields' contracts to itself, and no row
for everything those contracts reach.

`Core.mixed_sound` holds wherever the known rows do: each $(F,L,M)\in\kappa$
with $F$'s values within $\mathsf{arrs}(L;M)$ at every level.

Lean: `Core`, `Valid`, `Known`, `SameKind`, `Opaque`, `splitClause`,
`splitClause_sem`, `source_sem`, `CoversByProto`, `viewOf`, `covers_arrows_sound`,
`Core.mixed_sound`.

### Structural rules

`Sub` closes the core judgment under union inclusion and transitivity:

$$
\frac{G;\kappa\vdash_c S\le T\qquad\forall(F,L,M)\in\kappa.\;G\vdash F\le_{\mathsf{inst}}\mathsf{arrs}(L;M)}
     {G\vdash S\le T}
\qquad
\frac{\forall i\in S.\ i\in T}{G\vdash S\le T}
\qquad
\frac{G\vdash S\le U\quad G\vdash U\le T}{G\vdash S\le T}.
$$

The core rule's known rows are instances of scheme rows, each checked as
`inst` checks one (below, $\le_{\mathsf{inst}}$), against its arrows given
inline rather than as a type of the graph: an array's instance of a prototype
member has no row of its own.

Reflexivity and invariance under reordering or duplicating union labels
follow (`Sub.refl`, `Sub.congr`). Transitivity composes completed proofs, not
unchecked back-references in a table.

Three more rules read scheme rows. They turn on which **parameter rows a row
depends on**. A free-variable certificate $V$ on a domain $D$ assigns each
$i\in D$ a set $V(i)$ of parameter rows, with $D$ closed under what its rows
read (a clause row its operands, a scheme row its signature types, a meet row
its clauses' operands), such that

$$
i\ \text{a parameter row}\Rightarrow i\in V(i),\qquad
i=p\sqcap\vec c\Rightarrow p\in V(i),\qquad
l\in\mathsf{reads}_G(i)\Rightarrow V(l)\subseteq V(i)\cup\mathsf{binders}(i),
$$

where $\mathsf{binders}(i)$ is empty unless $i$ is a scheme row, so a scheme's
own binders are not free in it. A row means the same at two assignments that
agree on $V(i)$.

Lean: `FreeOk`, `freeOk_meet`, `meetClauses`, `agree_freeWith`, `mixed_respectsFree`.

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
- **fixed**: $T=\{i\}$ and $\kappa$ fixes $i$: it names no row of $V(i)$
  but parameter rows it maps to themselves, $\kappa(p)\in\{\bot,\{p\}\}$ for
  $p\in V(i)$, with $\kappa(p)=\{p\}$ only for a parameter row $p$ (inside a
  scheme matched against itself its binders stand for themselves; `fixedBy`);
- $i$ a clause row, $T=\{j\}$, $j$ a clause row, and $G(j)\doteq G(i)[\kappa]$:
  the same clauses, each operand with the same members as its image;
- $i$ the meet row $p\sqcap\vec c$ of a value parameter row $p$, every operand
  of $\vec c$ with an image, and $T=\{j\}$ with either $j$ the meet row
  $q\sqcap\vec d$ of a value parameter row $q$, $\kappa(p)=\{q\}$ (or $q=p$
  when $\kappa$ does not name $p$) and $\vec d\doteq\vec c[\kappa]$; or $j$ a
  clause row of value kind, $\kappa(p)=U$ a type of clause rows, and
  $G(j)\doteq\mathsf{meetLists}(G(U),\vec c[\kappa])$ or
  $G(j)\doteq\mathsf{meetLists}(\vec c[\kappa],G(U))$ (`meetOk`): the meet of
  the parameter's image with the clauses' images, which is what lowering
  `T & DepSafe` at `T := U` gives;
- $i$ the scheme row $(\vec q;\Sigma';\beta';\Sigma'_\ldots)$, $T=\{j\}$, $j$
  the scheme row $(\vec r;\Sigma'[\kappa'];\beta'[\kappa];\Sigma'_\ldots[\kappa'])$
  with $|\vec r|=|\vec q|$, $\vec r$ distinct parameter rows of matching kinds
  and $\kappa'=(\vec q\mapsto\vec r)\cdot\kappa|_{V(i)\setminus\vec q}$, the
  binders then $\kappa$ on $i$'s free rows only, in $V(i)$'s order
  (`enter`), provided no free row of $i$ outside $\kappa$'s domain, and no
  row free in an image $\kappa(p)$ for $p\in V(i)$, is in $\vec r$ (no
  capture).

A meet row's entry is sound because at assignments related by $\kappa$ its
parameter's values are $\kappa(p)$'s, its clauses mean their images', and the
meet of two clause lists means the intersection of their meanings
(`meetLists_sound`), in either order:

$$
\frac{\eta_L(p)=\llbracket U\rrbracket^{\eta_R}\qquad
      \llbracket\vec c\rrbracket^{\eta_L}=\llbracket\vec c[\kappa]\rrbracket^{\eta_R}\qquad
      G(j)\doteq\mathsf{meetLists}(G(U),\vec c[\kappa])}
     {\llbracket p\sqcap\vec c\rrbracket^{\eta_L}
      =\llbracket U\rrbracket^{\eta_R}\cap\llbracket\vec c[\kappa]\rrbracket^{\eta_R}
      =\llbracket j\rrbracket^{\eta_R}}\ \textsc{meet-image}
$$

Neither a meet row nor its image has argument lists (its image is of value
kind). So `V & DepSafe` at `V := [number, number]` is the tuple's meet with
each of DepSafe's alternatives: the primitives meet no array, and `Managed`,
a record, meets the array shape as one object holding its key too. That
object is inhabited: an array owns no key its prototype provides, and may own
`Managed`'s symbol key, which is none of them
([Conjunction and normalization](#conjunction-and-normalization)). The meet
row's rule does not depend on the array bound.

Entering a scheme keeps only what its free rows read, and nothing inside it
reads more (a signature's free rows are $i$'s or its binders), so the entry's
meaning is the same as under all of $\kappa$. Keeping less is what makes a
table for recursive types finite: relating `EagerCollection<K2ᵃ, V2ᵃ>` to
`EagerCollection<K2ᵇ, V2ᵇ>` enters `map`, then `reduce`, then `map` again,
without end, and a context carrying every scheme entered would never recur,
while one restricted to free rows alternates between two.

The table is checked when its rows lie in a domain with a free-variable
certificate and every entry is one of these. The producer (`matchRow`, not
trusted) builds a scheme entry's table by matching the bounds $\beta'$ under
$\kappa$, where they are read, and the signatures under $\kappa'$, so a generic
method whose result is its own interface at a bounded binder, such as
`map<V2, P extends readonly number[]>(m: new (...p: P) => Mapper<V, V2>, ...p: P): Box<V2>`,
has one (`class-value-generic-method`). Then, for every entry and every
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
\forall\tau\in L.\;\exists\sigma\in\Sigma.\;\tau\doteq\sigma[\kappa_0]\quad
\forall\tau\in M.\;\exists\sigma\in\Sigma_\ldots.\;\tau\doteq\sigma[\kappa_0]
\end{array}}
     {G\vdash\{i\}\le T}\ \textsc{inst}
$$

Here $\tau\doteq\sigma'$ when the two have the same arity and each type of
$\tau$ has the same members as the corresponding type of $\sigma'$: a type
means the union of its labels, so their order does not matter
(`sameLabels`, `sigMatch`, `restMatch`, and for clauses `sameClauses`). The
premises other than $T\equiv_G\mathsf{arrs}(L;M)$ are $G\vdash\{i\}\le_{\mathsf{inst}}\mathsf{arrs}(L;M)$
(`InstArrs`).

The same tables relate two rows of one type that differ only in which binder
rows their schemes use. Lowering gives one row per generic application
([DESIGN.md](DESIGN.md#one-row-per-application)), so this is for graphs that
hold copies anyway. With the empty context each row means its image:

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

Lean: `entryOk`, `meetOk`, `TableOk`, `instKinds`, `substitutionKind`, `InstArrs`, `Inst`,
`mixed_assignment_substitution`, `meet_row_value`, `meet_noArguments`,
`meetOk_noArguments`, `table_row_mixed`, `Sub.inst`, `Sub.table`,
`Sub.gen`, `Sub.mixed_sound`, `Sub.sound`, `Sub.args_sound`.

## Certificates

A certificate is an explicit proof tree, checked without a semantic oracle or
unbounded search. It has six forms, one per `Sub` rule:

| Form | Carries |
| --- | --- |
| `core` | the finite table, for each fixed signature to derive its derivation, and its known rows, each with its instance |
| `subset` | nothing: union inclusion is decided |
| `trans` | an intermediate type and a proof on each side |
| `inst` | the instance: its table, the instance types, a certificate per bound, the table's domain and free-variable certificate |
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
