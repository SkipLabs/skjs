# Connecting the model to ECMAScript

A sketch, not a plan of record. It states what a connection between this
development and a mechanized semantics of ECMA-262 would establish, which
parts of the [trust surface](DESIGN.md#trust-surface) it would turn into
theorems, which would remain assumptions, and what each piece would cost.
The nested-promise case illustrates what such a connection catches.

## What is proved today

[`checkJson_safe`](DESIGN.md#what-verified-means) is a theorem about the
**calculus**: for every accepted unit, every assignment $\eta$ of its
parameter rows, and every environment meeting the unit's inputs, the unit's
graph is `SafeGraph`. It never steps to a stuck state: every run returns a
value of its declared type, throws a closed value, or takes another step.

Two links between that theorem and a JavaScript run are not proved.

1. **The calculus is faithful to JavaScript.** Its step rules (`Calculus.lean`,
   [SEMANTICS](SEMANTICS.md#operational-language)) are our reading of the
   language. They are checked by review and by `#guard` tests against node,
   such as `numberToString`, `%` and `binop`, not against the specification.
2. **The host meets its stated types.** Promises, `await`, the library
   built-ins and the intrinsics have no step rules. They enter as values in
   the environment with a declared type (`EnvOk`). The theorem assumes the
   native code behaves as typed.

Source-to-calculus compilation is a third link. It is checked by the parser's
gate and by Lean's re-extraction of the claims, not proved preserving; see
[next steps](DESIGN.md#next-steps).

## The pieces of a connection

- **M**, a mechanized [ECMA-262](REFERENCES.md#ecma-262) semantics: an abstract machine over the
  specification's values, records, realms and job queue, with the built-ins'
  algorithms. ESMeta (formerly JISET, [Park et al. 2020](REFERENCES.md#jiset-and-esmeta)) extracts such a semantics from the
  specification's own algorithm text and covers promises and async. Using it
  from Lean would mean importing or re-stating its fragment in Lean. JSCert
  ([Bodin et al. 2014](REFERENCES.md#bodin-et-al-2014-jscert)) is a hand-written Coq alternative, for
  ECMAScript 5, before promises.
- **C**, the existing compilation from a TypeScript source unit to a
  calculus program.
- **R**, a relation between calculus states and M states:
  - values: primitives, including `numberToString`'s spelling of property keys;
  - objects: calculus locations to M objects, with own keys, `[[Prototype]]`
    and data properties;
  - the calculus's reserved keys: the array store `[]`, `[[proto]]`, the class
    brand;
  - realm objects: `Array.prototype`, `Promise`, and so on;
  - a graph's program point and slots to an M execution context.

## Expected top-level results

Each is a theorem to prove. Stated informally; $\to$ is a calculus step,
$\to_M$ an M step.

**T1. Faithfulness (simulation).** If $s \mathrel{R} m$ and $s \to s'$, then
$m \to_M^{+} m'$ with $s' \mathrel{R} m'$. If $s$ raises $v$, then $m$ throws a
value related to $v$. If $s$ is stuck, then $m$ either throws or performs an
operation the fragment refuses. T1 retires link 1. Its cost is a
per-rule proof against the specification's algorithms: property access,
`ToPropertyKey`, the arithmetic and relational operators, strict equality,
`ToBoolean`, `typeof`, allocation and copying from parts, prototype-chain
lookup and `instanceof`.

**T2. Host specifications as lemmas.** For every intrinsic and overlay entry
$x : \tau$ in the trust surface, the corresponding M built-in $b_x$ is in the
M-level meaning of $\tau$: $b_x \in \llbracket \tau \rrbracket_M$. The meaning
$\llbracket \cdot \rrbracket_M$ is the calculus's type meaning transported
along R, with one extension: a `Promise<X>` is a realm promise whose
fulfillment value is in $\llbracket X \rrbracket_M$. T2 retires most of link 2:
every row of the trust surface that names ECMA behaviour, such as `%Await%`,
`%Iterate%`, `%ForIn%`, `Array.prototype`'s members, `JSON`, `BigInt` and
`Set`/`Map`/`Date`, becomes a proof obligation.

**T3. End-to-end.** For a source unit $u$ that `check.mts` verifies: run
$C(u)$'s source in M, from any M state whose environment values are in the
M-meanings of the unit's declared inputs. Then every value observed at a
claimed program point is in the M-meaning of its claim, and every run
returns, throws, or continues. T3 composes `checkJson_safe` with T1 and T2.
Its remaining premises are only about code outside ECMA:
- imported modules and ambient declarations meet their declared types;
- the SKJS runtime keeps its interface;
- the trusted tools are correct: TypeScript's resolution and the parser.

What stays assumed is exactly what no specification of the language can
state: other people's code.

## Illustration: nested promises

**The error.** The trust surface once stated
$\mathtt{\%Await\%} : \forall T.\ \mathsf{Promise}\langle T\rangle \Rightarrow T$
with $T$ unbounded. A trusted generic declaration such as
`declare function wrap<T>(x: T): Promise<T>` could be instantiated at
`T = Promise<number>`. The model then expected `await wrap(p)` to be a
promise, but at run time it is a `number`. Every proof went through. The
false statement was an assumption, so nothing failed.

**What T2 would have exposed.** Take the lemma
$b_{\mathtt{Await}} \in \llbracket \forall T.\ \mathsf{Promise}\langle T\rangle \Rightarrow T \rrbracket_M$.
It is false at any thenable $T$, and the specification gives the
counterexample directly:
- a promise's resolve function, called with a value that has a callable
  `then`, does not fulfill with it; it schedules `NewPromiseResolveThenableJob`
  and adopts it (ECMA-262, *Promise Resolve Functions*);
- so no realm promise is ever fulfilled with a thenable;
- `Await` of a realm promise yields its fulfillment value
  (*Await*, *PromiseResolve*).

Hence $\llbracket \mathsf{Promise}\langle \mathsf{Promise}\langle \mathsf{number}\rangle\rangle \rrbracket_M = \emptyset$
among realm promises. Any type claiming such a value is empty, so the lemma
cannot be proved.

**What T3 would have exposed.** The declaration `wrap<T>` enters T3 as a
premise: `wrap` is in $\llbracket \forall T.\ T \Rightarrow \mathsf{Promise}\langle T\rangle\rrbracket_M$.
At $T = \mathsf{Promise}\langle\mathsf{number}\rangle$ the result type is
empty, so no implementation meets the premise, and T3's conclusion is vacuous
for every program that uses `wrap` there. T3 needs no premise to be
satisfiable, so this surfaces only if someone asks for it. That is a
reason for T3 to include a satisfiability check of its external premises at
their instantiations.

**The fix, read through the connection.** The pipeline now states:
- `%Await%` at $\forall T,\ U \le P.\ (\mathsf{Promise}\langle T\rangle \mid U) \Rightarrow T \mid U$;
- the host assumption that a value of type `Promise<T>` is a realm promise,
  with the source refused from building an object that has a `then` member;
- a trusted generic signature's type parameters that occur under
  `Promise<…>` bounded by the non-thenable types
  $N = P \mid \{\mathtt{readonly\ then?}: P\} \mid \mathsf{readonly\ unknown[]}$.

Under the connection:
- the bounded `%Await%` lemma is provable from the specification;
- "`Promise<T>` values are realm promises" becomes a lemma for every promise
  the program or the built-ins create;
- the non-thenable bound is exactly the condition under which a trusted
  generic promise signature is satisfiable, so T3's external premises are no
  longer vacuous.

The only assumption left is that third-party code keeps its declared promise
types, which no specification can state. The same fact is discussed for
ReScript ([#5709](REFERENCES.md#rescript-5709), [#6433](REFERENCES.md#rescript-6433), [#2345](REFERENCES.md#rescript-2345)) and TypeScript
([#27711](REFERENCES.md#typescript-27711), [#49946](REFERENCES.md#typescript-49946), [#35419](REFERENCES.md#typescript-35419),
[#55408](REFERENCES.md#typescript-55408)).

The same shape recurs in any **flattening** constructor, one whose runtime
representation satisfies $c\langle c\langle t\rangle\rangle = c\langle t\rangle$,
such as nullable values and promises. A generic signature is truthful at
$c\langle T\rangle$ only for $T$ outside $c$'s image, and generic
instantiation can always produce the nested type ([TypeScript #59111](REFERENCES.md#typescript-59111);
two such constructors composed, [ReScript #5211](REFERENCES.md#rescript-5211)). So soundness cannot rest
on banning nested types: it has to come from the meaning of the constructor,
or from a bound at every trusted instantiation ([ReScript #5707](REFERENCES.md#rescript-5707)).

## Cost, roughly

| Piece | Scale | Retires |
| --- | --- | --- |
| M in Lean, for the fragment's operations and built-ins | Large: importing or re-stating ESMeta's semantics for objects, operators, promises and the job queue | — |
| R and T1 | Large: one simulation case per calculus rule, including graph code and `merge` | Link 1: every "the calculus reads JavaScript this way" statement in DESIGN |
| T2 | Medium per built-in; many built-ins | The ECMA rows of the trust surface |
| T3 | Small once T1 and T2 exist | Composition; the satisfiability check for external premises |

A cheaper intermediate step catches much of the same class of error without
M: a differential harness that runs node against each trust-surface entry
and calculus rule on generated values. Its adversarial inputs are thenables,
extra own keys, `NaN`/`-0`, holes and nested promises. It proves nothing,
but it would have flagged the unbounded `%Await%` mechanically.
