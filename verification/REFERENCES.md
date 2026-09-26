# References

Every paper, specification, tool and issue this development draws on, in one
place. Other documents cite an entry by a short link to its anchor, such as
[Abadi and Cardelli 1996](#abadi-and-cardelli-1996); they do not restate the
bibliography.

Each entry gives the full citation, what the project takes from the work, and
where that is discussed: current document sections and code, and, where a
discussion survives only in history, the commits by short hash. An entry marked
**historical** backed a result or an explanation that has since been removed;
it is kept so the attribution is not lost.

## Semantics and logical relations

### Appel and McAllester 2001

Andrew W. Appel and David McAllester. *An indexed model of recursive types for
foundational proof-carrying code.* ACM Transactions on Programming Languages
and Systems 23(5):657–683, 2001.
[doi:10.1145/504709.504712](https://doi.org/10.1145/504709.504712).

**Used for** the step-indexed model: a type is a family indexed by a budget,
`Safe A n` asks for safety only for $n$ steps, and a recursive type reads its
operands only at lower indices. This is the budget of `Safe`, `SafeGraph` and
every `Fam`.
**Discussed in** [SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types),
[POSITIVE-TYPES: notation](POSITIVE-TYPES.md#positive-types),
[DESIGN: heap and contracts](DESIGN.md#heap-and-contracts).
Named as "step-indexed logical relations (Appel and McAllester 2000)" in the
removed "Names" section of SEMANTICS (added `50217bc1`, removed `d54ee142`);
the journal version is 2001.

### Ahmed 2004

Amal Ahmed. *Semantics of Types for Mutable State.* PhD thesis, Princeton
University, 2004.

**Used for** step-indexed worlds for higher-order mutable state: every
location carries a type (here, a contract) in a world, a reference is
invariant because the world fixes its contract, heap satisfaction ties
contracts to contents, and functions are safe in every future world. This is
`WorldT`, `refT`, `HeapOk` and admissible world extension.
**Discussed in** [DESIGN: heap and contracts](DESIGN.md#heap-and-contracts),
[SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types),
[INTERSECTIONS: what the model fixes](INTERSECTIONS.md#what-the-model-fixes);
named in the removed "Names" section of SEMANTICS (`50217bc1`, removed
`d54ee142`).

### Dreyer, Ahmed and Birkedal 2011

Derek Dreyer, Amal Ahmed and Lars Birkedal. *Logical step-indexed logical
relations.* Logical Methods in Computer Science 7(2:16), 2011; conference
version LICS 2009. [doi:10.2168/LMCS-7(2:16)2011](https://doi.org/10.2168/LMCS-7%282:16%292011).

**Background**, not cited in the documents: the logic in which "below the
level" is a later modality ▷ over Kripke-style (world-indexed) logical
relations. The development does not use this logic; it works with explicit
indices ([POSITIVE-TYPES: notation](POSITIVE-TYPES.md#positive-types)).

### Nakano 2000

Hiroshi Nakano. *A modality for recursion.* Proceedings of the 15th Annual
IEEE Symposium on Logic in Computer Science (LICS 2000), pp. 255–266.
[doi:10.1109/LICS.2000.855774](https://doi.org/10.1109/LICS.2000.855774).

**Used for** guarded recursion: a recursive type is well defined when its
recursive occurrences sit under a guard (the later modality ▷), here a read
below the current budget.
**Discussed in** [SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types),
[DESIGN: heap and contracts](DESIGN.md#heap-and-contracts).
Named in the removed "Names" section of SEMANTICS (`50217bc1`, removed
`d54ee142`).

### Birkedal et al. 2012

Lars Birkedal, Rasmus Ejlers Møgelberg, Jan Schwinghammer and Kristian
Støvring. *First steps in synthetic guarded domain theory: step-indexing in
the topos of trees.* Logical Methods in Computer Science 8(4:1), 2012;
conference version LICS 2011.
[doi:10.2168/LMCS-8(4:1)2012](https://doi.org/10.2168/LMCS-8%284:1%292012).

**Used for** the categorical reading of the guarded fixed point: contractive
operators on step-indexed families have unique fixed points, with no
monotonicity required, so recursion through function domains is admitted.
**Discussed in** [SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types)
(`Tower.lean`), `Types.lean`'s module comment. Named in the removed "Names"
section of SEMANTICS (`50217bc1`, removed `d54ee142`).

### Banach 1922

Stefan Banach. *Sur les opérations dans les ensembles abstraits et leur
application aux équations intégrales.* Fundamenta Mathematicae 3:133–181,
1922.

**Used for** the fixed-point theorem behind recursive types: a contractive
operator, with distance the first budget at which two families disagree, has
a unique fixed point.
**Discussed in** `lean/Verification/Model/Types/Types.lean` (module comment),
[SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types).

### Jung et al. 2018 (Iris)

Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars
Birkedal and Derek Dreyer. *Iris from the ground up: A modular foundation for
higher-order concurrent separation logic.* Journal of Functional Programming
28:e20, 2018. [doi:10.1017/S0956796818000151](https://doi.org/10.1017/S0956796818000151).

**Historical.** Cited as the machinery that carries guarded recursive
predicates in practice. The development does not use Iris.
**Discussed in** the removed "Names" section of SEMANTICS (`50217bc1`,
removed `d54ee142`).

### Wright and Felleisen 1994

Andrew K. Wright and Matthias Felleisen. *A syntactic approach to type
soundness.* Information and Computation 115(1):38–94, 1994.
[doi:10.1006/inco.1994.1093](https://doi.org/10.1006/inco.1994.1093).

**Used for** the shape of the safety statement with exceptions: a well-typed
program yields a value of its type, takes a step, or raises; a type says what
a value is, never that none is thrown. The development proves this shape
semantically, not by progress and preservation.
**Discussed in** [DESIGN: principles](DESIGN.md#principles),
[DESIGN: throws](DESIGN.md#throws),
[SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types).
Named ("ML-style type soundness with exceptions, Wright and Felleisen's") in
DESIGN's Throws section (`693d706a`), dropped in the DESIGN rewrite
(`6ee739f8`).

### Reynolds 1983

John C. Reynolds. *Types, abstraction and parametric polymorphism.*
Information Processing 83, Proceedings of the IFIP 9th World Computer
Congress, pp. 513–523. North-Holland, 1983.

**Used for** the idea behind `Parametricity.accept_reassign`: a checker that
never inspects how a type parameter is interpreted accepts a generic body at
every interpretation, so one derivation covers every instantiation.
**Discussed in** [DESIGN: generic bodies](DESIGN.md#generic-bodies),
[DESIGN: lasting decisions](DESIGN.md#lasting-decisions),
[POSITIVE-TYPES: parameter and scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows).

## Objects and self types

### Abadi and Cardelli 1996

Martín Abadi and Luca Cardelli. *A Theory of Objects.* Monographs in Computer
Science, Springer, 1996.
[doi:10.1007/978-1-4419-8598-9](https://doi.org/10.1007/978-1-4419-8598-9).

**Used for** self-application: in the ς-calculus a method is a function of
its host object (its self), and invoking `o.l` runs the method with `o` bound
to self. A method member's contract here is likewise relative to its host:
read from `o` and invoked with receiver `o` it behaves as typed, and it
promises nothing for another receiver (`methodT`, `holdsAt`, `bindMember`).
The development takes the self-application semantics, not the book's Self
types or its object subtyping.
**Discussed in** [DESIGN: method members are host-relative](DESIGN.md#method-members-are-host-relative),
[POSITIVE-TYPES: records](POSITIVE-TYPES.md#records),
`lean/Verification/Model/Types/MethodMembers.lean` (module comment). Designed
in `6a823646` and `d6645444`; the citation was dropped from DESIGN in
`6ee739f8`.

### Smith, Walker and Morrisett 2000

Frederick Smith, David Walker and Greg Morrisett. *Alias Types.* In
Programming Languages and Systems (ESOP 2000), LNCS 1782, pages 366–381,
Springer, 2000.
[doi:10.1007/3-540-46425-5_24](https://doi.org/10.1007/3-540-46425-5_24).

**Used for** the strong update: a change to a location's type is sound where
no other reference to the location exists, since no one else holds the old
type. A key-adding write changes an object's own keys, so it is typed only on
a local's own fresh object nothing else has reached; the pipeline takes the
idea, not the paper's linear capabilities: the unaliasedness is a syntactic
fact of the source (`growSites`), and the write is a copy the local is
rebound to rather than an update in place.
**Discussed in** [DESIGN: objects and prototypes](DESIGN.md#objects-and-prototypes),
[PROGRAM-TYPING: key-adding writes](PROGRAM-TYPING.md#key-adding-writes).

## Type-system design

### Frisch, Castagna and Benzaken 2008

Alain Frisch, Giuseppe Castagna and Véronique Benzaken. *Semantic subtyping:
Dealing set-theoretically with function, union, intersection, and negation
types.* Journal of the ACM 55(4):19:1–19:64, 2008; conference version LICS
2002. [doi:10.1145/1391289.1391293](https://doi.org/10.1145/1391289.1391293).

**Used as the contrast** for subtyping in a model with state. The
set-theoretic arrow decomposition $(A\to B)\wedge(A\to C)\le A\to(B\wedge C)$
holds in semantic subtyping and fails here: an allocating function meets both
arrows by choosing different cell contracts. The development therefore keeps
a clause-to-clause rule and refuses that law.
**Discussed in** [SEMANTICS: two retained design constraints](SEMANTICS.md#two-retained-design-constraints),
[DESIGN: lasting decisions](DESIGN.md#lasting-decisions),
[INTERSECTIONS](INTERSECTIONS.md#what-the-model-fixes). Named in
`85ce52c4` (INTERSECTIONS and its commit message) and in the positive-types
completeness study (`50217bc1`, removed `d54ee142`).

### Amadio and Cardelli 1993

Roberto M. Amadio and Luca Cardelli. *Subtyping recursive types.* ACM
Transactions on Programming Languages and Systems 15(4):575–631, 1993.
[doi:10.1145/155183.155231](https://doi.org/10.1145/155183.155231).

**Historical.** Sound and complete axiomatization of equality and subtyping
for recursive types, the cycle handled by an assumption set (the Amber rule).
It placed the removed equality-completeness result (`semantic_eq_iff`).
**Discussed in** `50217bc1` (removed in `d54ee142`). Recursive types are
still finite graphs checked coinductively over a table of assumed pairs
([POSITIVE-TYPES: subtyping](POSITIVE-TYPES.md#subtyping)).

### Brandt and Henglein 1998

Michael Brandt and Fritz Henglein. *Coinductive axiomatization of recursive
type equality and subtyping.* Fundamenta Informaticae 33(4):309–338, 1998;
conference version TLCA 1997.

**Historical.** The coinductive rule over an assumption set that the
certificate checker's table $\Delta$ follows.
**Discussed in** `50217bc1` (removed in `d54ee142`);
[POSITIVE-TYPES: notation](POSITIVE-TYPES.md#positive-types) states the table
without the citation.

### Milner 1984

Robin Milner. *A complete inference system for a class of regular
behaviours.* Journal of Computer and System Sciences 28(3):439–466, 1984.
[doi:10.1016/0022-0000(84)90023-0](https://doi.org/10.1016/0022-0000%2884%2990023-0).

**Historical.** Unique solutions of guarded equations, the shape of the
removed equational theory of recursive-type equality.
**Discussed in** `50217bc1` (removed in `d54ee142`).

### Salomaa 1966

Arto Salomaa. *Two complete axiom systems for the algebra of regular events.*
Journal of the ACM 13(1):158–169, 1966.
[doi:10.1145/321312.321326](https://doi.org/10.1145/321312.321326).

**Historical.** The ancestor of the unique-fixed-point rule, whose side
condition corresponds to guardedness.
**Discussed in** `50217bc1` (removed in `d54ee142`).

### Pierce 1994

Benjamin C. Pierce. *Bounded quantification is undecidable.* Information and
Computation 112(1):131–165, 1994.
[doi:10.1006/inco.1994.1055](https://doi.org/10.1006/inco.1994.1055).

**Used for** the restriction a subtyping rule between quantified signatures
must take: subtyping in System F<:, whose rule for bounded quantifiers
compares the bounds contravariantly and the bodies under the target's, is
undecidable, so the rule relating two generic methods instantiates the
target's binders rigidly and the source's at them only where the binder
counts are equal and the bounds identical, a decidable check.
**Discussed in** [DESIGN: next steps](DESIGN.md#next-steps).

## JavaScript and ECMAScript

### ECMA-262

Ecma International, TC39. *ECMAScript Language Specification* (ECMA-262).
The development reads the current draft,
[tc39.es/ecma262](https://tc39.es/ecma262/) (titled *ECMAScript® 2027
Language Specification* as of this writing). Sections relied on by name:

- [PromiseResolve](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-promise-resolve),
  [Await](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#await),
  [NewPromiseResolveThenableJob](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-newpromiseresolvethenablejob),
  and the promise resolve functions, which older editions title *Promise
  Resolve Functions* and the 2027 draft defines in
  [CreateResolvingFunctions](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-promise-resolve-functions);
- [Number::equal](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-equal),
  `IsStrictlyEqual`, `ToString`/`Number::toString`, `ToPropertyKey`,
  `ToBoolean`, `typeof`;
- [OrdinaryCallBindThis](https://tc39.es/ecma262/#sec-ordinarycallbindthis),
  [EvaluateCall](https://tc39.es/ecma262/multipage/ecmascript-language-expressions.html#sec-evaluatecall),
  bound function exotic objects, `Function.prototype.apply`;
- iteration: [ForIn/OfBodyEvaluation](https://tc39.es/ecma262/#sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset)
  and [IteratorClose](https://tc39.es/ecma262/#sec-iteratorclose) (an early
  exit calls `return` only where the iterator has one),
  [%ArrayIteratorPrototype%.next](https://tc39.es/ecma262/#sec-%arrayiteratorprototype%.next)
  (the length read at each step),
  [%StringIteratorPrototype%.next](https://tc39.es/ecma262/#sec-%stringiteratorprototype%.next)
  (code points), [CreateSetIterator](https://tc39.es/ecma262/#sec-createsetiterator)
  and [CreateMapIterator](https://tc39.es/ecma262/#sec-createmapiterator)
  (a fresh entry array per step), the
  [%IteratorPrototype%](https://tc39.es/ecma262/#sec-%iteratorprototype%-object)
  (its `[Symbol.iterator]` returns the iterator; no `return`),
  [IteratorBindingInitialization](https://tc39.es/ecma262/#sec-runtime-semantics-iteratorbindinginitialization)
  of a rest element and
  [ArgumentListEvaluation](https://tc39.es/ecma262/#sec-runtime-semantics-argumentlistevaluation)
  of a spread;
- [InstanceofOperator](https://tc39.es/ecma262/multipage/ecmascript-language-expressions.html#sec-instanceofoperator)
  (a static `[Symbol.hasInstance]` called, its result converted by
  `ToBoolean`), [Private Names](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-private-names)
  and [PrivateFieldGet](https://tc39.es/ecma262/multipage/ordinary-and-exotic-objects-behaviours.html#sec-privatefieldget)
  (a private name a key of its own, a missing slot a throw),
  [ClassStaticBlockDefinition](https://tc39.es/ecma262/multipage/ecmascript-language-functions-and-classes.html#sec-class-definitions)
  evaluation, and the `try` statement's completions (a `break` or
  `continue` running each `finally` it leaves).

**Used for** the meaning of every calculus step and every host row of the
trust surface; checked by review and `#guard` tests against node, not proved.
**Discussed in** [ECMA-CONNECTION](ECMA-CONNECTION.md),
[DESIGN: the model in brief](DESIGN.md#the-model-in-brief),
[DESIGN: trust surface](DESIGN.md#trust-surface),
[SEMANTICS: operational language](SEMANTICS.md#operational-language),
[PROGRAM-TYPING: async functions and await](PROGRAM-TYPING.md#async-functions-and-await),
[PROGRAM-TYPING: loops and spreads over iterables](PROGRAM-TYPING.md#loops-and-spreads-over-iterables),
[PROGRAM-TYPING: patterns](PROGRAM-TYPING.md#patterns),
[PROGRAM-TYPING: classes](PROGRAM-TYPING.md#classes),
PROGRAM-TYPING's callable-object sections (its `[c1]`–`[c7]` links),
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md),
[callables tests](tests/callables/README.md).

### JISET and ESMeta

Jihyeok Park, Jihee Park, Seungmin An and Sukyoung Ryu. *JISET: JavaScript
IR-based Semantics Extraction Toolchain.* Proceedings of the 35th IEEE/ACM
International Conference on Automated Software Engineering (ASE 2020),
pp. 647–658, 2020.
[doi:10.1145/3324884.3416632](https://doi.org/10.1145/3324884.3416632).
ESMeta, JISET's successor, is the ECMAScript specification metalanguage and
toolchain at [github.com/es-meta/esmeta](https://github.com/es-meta/esmeta).

**Candidate** for the mechanized ECMA-262 semantics M of a connection: it
extracts the semantics from the specification's own algorithm text and
covers promises and async.
**Discussed in** [ECMA-CONNECTION: the pieces of a connection](ECMA-CONNECTION.md#the-pieces-of-a-connection),
[cost](ECMA-CONNECTION.md#cost-roughly) (`89be3129`).

### Bodin et al. 2014 (JSCert)

Martin Bodin, Arthur Charguéraud, Daniele Filaretti, Philippa Gardner, Sergio
Maffeis, Daiva Naudžiūnienė, Alan Schmitt and Gareth Smith. *A trusted
mechanised JavaScript specification.* Proceedings of the 41st ACM
SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2014),
pp. 87–100. [doi:10.1145/2535838.2535876](https://doi.org/10.1145/2535838.2535876).

**Context.** A Coq specification of ECMAScript 5 with a certified reference
interpreter; an alternative, hand-written route to M, which predates promises.
**Discussed in** [ECMA-CONNECTION: the pieces of a connection](ECMA-CONNECTION.md#the-pieces-of-a-connection).

## Promises and flattened types

The nested-promise case: resolution adopts a thenable, so no realm promise is
fulfilled with one, and a generic signature is truthful at `Promise<T>` only
for a non-thenable `T`. These issues discuss the same fact from the ReScript
and TypeScript sides. It is used in
[ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises),
[PROGRAM-TYPING: async functions and await](PROGRAM-TYPING.md#async-functions-and-await)
and the promise row of [DESIGN: trust surface](DESIGN.md#trust-surface)
(`6ed4c72c`, `395ccd5f`, `89be3129`).

### ReScript 5707

Cristiano Calcagno (cristianoc). *Explore ideas about flattened types.*
rescript-lang/rescript issue #5707, opened 2022-09-29.
[github.com/rescript-lang/rescript/issues/5707](https://github.com/rescript-lang/rescript/issues/5707).

Cited as ReScript #5707 in [ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises).

**Used for** the notion of a flattening constructor, $c\langle
c\langle t\rangle\rangle = c\langle t\rangle$ at run time (nullable values,
promises), and the conclusion that a generic signature is truthful at
$c\langle T\rangle$ only for $T$ outside $c$'s image.

### ReScript 5709

Cristiano Calcagno (cristianoc). *Safe promises.* rescript-lang/rescript pull
request #5709, opened 2022-10-01, merged.
[github.com/rescript-lang/rescript/pull/5709](https://github.com/rescript-lang/rescript/pull/5709).

**Context** for making promise types sound against thenable adoption.
**Cited in** [ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises).

### ReScript 6433

dodomorandi. *Should we make async/await work on "thenables"?*
rescript-lang/rescript issue #6433, opened 2023-10-11.
[github.com/rescript-lang/rescript/issues/6433](https://github.com/rescript-lang/rescript/issues/6433).

**Context** for `%Await%` refusing a non-promise object operand: `await`
calls an object's callable `then`
([PROGRAM-TYPING: async functions and await](PROGRAM-TYPING.md#async-functions-and-await)).
**Cited in** [ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises).

### ReScript 2345

Hongbo Zhang (bobzhang). *sound js promise.* rescript-lang/rescript issue
#2345, opened 2017-12-10.
[github.com/rescript-lang/rescript/issues/2345](https://github.com/rescript-lang/rescript/issues/2345).

**Context**: the early statement that JavaScript promises cannot be typed
soundly at every type parameter. **Cited in** [ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises).

### ReScript 5211

praveen-kumar-rr. *Promise nested inside an option is throwing error.*
rescript-lang/rescript issue #5211, opened 2021-07-09.
[github.com/rescript-lang/rescript/issues/5211](https://github.com/rescript-lang/rescript/issues/5211).

**Context**: a run-time witness of two flattening constructors (option and
promise) composed.

### TypeScript 27711

delautour. *Promise<Promise<T>> cannot exist in JS.* microsoft/TypeScript
issue #27711, opened 2018-10-11.
[github.com/microsoft/TypeScript/issues/27711](https://github.com/microsoft/TypeScript/issues/27711).

**Context**: the nested type TypeScript admits and JavaScript never produces. **Cited in** [ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises).

### TypeScript 59111

eps1lon. *Nested Promise not automatically unwrapped.* microsoft/TypeScript
issue #59111, opened 2024-07-02.
[github.com/microsoft/TypeScript/issues/59111](https://github.com/microsoft/TypeScript/issues/59111).

**Context**: a generic instantiation producing the nested type.

### TypeScript 49946

ChrisHamilton91. *Should infer that resolved value of awaited generic Promise
does not extend Promise.* microsoft/TypeScript issue #49946, opened
2022-07-19.
[github.com/microsoft/TypeScript/issues/49946](https://github.com/microsoft/TypeScript/issues/49946).

**Context** for the non-thenable bound on promised type parameters
(`promisedBinders`). **Cited in** [ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises).

### TypeScript 55408

rotu. *Cannot await Thenable.* microsoft/TypeScript issue #55408, opened
2023-08-17.
[github.com/microsoft/TypeScript/issues/55408](https://github.com/microsoft/TypeScript/issues/55408).

**Context** for awaiting a thenable that is not a promise.

### TypeScript 35419

Yogu. *Strict await.* microsoft/TypeScript issue #35419, opened 2019-11-29.
[github.com/microsoft/TypeScript/issues/35419](https://github.com/microsoft/TypeScript/issues/35419).

**Context** for refusing `await` of a non-promise object. **Cited in**
[ECMA-CONNECTION: illustration](ECMA-CONNECTION.md#illustration-nested-promises).

### TypeScript 45350

Ron Buckton (rbuckton). *Adds 'Awaited' type alias and updates to
Promise.all/race/allSettled/any.* microsoft/TypeScript pull request #45350,
merged 2021-09-10.
[github.com/microsoft/TypeScript/pull/45350](https://github.com/microsoft/TypeScript/pull/45350).

**Context**: TypeScript's `Awaited<T>`, which `Promise.resolve` and
`Promise.all` are declared with; the model reads them through
`%AsyncReturn%` and `%PromiseAll%` instead.
**Discussed in** the `Promise.resolve`/`Promise.all` rows of DESIGN before
`6ee739f8` (`355a9ecb`); the intrinsics are in
[PROGRAM-TYPING: async functions and await](PROGRAM-TYPING.md#async-functions-and-await).

## Tools and prior checkers

### SKJS

SkipLabs. *SKJS*, a checker for a sound subset of TypeScript, this
repository ([github.com/SkipLabs/skjs](https://github.com/SkipLabs/skjs)).

**Used as** the claim producer whose results the pipeline checks, frozen at
the tag `skjs-frozen`. Its soundness corpus and ledger (the issue reports
under `docs/deep-dives/issues/` and `docs/ledger.yaml` at `bf20814b`, and the
mathematical audit `docs/skjs-type-soundness.tex`) supplied the witnesses the
calculus reproduces.
**Discussed in** [DESIGN: SKJS is frozen](DESIGN.md#skjs-is-frozen),
[SKJS-COVERAGE](ocaml-producer/SKJS-COVERAGE.md),
[INTERSECTIONS](INTERSECTIONS.md), [skjs-improvement](../docs/skjs-improvement.md),
[TypeScript soundness holes](../docs/typescript-soundness-holes.md); the
corpus table in DESIGN before `6ee739f8` (`355a9ecb`).

### TypeScript

Microsoft. *TypeScript* ([typescriptlang.org](https://www.typescriptlang.org/)),
its checker and its library declarations (`lib.*.d.ts`), and the handbook's
[More on Functions](https://www.typescriptlang.org/docs/handbook/2/functions.html).

**Used for** name resolution, computed and contextual types, and the library
contracts the overlays filter: a trusted tool of the pipeline.
**Discussed in** [DESIGN: principles](DESIGN.md#principles),
[DESIGN: trust surface](DESIGN.md#trust-surface), PROGRAM-TYPING's `[c5]`
link.

### Lean 4

Leonardo de Moura and Sebastian Ullrich. *The Lean 4 theorem prover and
programming language.* CADE-28, LNCS 12699, pp. 625–635, Springer, 2021.
[doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37).

**Used as** the authority: the model, the rules, their soundness proofs and
the checker that consumes producer evidence.
**Discussed in** [README](README.md), [DESIGN: what "verified" means](DESIGN.md#what-verified-means).
