# Independent verification of type claims

The pipeline checks type claims about TypeScript programs with a small,
independently justified consumer. A producer proposes the types of a
module's expressions and the environments at its program points; Lean checks
that those claims are derivable in a calculus whose rules are proved sound
against an execution model. The OCaml producer, which reads TypeScript's own
declarations, supplies the pipeline and corpus claims. No producer is trusted.

This document owns the principles, architecture, trust surface and lasting
decisions. [The source model](SOURCE-MODEL.md) connects source constructs to
the calculus. [The fragment boundary](SOURCE-FRAGMENT.md) states the restrictions
the source pipeline enforces. [The work ledger](WORK.md) records milestones,
completion conditions and open investigations. The [documentation map](README.md#documentation-ownership) assigns
them: terms, values and execution to [SEMANTICS](SEMANTICS.md), types and
subtyping to [POSITIVE-TYPES](POSITIVE-TYPES.md), program and source rules to
[PROGRAM-TYPING](PROGRAM-TYPING.md), wire formats to
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) and [SOURCE-CLAIMS](SOURCE-CLAIMS.md).
How much of SKJS's own test suite verifies, and what stops the rest, is
[SKJS-COVERAGE](pipeline/SKJS-COVERAGE.md). Works the design draws on
are cited from [REFERENCES](REFERENCES.md).

## Principles

**Utility justifies complexity.** Support ordinary, useful programs well;
support for every JavaScript corner case is not an objective. When a rarely
useful behavior would require disproportionate machinery, prefer a simple
semantic restriction with a clear refusal. State the restriction explicitly,
enforce it, and require external code to respect it wherever the result relies
on that assumption. This is a choice of admitted language, not permission to
ignore behavior of an admitted program or erase a difficult contract. The
ordinary-array construction restriction is one such trade-off. A motivating
ordinary program is not a corner case merely because its implementation is hard.

**Soundness is no wrong values.** An accepted unit, run in any environment
meeting its inputs, evaluates to a value of its declared type, takes a step,
or throws a value: it never gets stuck and never produces a value outside its
type. A throw is an outcome, as in ML-style soundness with exceptions
([Wright and Felleisen 1994](REFERENCES.md#wright-and-felleisen-1994)): a type
says what a value is, never that none is thrown. Termination is not claimed.
What is refused because it could produce a wrong value stays refused; what
would only throw is admitted (`BigInt(1.5)`, a bigint division by zero,
`toString(radix)` out of range).

**Types express what is actually true.** A type states what holds of every
value JavaScript can give it, no more. `s[i]` is `string | undefined`, since
a string's length is not tracked; a number's falsy part is all of `number`,
since no type names `{0, -0, NaN}`; an array may own keys its type does not
name; a fresh literal owns exactly its written keys, and a record type is
open. Where TypeScript states more than is true, the model states less, and
the program must justify the rest.

**Lean is the authority; OCaml proposes.** Claims, contracts, instances,
loop heads and construction hints are proposals. Lean checks every proposal
used to establish an extracted obligation against the source it reads itself. Search strategy, fuel and hints
decide whether evidence is found, never what acceptance requires. A search
that finds nothing leaves a unit *unverified*, never disproved. The consumer
must stay usable with evidence from any producer.

**One mechanism, not two.** A new source form reuses the rules that exist:
every guard is a tag test; every array is one store and one prototype; every
intersection is one meet; every body, function or closure, is graph code;
every library contract is read through one overlay mechanism; one headline
theorem covers every accepted unit. A second typing path for a case the first
covers is not added, and a form that needs one waits until the first is
extended.

**Follow TypeScript where it is sound; refuse, with a reason, where it is
not.** The source is TypeScript and the pipeline reads it as TypeScript's
checker does: names resolve as it resolves them, computed types mean what it
computes, contextual types are its. Where TypeScript's rule is unsound
(method bivariance, covariant mutable arrays, implicit index signatures,
width subtyping into optional fields, narrowing an open record by `in`), the
form is refused with the specific reason, located at the source. Where
TypeScript refuses what would merely throw (arithmetic mixing a number and a
bigint), the pipeline follows it too: its rule is sound and the program is
almost surely a bug.

**Minimal, stated trust.** Every assumption is named and enters the safety
theorem as a premise: an input slot of the unit at a declared type, or a
listed property of the host. The [trust surface](#trust-surface) lists all of
them. Library contracts are TypeScript's declarations filtered by reviewed
overlays that record the text they were reviewed against, so a changed
library is refused rather than trusted silently.

**Evidence is syntax-directed.** Entry claims attach to execution points,
and expression claims to sites within those points; loop heads and joins are supplied, and every incoming edge
must justify them. The checker infers no invariant and computes no join. What
a producer states at a program point is exactly what is checked there, and
source maps, which say how a node reads in the source, never reach evidence.

## Architecture

The pipeline has two distinct jobs: proposing type information and checking
whether that information follows from the program. It also has two stages of
lowering, meaning translation into a simpler program representation. The first
fixes execution order without needing types; the second constructs the typed
calculus program that the verifier checks.

![Architecture: source parsing, Lean execution plans, OCaml type proposals, Lean typed elaboration, evidence search and certificate checking.](diagrams/architecture.svg)

[Open the full-size diagram](diagrams/architecture.svg). Amber marks translation
whose correspondence with JavaScript is reviewed and tested. Blue marks
replaceable proposals. Green marks checking with a proved safety consequence
for the extracted calculus program.

### Stages

1. **Parse source and collect declarations.** The TypeScript front end reads
   source using the project's strict compiler configuration. It emits a
   **Fragment**, a syntax tree for the supported source constructs, and a
   declaration graph describing the types and external values the source uses.
   Parsing includes source rewrites such as representing `switch` with labeled
   blocks. These rewrites must preserve JavaScript behavior.
2. **Build execution plans in Lean.** Lean derives a statement graph and
   schedules for expression evaluation and binding. A graph edge records where
   execution can go, including a transfer through `finally` or an exception
   handler. Expression schedules record operand order and conditional
   evaluation. Binding schedules record parameter defaults and destructuring.
   These plans depend on source syntax, before the producer supplies claims.
3. **Propose types in OCaml.** The producer follows the exported plans and
   computes environments along their edges. An **environment** records the
   proposed types of local bindings and facts about their current contents.
   At a loop head, the producer seeks an invariant that is preserved by the
   loop's back edges. Source syntax supplies contextual types, generic-call
   inference and other type information. The output is a claims document.
4. **Elaborate the typed program in Lean.** Lean reconstructs the execution
   plans from the Fragment. It checks claim identities, interprets annotations
   and proposed types, and elaborates operations into a **calculus graph**:
   the program over which typing and safety are defined. This stage can depend
   on types, for example when choosing how to read an array element or a field.
   It produces a request containing that graph and the obligations it must meet.
5. **Search for evidence.** Lean's search procedure proposes a **certificate**,
   a finite description of typing and subtype derivations for the request.
   Search can fail or exhaust its budget even when the obligations hold.
6. **Check the certificate.** The verifier checks the proposed derivations
   against the exact extracted request. Success establishes safety for that
   calculus program under its stated input and host assumptions.

The OCaml producer analyzes the early execution plans; it does not need a
finished typed calculus graph. This ordering avoids the circularity in which
expression lowering needs types that the producer has yet to infer. The
exported execution-plan document is an input to proposal generation. Acceptance
uses the plans Lean reconstructs from source, rather than trusting that document.

Implementation entry points are [the parser](tools/fragment-parse.mts),
[the execution-plan writer](lean/Verification/Source/FlowJson.lean),
[the OCaml producer](ocaml-producer/README.md),
[typed extraction](lean/Verification/Source/SourceExtraction.lean) and
[claim checking](lean/Verification/Source/SourceClaimJson.lean).
[LANGUAGES](LANGUAGES.md) maps each representation to its definitions.

### Claims and the claim reader

A **claim** is a proposed type or state description. It becomes an obligation
where extraction uses it. A **source span** is a pair of offsets locating
syntax in the source file. An **execution point** identifies a node in a body's
statement graph. One span can occur at several points: a finalizer, for example,
can execute on a return path and on a loop exit.

Entry claims are identified by execution point. Expression claims use both a
point and a span, since one statement can evaluate several expressions.
Mutable declarations have separate **storage contracts**, the types every
value written to their cells must satisfy. A point's current-content claim
may be narrower than that contract; it does not change what later writes allow.
The [claims protocol](SOURCE-CLAIMS.md) defines the identities and encodings.

Lean validates point ownership and source-site membership, rejects duplicate
identities, and requires the claims needed by extraction. It reads source
annotations independently. A function's proposed signature must agree with its
annotation; a closure must justify the signatures claimed for it and meet its
written annotation. An unused display claim is not thereby certified: acceptance
covers the extracted program's required obligations, not every candidate a
producer might include at a valid site.

Types are interpreted through a common graph of recursive type equations.
A **type label** names a type in that graph; the label's number or spelling
has no independent meaning. Comparisons use the types denoted by labels.
[RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md) defines that interpretation.

The extractor also writes a **source map** linking calculus nodes and local
slots to source descriptions. Reports use it to locate failures. It is
diagnostic metadata and supplies no evidence for acceptance.

### Search

Search tries to construct evidence for each required typing or subtype
judgment. Some operations have evidence determined by their elaboration;
others require searching among types and rules relevant to the request.
Recursive subtype comparisons use finite certificates whose dependencies the
checker validates. The details belong to
[recursive subtyping](RECURSIVE-EQUATIONS.md#4-subtyping) and
[evidence construction](SOURCE-ELABORATION.md#producing-evidence-from-supplied-claims).

Search is replaceable. It cannot change the source requirements, and an
unsuccessful search is not evidence that a program is unsafe. The OCaml
producer's `--explain` output and TypeScript diagnostics can help explain a
failure in the report; neither is a premise of certificate checking.
[Failure classification](OBLIGATION-DIAGNOSTICS.md) specifies these distinctions.

### The pipeline entry point

`pipeline/verify-source.mts` runs parsing, execution-plan export, OCaml proposal
generation, Lean evidence search and Lean checking. Each subprocess has a log
and a time limit. `--project` selects the strict TypeScript project configuration.
The case suite, coverage run, corpus and report viewer use this entry point.

The outcome is one of:

- **verified**: certificate checking accepted the extracted request;
- **unsupported**: source processing or proposal generation refused a construct;
- **unverified**: search or checking did not establish the required derivation;
- **exhausted**: a verification resource budget was reached before the
  obligation could be decided;
- **error**: a subprocess failed or exceeded its time limit.

A whole-file failure can precede claim generation. When claims exist, the corpus
and report viewer can rerun checks per code unit to identify which unit failed.
Neither an unsupported result nor an infrastructure error is a safety verdict.

### What "verified" means

`SourceClaimJson.checkJson_safe` connects successful source-claim checking to
safety of every certified calculus request. Each **code unit** is a function
or module-initialization body. Its inputs include parameters and the module,
imported and host values it uses.

For inputs that satisfy their types and a heap that satisfies its storage
contracts, the extracted program does not get stuck or return a value outside
its result type. It may throw or run forever. Generic units have this guarantee
at every admissible assignment of their type parameters. All extracted plans
pass through the checked conversion to `CertifiedPlan`; acceptance cannot
silently omit an unhandled kind of plan.

This is a theorem about the extracted calculus program. Correspondence between
source JavaScript and that program, the interpretation of annotations, and the
host's compliance with assumed contracts remain review obligations. The
[trust surface](#trust-surface) lists them. The proofs use no `sorry` and no
project axioms; that fact does not itself establish source correspondence.
See [the semantic guarantee](SEMANTICS.md#what-the-checked-development-establishes)
and [trust-reduction options](TRUST-REDUCTION.md).

### Modules and code units

The module is the unit of source verification. Its top-level functions and
initialization body have separate obligations, so a failure can name the
responsible code unit. Initialization evaluates constants, classes, enums and
top-level statements in source order; class constructors and methods receive
their own code checks.

A module function is available at its source signature. A module constant is
available at its annotation or its checked initializer claim. Initialization
refuses calls that could read a constant before it is initialized. Imports,
ambient declarations and globals enter at assumed declared types.
[Module rules](SOURCE-CONTRACTS.md#modules-and-code-units) specify these interfaces.

Each unit's theorem assumes the signatures of the module values it reads.
A Lean theorem composing these unit guarantees for an entire module execution
is not available. `--function` selects a unit while retaining the module scope;
it does not establish the omitted units' obligations.

### Generic bodies

A generic type parameter denotes an arbitrary type satisfying its bound.
The calculus represents it with a **parameter row**, a type-graph entry whose
interpretation is supplied when the generic is instantiated. Typing rules may
use its declared bounds but cannot inspect that arbitrary interpretation.
`Parametricity.accept_reassign` proves that accepted evidence remains valid
when the interpretation changes.

A bounded parameter such as `T extends A` is interpreted as the intersection
of its arbitrary type with `A`. A bound `U extends T` relates the parameters
by the same intersection construction. A generic call proposes a substitution
for the parameters; Lean checks the instance and its bounds. Generic classes
and closures use this mechanism too.

A **type scheme** is a callable contract with universally quantified type
parameters. A generic closure is checked at its scheme's signatures with
fresh parameter rows, including the types of captured values. It is checked
for all admitted instances, rather than only for calls observed in the source.
See [generic typing](CALLABLES.md#overloads-polymorphism-and-binding) and
[parameterized equations](RECURSIVE-EQUATIONS.md).

### Closures are graph code

A closure's body is a calculus graph with its own certificate. Its entry receives
a receiver, arguments and captured values. A mutable capture is the identity
of its cell; its creation-time contents cannot be assumed when the closure
later runs. Each claimed call signature must be justified by the body.

Parameter defaults execute at entry in source order. A rest parameter collects
surplus arguments into fresh array storage. Constructors have construct
signatures, checked against constructor code; callable objects combine code
with property storage. `.bind` creates a forwarding value with a retained
receiver and arguments. These forms share the model's call and code checking
rather than relying on a special source-level acceptance test.

The creating body's certificate identifies the checked closure code and its
captures. [Graph code](SEMANTICS.md#graph-code) and
[call rules](SOURCE-ELABORATION.md#source-closures-and-their-annotations) define the entry frames and obligations.

## Trust surface

Everything the safety theorem does not establish. Each assumption enters as
a premise: an input slot of the unit at a declared type (`EnvOk` over the
unit's inputs, in the premise of `checkJson_safe`), a property of the host
the model's reading of an operation relies on, or the correctness of a
trusted tool. Where an item is stated in code, that code is the reviewed
text.

Equation well-formedness and inclusion are proved over the lowered equations
([validation and soundness](RECURSIVE-EQUATIONS.md#6-trust-and-acceptance)).
Interpreting source annotations as those equations is part of source extraction's
trusted obligation below.

**Trusted tools.**

| Assumption | Where it is stated |
| --- | --- |
| The parser represents the source faithfully: it admits only the fragment, and its lowerings (unbraced arms, `switch`, `for`, templates, enums, optional chains, async forms, patterns, dead code, a shadowing local's renaming by the declaration TypeScript binds each reference to, a `let` nothing writes as a `const` (a `for...of` or `for...in` head's too), a `for...in` whose body reads the entry at its key before anything that could change it runs as the steps of `%Iterate:ForIn%` with that read the step's value (`forInEntryReads`: the object's name written nowhere in the outermost function holding the loop, and a chain of reads from it unchanged by a body that runs no code and writes no property), a written `let` pattern as a `const` pattern and `let`s, a static block as a closure called at once, `instanceof` of a class with a static `[Symbol.hasInstance]` as its call, `k in o` with a key TypeScript types as other than string literals as `%HasProperty%(k, o)`, `xs[k]` of an array at a `number` key as `%ElementAt%(xs, k)`, a private name as its member's symbol, a rest parameter's alias equation, the iterator protocol of a program's iterable in a `for...of`, a spread and an array pattern, with its closing region) preserve JavaScript's execution. | `tools/fragment-parse.mts`, `fragment.mts` |
| Source extraction preserves control flow, lexical binding, evaluation order and annotations: which program point a claim is attached to is unproved. No source-to-graph preservation theorem exists. A key-adding write is lowered as a copy only where the object is its local's own and unreached (`growSites`, a syntactic analysis): that JavaScript's write in place and the copy agree rests on it. | `Source/Fragment.lean`, `Source/SourceFacts.lean`, `Source/SourceExtraction.lean` |
| Decoding represents the submitted AST, declarations, claims and evidence faithfully. | `RequestJson.lean`, `SourceClaimJson.lean` |
| TypeScript's checker resolves each name to its declaration in the file's project, whose strict `tsconfig.json` (paths, links, library set, type packages) reflects the real build; a TypeScript error in a collected declaration or on an import it passes through refuses the graph. The parser checks TypeScript read the bytes it parsed. | `tools/declaration-graph.mts` |
| TypeScript's evaluation is trusted as its resolution is: a computed type (`typeof`, `keyof`, `T[K]`, template literal types, primitive intersections, mapped keys) means what its checker computes; an enum member's value is `getConstantValue`'s, which its emit writes; a `const enum` read is the member TypeScript binds it to; global member and overload resolution selects which declared signatures are assumed. | [`tools/computed-types.mts`](tools/computed-types.mts), `declaration-graph.mts` |
| The execution model agrees with JavaScript on the supported operations, including that Lean's compiled `Float` operations are IEEE-754's and `Float.pow` is C's `pow`, which `binop` corrects where `**` differs. | `Semantics/Calculus.lean`; [ExecutionModelTests.lean](lean/Verification/Tests/ExecutionModelTests.lean) runs the model where no proof and no pipeline case compares it with JavaScript (NaN, the prototype chain, evaluation order, stuck subterms, reentry), and `pipeline/test.mts` runs the examples under Node beside their outcomes |
| Lean's kernel, its compiler (including the `@[csimp]` replacements, each proved equal to its definition) and the executed verifier binary are correct. | — |

**Assumed values.** Each is an input slot of the units that use it, at its
declared or stated type; nothing checks the code behind it, and each may
throw, which safety admits, but never return a wrong value.

| Assumption | Where it is stated |
| --- | --- |
| An imported value meets its declaration; a function declared with overloads meets every overload. | `IMPORT`, `OVERLOADS` in [SOURCE-CONTRACTS](SOURCE-CONTRACTS.md#imported-ambient-and-global-values) |
| An ambient declaration (`declare function`, `declare const`, `declare class`) holds of the value the environment supplies under that name; the declaration document lists it with the specifier `ambient`. | `AMBIENT`; `collectDeclarations` |
| A global variable outside the standard library (Node's `process`) meets its declaration at the members and calls the module selects, from the project's type packages, and no code the module does not see reassigns it. | `GLOBAL`; `selectGlobal` |
| Each standard library global meets its reviewed overlay entry: `console.log`; `BigInt`; `Symbol`, `Symbol.for`, `Symbol.keyFor` and five well-known symbols; `String` of a primitive; `Object.keys`, `Object.values`, `Object.entries` (and the generic two at a dictionary); `new Array()`; `Array.isArray` and `Array` as `instanceof`'s operand; `new Error(m)`; `new Set`, `new Map` of an array, `new Date` of nothing, a primitive or components, `Date.now`; the `Promise` statics and constructor, through the intrinsics below; `JSON.parse` of a string and `JSON.stringify` of a `JsonValue`. | `globalsOverlay` in [`tools/library-globals.mts`](tools/library-globals.mts); [rules](SOURCE-CONTRACTS.md#library-globals) |
| `Array.prototype` meets `ArrayProto`: its natives `forEach`, `map`, `reduce` and `reduceRight` (with an initial value), `every`, `some`, `filter`, `slice`, `join`, `toString`, `indexOf`, `lastIndexOf`, `includes`, `at`, `find`, `findIndex`, `sort`, `push`, `pop`, `shift`, `unshift`, `reverse` and `[Symbol.iterator]` meet the reviewed overlay contracts, at the listed receiver, without `thisArg`; result construction uses the ordinary-array invariant; `map` promises a sparse result for unrestricted callbacks and a readable result, freshly dense, for a dense input and certified heap-preserving callbacks; `find`/`findIndex` admit missing callback values unless the callback has that guarantee, and `join`, `toString` and default `sort` restrict elements to the recursive standard-conversion contract, with own conversion hooks excluded; comparator sorting checks the supplied callback. Units allocating arrays read it from the input slot `[[Array.prototype]]`. | `overlay` in [`tools/array-prototype.mts`](tools/array-prototype.mts) |
| `String.prototype`, `Number.prototype`, `BigInt.prototype` and `Boolean.prototype` meet `StringProto`, `NumberProto`, `BigIntProto` and `BooleanProto`, each member an own property of that prototype (`split`, `replace`, `replaceAll` stated at a string pattern; `toLocaleString` without `options`), read from the slot `[[String.prototype]]` and so on. | `primitiveOverlay` in `tools/array-prototype.mts` |
| `Set.prototype`, `Map.prototype` and `Date.prototype` hold the listed natives, unmodified (`keys`, `values` and `entries` giving a host iterator of the collection). | `interfaceOverlay` in `tools/array-prototype.mts` |
| The intrinsics meet their signatures: `%Await%` yields what a native promise settles to, or a resolution-qualified input's observation, or throws its rejection; `%AsyncReturn%` resolves an async return to a resolution-qualified input's result and `%AsyncComplete%` fulfills completion with `undefined`; `%PromiseResolve%` preserves a native promise through its constructor identity path or yields a promise of a resolution-qualified input's observation; `%Stable%` is the stable non-thenable family those descriptors are relative to; `%PromiseAll%` (`Promise.all`), `%PromiseReject%` (`Promise.reject`), `%NewPromise%` (`new Promise`, calling its executor at once); `%Iterate%` steps an array's iterator, reading the current length at each step; `%Iterate:string%` a string's, by code point; `%Iterate:Set%` a `Set`'s, in insertion order; `%Iterate:Map%` a `Map`'s, a fresh `[key, value]` array per entry; `%Iterate:Iterator%` a `SetIterator` or `MapIterator`, which is its own iterator; `%Iterate:ForIn%` the keys a `for...in` over a dictionary visits, its own, a fresh `[key, value]` array per key with the value it holds under the key at the step; none of these iterators has a `return`; `%Spread:K%` is the fresh array of what `%Iterate:K%`'s step yields until it ends; `%RestFrom:k%` is the fresh array of an array's elements from `k` to its current length, as its iterator yields them after a pattern's `k` elements; `%ForIn%` gives the keys a `for...in` visits, strings; `%HasProperty%` answers `k in o` for a key TypeScript types as other than string literals, as the host's lookup does; `%ElementAt%` reads `xs[k]` of an array at a `number` key as the host does: the element at an index below the length, an own property at another numeric key, else `undefined`. The job queue and a promise that never settles are not modelled. | [`tools/intrinsics.mts`](tools/intrinsics.mts); [async](SOURCE-CONTRACTS.md#async-functions-and-await) |
| A thrown value is a value, of any type. | `Thrown` in `Safe` (`Semantics/Safety.lean`) |
| The runtime with the sound service binding meets its declarations: `InputCollections.get(definition)` returns the collection built from that definition at its types, or throws; resources are constructed with the request's `Json` parameters. | `pipeline/skip-runtime-sound-binding/` |
| In the SKJS test environment, SKJS's import stubs describe the modules a test imports, and `skjs-environment.d.ts` the host's `process`, `__SKJS_show`, `__SKJS_show_expanded` and `StringRecord<V>` as SKJS's builtins stub does, with the ES2022 library and no DOM (`console` restated); `Closed<T>` and `SKJS_Ignorable<T>` are read as `T`; an ambient class's untyped field is a readonly `unknown` field. These are premises of the coverage result only. | `pipeline/skjs-environment/`; `STUB`, `ENV` |

**Assumed of the host.** Properties of every value a unit receives, on which
the model's reading of an operation relies.

| Assumption | Where it is stated |
| --- | --- |
| The caller contract: a value conforming to a structural annotation (a parameter, an import, a library result) is a plain data object, its stated string-keyed fields own enumerable data properties, not accessors or proxies, which a spread copies, an optional field `f?: T` is absent or holds a `T` (the exact reading SKJS defines, as `exactOptionalPropertyTypes` does; a present `undefined` is stated as `f?: T | undefined`), and a class instance owns its private slots, keyed by their private names; a conforming function respects its contract across every future heap, callback effects included. Two such parameters may alias. `Error`'s `message` is the exception, held on a prototype the model gives it. | `RequestJson.verify_safe` quantifies over environments meeting the input types |
| A value whose trusted declaration types it `Function` has call or construct code. | [`Function`](SOURCE-CONTRACTS.md#library-types) |
| A value TypeScript types as `Set<T>`, `Map<K, V>`, `SetIterator<T>` or `MapIterator<T>` that a loop or spread iterates is the host's: its iterator is the realm's, and the prototypes it inherits (`%IteratorPrototype%` included) hold no `return` and are unmodified. Assumed of every such value a program receives; the fragment builds none but through the host: a `Set`'s and a `Map`'s type state their `[Symbol.toStringTag]`, a well-known symbol key no literal or class of the fragment writes, and no annotation of the fragment states a `SetIterator` or `MapIterator`. A host iterator a program's protocol steps (an array's, as an `Iterable<T>`) likewise has no `return` along its chain. | the iteration intrinsics' pick, `iterationKind` in `tools/declaration-graph.mts`; `writtenSymbol` in `tools/fragment-parse.mts` |
| Every object owning the array store key is a JavaScript array: every object the model allocates, and assumed of every object a program receives. `Array.isArray` is the native test. For `instanceof Array`, every array a program receives is of its realm and no object but an array inherits from `Array.prototype`. | `isArray` ([SEMANTICS](SEMANTICS.md#operational-language)); the `Array` entries of `library-globals.mts` |
| The array invariant: every object a unit receives at a record or dictionary type that owns the array store key is an array of the realm: its store may be sparse, it holds `Array.prototype` (meeting `ArrayProto`, which reads no parameter row), and it owns neither `constructor`, `then` nor any key declared by `ArrayProto`. Proved of every object the unit allocates; assumed of every value it receives, as the arrays it receives at array types already are. Nothing is assumed of a value at `unknown`, and no class invariant: an object whose prototype chain holds a class's prototype need not have the class's fields. | `realmInvariant` in the meaning of record and dictionary rows, so `EnvOk` in the premise of `checkJson_safe` ([SEMANTICS](SEMANTICS.md#the-array-invariant)) |
| An array a program receives owns neither `constructor`, `then` nor any key declared by `ArrayProto`. The realm keeps standard `Array.prototype.constructor`, `Array[Symbol.species]` and their prototype links; external code preserves that behavior across calls. | the own-key exclusion bound includes `constructor` and `then` (`RequestJson.arrayExcludedKeys`); standard native construction and the absence of inherited `then` are host assumptions |
| An array a program receives owns, at a canonical numeric key that is no index below its length, only a data property holding a value of its element type, as `Array<T>`'s declared `[n: number]: T` says; the realm's `Array.prototype` owns no numeric key. What `%ElementAt%` reads rests on it; the arrays the model allocates own no such key. | `%ElementAt%` in `tools/intrinsics.mts` |
| The model's reserved keys (the store key `[]` and every name in double brackets) are spelled by no source key, and an object a program receives is represented with its own keys apart from them. | `Fragment.sourceKey`, `reservedSourceKey` |
| `Object.prototype`, `Array.prototype` and `Function.prototype` own no string key but those `inKeyRefusal` lists (node's `Object.getOwnPropertyNames`), none enumerable, so a `for...in` over a plain object visits its own keys only; `String.prototype`, `Array.prototype` and `Object.prototype` own no numeric key; `String.prototype` owns no `[Symbol.split]` or `[Symbol.replace]`; `Object.prototype` has no `toJSON` or `then`. | `inKeyRefusal` in `Source/Fragment.lean`; the overlay comments |
| Distinct JavaScript objects have disjoint field locations, which is how `===` on objects with a field is answered; only allocation creates an object value. | `Arith.eq` |
| Code outside a unit adds keys to an object it holds at a writable index only at that index's contract and only keys of its class, none the model keeps for itself (`[[proto]]`, `[]`: an object owning a property JavaScript spells so is one the model does not represent, as for any object it meets). The calculus has no step that adds a key; a program adds one by copying its own object. Every type the unit may hold such an object at stays true of it with the key: its own-key bounds by `ownKeysT_keeps` and `covers_writable_keeps` (a writable index some value meets is met only through bounds that keep its class; a literal meant for one is allocated at it, `allocDict`), its fields, views, indexes and optional fields by the covering premises a writable target states. | [index signatures](SOURCE-MODEL.md#writable-string-index-signatures) |
| The model's spread and `Object.assign` copy string keys only, where JavaScript's also copy an own enumerable symbol-keyed property: the copy's type states no symbol key and is open, so no typed read names one, and a key test for a symbol is the host's `%HasProperty%`, which answers from JavaScript's object and narrows nothing. | [object literals](SOURCE-MODEL.md#object-literals); [`in`](SOURCE-ELABORATION.md#derived-source-forms) |
| The standard `Object.assign`, `Function.prototype.call`, `apply` and `bind` are the intrinsics the parser identifies by lexical provenance; the fragment cannot write those properties. | `tools/fragment-parse.mts` |
| A value of type `Promise<T>` is a genuine native promise with the realm's stable standard prototype, constructor, methods and species. The source contract excludes own replacements of those inherited members through structural aliases. Direct observation retains its fulfilled `T`, which may be an object that later acquires `then`; fresh resolution operations require their stated stable non-thenable result contracts. External code supplies and preserves the same native invariant. | [native promise contracts](SOURCE-CONTRACTS.md#async-functions-and-await); the prototype overlay in `tools/declaration-graph.mts` |

**Not yet proved.** Module composition: a unit's certificate assumes the
signatures of the module values it reads, each certified by its own unit;
the step-indexed argument that they compose is not a Lean theorem
([modules](#modules-and-code-units)).

## Lasting decisions

One line each; the reason is the one the design keeps.

- **Density belongs to a contract, not the realm.** Source `T[]` currently
  requires readability; dense and sparse contracts also exist. Iteration, spreads
  and `.apply` consume that read guarantee; sparse stores need a separate
  `undefined` alternative. `find` needs
  `undefined` even on dense input because callbacks can remove later elements.
- **Arrays own neither `constructor` nor any of `ArrayProto`'s keys.** An exact
  bound would make every tagged array type empty and verify its readers
  vacuously. At a numeric key that is no index, an own property holds an
  element, as `Array<T>`'s number index declares: a read at a `number` key is
  the host's (`%ElementAt%`), an element or `undefined`.
- **A fresh literal has exact keys; an existing record is open.** Only
  allocation establishes absence.
- **A key is added by copying an object nothing else can observe.** Objects
  keep their keys; a write that would change them where another reference
  sees it is refused.
- **Enum types are their value sets.** Any number is not a numeric enum;
  two enums with the same values are one type.
- **`in` tests own keys along the prototype chain the model holds**, and
  refuses literal keys the realm's prototypes hold; a key typed other than
  string literals is the host's test, which narrows nothing.
- **A record or dictionary type is of arrays of the realm where it owns a
  store; `unknown` is every value.** `Array.isArray` narrows a record arm,
  never `unknown`; no class invariant is assumed, so `instanceof` never
  narrows `unknown`.
- **Method members are host-relative, read-only and contravariant in their
  parameters.** Bivariance is refused.
- **Mutable arrays, dictionaries, `Set` and `Map` are invariant.**
- **Readonly optional fields are views that may be absent**; a readonly
  field never meets a writable one.
- **A throw is an outcome.** Trusted steps are assumed to return a value of
  their result or throw, never a wrong value.
- **`await` is a trusted step; an async result is a primitive.** Thenable
  adoption is never modelled.
- **A host iterable's iteration is one intrinsic family, picked by the
  iterable's type**: `%Iterate:K%` per host iterable kind, none with a
  `return`. **A program's iterable runs the iterator protocol** as ordinary
  calls, IteratorClose a closing region that the `finally` machinery
  compiles; generators, which suspend, are not expressed.
- **Library contracts are TypeScript's declarations through reviewed
  overlays**, each entry pinned to the declaration text; nothing is vendored.
- **`Function` is "has call or construct code"**; `object` is every object;
  `{}` is every value but `null` and `undefined`.
- **Closure parameters without a type take TypeScript's contextual type as
  an annotation**, checked like any other; `any` is refused.
- **A module is the unit of verification; obligations stay per code unit.**
- **Statement entries are exact interfaces**; no invariant is inferred and no
  join computed by the checker.
- **A call forgets heap facts.** No reachability or capture analysis is
  justified by the model's open record types.
- **Every guard is a tag test**; strict equality without a singleton narrows
  nothing.
- **Generic bodies are graph requests over parameter rows**, certified at
  every assignment admitted by their source signature.
- **One row per generic application**, lowered from an empty visit.
- **Wire formats carry no version and have one shape**; producers and
  consumers are typed against one declaration.
- **Strings' lengths are not tracked**: `s[i]` is `string | undefined`.
- **Relational comparison admits only operands compared in their primitive
  order.**
- **`Closed<T>` is read as `T`**: less than SKJS's meaning, and true of every
  closed value.
- **A number is its double's bit pattern; a bigint its integer.** Distinct
  spellings of one value are one singleton ([values](SOURCE-MODEL.md#values)).
- **An omitted closure result is the producer's claim**; an annotation adds a
  requirement at the annotated signature and never removes a check.
- **`<T>e` is `e as T`**, and a type reference to a name that is also a function resolves to the type.
- **A type assertion decides nothing**: `e as T` is an obligation that the
  operand meets `T`.
- **Two model laws stay refused**: distributing arrow results over an
  intersection, and collapsing eventually incompatible reference contracts to
  bottom ([retained constraints](SEMANTICS.md#two-retained-design-constraints);
  contrast [Frisch, Castagna and Benzaken 2008](REFERENCES.md#frisch-castagna-and-benzaken-2008)).
- **A type parameter's bounds include those its signature implies; a body
  implies none.** Resolution qualification, implied by `Awaited<T>`, is the
  one implied constraint that is not a subtype bound
  ([implied bounds](SOURCE-CONTRACTS.md#implied-bounds)).
- **`await` and async return are typed through two qualifications.**
  $`X:\mathsf{Awaitable}`$ owns an observation $`X.\mathsf{Observed}`$, and
  $`X:\mathsf{Resolvable}`$ also a result $`X.\mathsf{Result}`$; every
  resolvable input is awaitable. `await` and `Promise.resolve` quantify an
  awaitable $`X`$, async return a resolvable one. A generic parameter takes
  `Awaitable` by `T extends Awaitable`, and `Resolvable` by
  `T extends Resolvable` or by `Awaited<T>` in its signature. A qualification
  restricts which instances are admitted, never the values of $`T`$
  ([async](SOURCE-CONTRACTS.md#async-functions-and-await)).
- **Ordinary graph evidence is certified at every assignment of parameter rows**
  (`Parametricity.accept_reassign`). Qualified body evidence is certified at
  assignments satisfying the signature’s descriptor constraints
  (`RequestJson.verify_qualified_safe_at`).
