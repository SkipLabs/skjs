# Independent verification of type claims

The pipeline checks type claims about TypeScript programs with a small,
independently justified consumer. A producer proposes the types of a
module's expressions and the environments at its program points; Lean checks
that those claims are derivable in a calculus whose rules are proved sound
against an execution model. The OCaml producer, which reads TypeScript's own
declarations, supplies the pipeline and corpus claims. No producer is trusted.

This document states the current design and what comes next: the principles,
the architecture, the model in brief, the trust surface, the fragment's
boundary, the lasting decisions and the open work. It does not restate
rules. The [documentation map](README.md#documentation-ownership) assigns
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
[evidence construction](PROGRAM-TYPING.md#producing-evidence-from-supplied-claims).

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
[Module rules](PROGRAM-TYPING.md#modules-and-code-units) specify these interfaces.

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
See [generic typing](PROGRAM-TYPING.md#overloads-polymorphism-and-binding) and
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
[call rules](PROGRAM-TYPING.md#source-closures-and-their-annotations) define the entry frames and obligations.

## The model in brief

The calculus describes execution, types and the conditions under which a
program may use a value. This section introduces the main concepts;
[SEMANTICS](SEMANTICS.md), [POSITIVE-TYPES](POSITIVE-TYPES.md) and
[PROGRAM-TYPING](PROGRAM-TYPING.md) own the formal definitions and rules.

### Values

Values include JavaScript primitives and allocated objects. Object properties
refer to heap locations. Arrays have element storage; callable objects also
carry call or constructor code. Every allocated object has an identity, including
empty objects and functions, so object equality compares identities.

Primitive operations model the supported JavaScript behavior, including IEEE-754
numbers, bigint arithmetic and string operations.
Literal type `0` includes both positive and negative zero; equality against
`0` keeps or excludes both. The [operational language](SEMANTICS.md#operational-language)
defines their numeric representation and comparison.

The supported equality
comparisons are specified under [guards](#guards) and in the
[operational language](SEMANTICS.md#operational-language). Operations requiring
unsupported coercions are refused at the source boundary.

### Heap and contracts

The **heap** maps locations to their current values. A **world** assigns each
allocated location a fixed type, its storage contract. A heap satisfies a world
when each stored value meets that contract. A write must preserve it. Allocation
extends the world with fresh locations; it does not change existing contracts.

A readonly view permits reading a location without permission to write it.
A writable reference must preserve the same contract through every alias.
For example, a writable Boolean cell cannot be used as a writable `true` cell,
because another alias could store `false`.

The semantic model handles recursive types using a **step index**, a natural
number bounding how much execution an approximation describes. The safety
result holds at every index. This mathematical index is separate from the
resource budget used by proof search.
[Worlds and recursive types](SEMANTICS.md#computations-and-recursive-types)
give the definitions and their relation to the cited step-indexed models.

### Current-content assertions

A cell's current contents can be more precise than its lifetime contract.
For example, `{ value: boolean = true }` describes a Boolean cell whose current
value is `true`. The observation permits a more precise read; later writes
must still satisfy the Boolean contract.

Each statement entry supplies a local interface: binding types and current
heap observations. Every incoming edge, including a loop back edge, must
establish that interface. The calculus can also retain relationships such as
two slots denoting the same value or two private cells being distinct.
The source-entry rules determine which of these facts cross a checkpoint.

An unrestricted call invalidates heap observations because the callee may write
through an alias. A certified heap-preserving call can retain facts on normal
return, under the [effect rules](#inferred-call-effects-elaboration-and-certification).
Immutable values remain available. A closure's initial heap assumptions follow
from storage contracts, rather than observations made when the closure was
created. See [source checkpoints](PROGRAM-TYPING.md#source-observation-checkpoints).

### Mutable bindings

A `let` and an assigned parameter are private cells
with a storage contract fixed where they are declared: the annotation, or
the producer's proposal (TypeScript's widened or evolved type), against which
the initializer and every write are checked. A closure holds the cell's
identity; a `const` copy holds a snapshot, and an unannotated constant of a
named union is held at the union's arms, as an annotated one is, an
annotated one initialized by an object literal at the arms the literal may
be of (TypeScript's narrowing on assignment); a constant's object literal
used whole where an optional field it leaves out is expected is claimed
with its exact keys
([rules](PROGRAM-TYPING.md#mutable-bindings-and-module-constants)). A `let`
statement whose initialized bindings nothing in their scope writes, closures
included, is a `const`: each holds its initial value throughout, so a test
narrows it and a `let` pattern binds (`LET-CONST`). A `let` that is written
and holds a union of objects is not narrowed by a test of its object: a
cell's known contents are primitive or merely no `undefined`, and a write in
between may replace it.
A written `let` pattern binds hidden names, then each source name is a
cell of its own at its value.

A local may hide an outer binding of its name. The parser renames it, by
the declaration TypeScript binds each reference to, to a name no source
spells (`x@line:col`), so the lowering never meets two bindings of one name:
consistent renaming of bound variables, for `const`, `let`, parameters, patterns, closure
parameters, `for...of` and `catch` bindings in any body
([shadowing](PROGRAM-TYPING.md#derived-source-forms)). A mention above the
declaration, a closure's included, or in its own initializer is refused, as
JavaScript's temporal dead zone throws there.

### Objects and prototypes

An object's set of keys is fixed at allocation in the calculus. Writing a field
changes its location's contents. Adding a key to a fresh, unaliased local object
can be represented by copying the object with the additional field and updating
the local binding. This translation is valid only when no other reference can
observe the old object. Source extraction checks that ownership condition;
[key-adding writes](PROGRAM-TYPING.md#key-adding-writes) states the restriction.

A record type is **open**: it describes named properties without excluding
others. An **own-key bound** adds information about which properties an object
itself owns. An upper bound lists the only permitted keys; an exclusion bound
lists keys that must be absent. Fresh object literals have known own keys.
These bounds matter for optional fields, dictionaries and native methods.

The model represents a prototype link under the reserved key `[[proto]]`.
A missing own property can be read through that link. Classes use prototype
objects for methods and distinct keys for private fields. `readonly` grants a
read capability without granting a write through that view. The exact
[record contracts](POSITIVE-TYPES.md#records) and
[class translation](PROGRAM-TYPING.md#classes) define these forms.

### Object literals

A literal allocates one object owning exactly the properties it writes, in
order. A spread of a literal is its fields; a spread of any other value is an
allocation from parts, copying the value's own enumerable data properties
when it is evaluated
([allocation from parts](PROGRAM-TYPING.md#allocation-from-parts)): a class
instance's methods are its prototype's and are not copied, nor is an
`Error`'s non-enumerable `message`. The model's copy takes string keys
only, where JavaScript's also takes an own enumerable symbol-keyed property:
a spread of a value whose type states a symbol key is refused, and the
[trust surface](#trust-surface) states why no typed read observes the
difference. A
function's own enumerable properties are the fields its type states (a
callable object's) and whatever else was assigned to it, which the copy's
type leaves open; a function the program creates owns none, its one field,
which gives it an identity, being under a key no source spells. A numeric
key is the property its `ToString` spells, and a computed key naming a
`unique symbol` constant (`Symbol.iterator`, or one the program makes) is that
symbol's key; `__proto__`, any other computed key and accessors are refused. An object pattern's rest is the same copy less the
named keys. Where a part is a dictionary and every part says what it gives
under the index's keys, through an index or its exact keys, the result is a
writable dictionary at what the parts give there; a spread of an open record
meets no index. `Object.assign` is the same copy, onto a fresh literal or,
as a statement, a local's own object, from sources whose types rule out an
own `__proto__`, which it would set through the prototype's setter.

### Arrays

A **realm** is a JavaScript global environment with its associated built-in
objects and prototypes. The array contracts below assume the standard
prototypes of that realm.

An array is one store of element locations under the reserved
store key and one object holding `Array.prototype` under `[[proto]]`, read
through the one array shape (`arrayClauseOf`,
[arrays](POSITIVE-TYPES.md#arrays)). Its own keys exclude the members declared by
`ArrayProto` and `constructor`, so `xs.map` reaches the prototype
and ordinary construction cannot be overridden; it may own other keys,
as Skip's runtime tags managed arrays with a symbol key. Stores may be sparse;
source `T[]` requires **readability**: every in-bounds read, including a hole's
`undefined`, meets `T`. Density is a separate, stronger guarantee. All three
spellings (`T[]`, `Array<T>`, `ReadonlyArray<T>`) use the same element-family
interpretation, including generic substitution. Element writes currently require
an in-bounds position or appending; they preserve each presence mode.
Mutable arrays are invariant;
`readonly T[]` reads only and is covariant. Arrays are `Iterable<T>` through
their prototype's `[Symbol.iterator]`, a tuple through the readonly array of
its positions. An array's `length` is read from its store, in a statement and
in a closed expression alike. An array pattern's rest over a tuple of
required positions is reads; any other is a slice, a call of the trusted
`%RestFrom:k%` ([patterns](PROGRAM-TYPING.md#patterns)).
Every record and dictionary type is of objects meeting the **array
invariant**: one owning the store key is an array of the realm, a possibly sparse store
and `Array.prototype`, owning no key it provides. Allocation keeps it, since
an allocation owning the store key is typed only as such an array and a
merge copies no store; it is assumed of every value a unit receives at such a
type ([the array invariant](SEMANTICS.md#the-array-invariant)). So where
`Array.isArray` holds, a record arm is `readonly unknown[]`. `unknown`, which
is also what a handler binds a thrown value at, carries no invariant.

### Index signatures

An index signature describes properties in a **key class**: string keys,
canonical numeric property keys, or symbol keys. A dictionary read returns
`V | undefined` when the key may be absent. A readonly index promises values
of type `V` at present keys without granting writes.

#### Writable string index signatures

A writable index must permit every admitted write while preserving all aliases'
contracts. It is therefore invariant in its value type. A dictionary of `true`
cannot be passed as a writable dictionary of Boolean values: a caller could
store `false` through the wider view.

An own-key bound must also remain valid when external code adds an allowed key.
For example, a type that excludes `x` cannot justify a writable string index
whose callers may add `x`. Fresh literals intended as writable dictionaries are
allocated at the dictionary contract rather than using an exact-key bound to
justify that capability.

Within the source fragment, adding a key requires the ownership condition for
[key-adding writes](PROGRAM-TYPING.md#key-adding-writes). General dynamic
key-adding writes are restricted. External code is assumed to respect the
writable contract and the reserved-key restrictions.
[Dictionary typing](POSITIVE-TYPES.md#records) and
[source index operations](PROGRAM-TYPING.md#index-signatures) specify the
coverage checks and supported keys.

### Method members are host-relative

A method member's contract is relative to its host: read from `o` and invoked
with receiver `o` and admitted actuals, it behaves as typed, and it promises
nothing for another receiver ([`methodT`](POSITIVE-TYPES.md#records)): the
self-application of [Abadi and Cardelli 1996](REFERENCES.md#abadi-and-cardelli-1996). A
method call reads the member and binds it to its host in one term
(`bindMember`); nothing types a member read on its own. Consequences, each
forced by soundness:

- A method is not a function-typed property: the property covers the method,
  never the reverse (`const g = p.m; g()` would throw).
- Extracting a method (`const f = o.m`, `xs.forEach(o.m)`) gets nothing; the
  supported forms are `o.m.bind(o)` and class-field arrows.
- Method parameters are contravariant; TypeScript's method bivariance is
  refused.
- Interfaces with methods are covariant in results, so a class instance meets
  an interface it structurally meets, and an array meets `Iterable<T>`.
- Method members are read-only views: a write to one is refused.
- A class method taking fewer parameters than an interface's member is
  claimed at the longer signature as well, the extra actuals discarded at
  binding (`CodeOffers`); no subtyping widens an arrow's parameters.
- A method declaring `this: T` is a member whose host must meet `T`: it
  promises its signatures on a host that is a `T`, and a call proves its
  host one. The types a member's host must meet are contravariant, so a
  member stating one is no member stating none.

A generic method is a member with **quantified signatures**: a scheme the
member bound to its host meets, whatever receiver the bound function is
later given (`MethodMembers.boundOn`). It is the same host-relative promise,
read through `.bind`, so the scheme's own receivers admit every value, and a
call binds the member (`bindScheme`) and names its instance below the scheme.
Two quantified members relate as their schemes do, by the covering rule for
quantified signatures ([covered pairs](POSITIVE-TYPES.md#covered-pairs)): equal
binders, the source's bounds among the target's, the target's signatures
covered with its binders opaque, so decidable
([Pierce 1994](REFERENCES.md#pierce-1994)). Since the receiver is the host on
both sides, it is never compared, and a declaration whose generic methods take
its argument only covariantly is covariant: `Promise<A>` is below `Promise<B>`
where `A` is below `B`, by `then`'s and `catch`'s own signatures. A
generic method's binders are owned by its application
([generic methods](PROGRAM-TYPING.md#generic-methods)), so two instances of a
declaration, and members of two declarations, bind different parameters:
relating them needs the covering rule up to renaming the target's binders
([quantified-α](RECURSIVE-EQUATIONS.md#41-quantified-signatures)).
A class's generic method is such a member of its instance type, which its
prototype's closure, a scheme received by the instance, covers bound to the
instance ([classes](PROGRAM-TYPING.md#classes)).

### Exact contracts and native effects

A source declaration is lowered in full or refused. Unsupported generic
bounds, mixed value/argument-pack binders and an unguarded alias cycle are
refusals. No such failure denotes `unknown`, and no
method is dropped. This matters in result and writable positions: forgetting
a contract there would certify a value that does not satisfy its annotation.

Native contracts are reviewed separately from their TypeScript declarations.
Unrestricted `find` and `findIndex` callbacks receive `T | undefined`: a prior callback can
shrink even an initially dense array through another reference, while these
methods visit the original index range. `map` visits only present indices,
but shrinking its source can leave holes in its result. Separate overloads consume
a certified `preservesInputHeap` callback: `find`/`findIndex` can then pass `T`,
and `map` produces a dense result from its dense receiver. The fresh result
is assigned the readable `U[]` lifetime contract, so it remains writable at
the source type even when `U` admits holes. These are ordinary
qualified callback types, including when the callback is returned or bound.

**Ordinary array construction is part of the admitted semantics.** An array
owns no `constructor` key, and the realm's `Array.prototype.constructor`,
`Array[Symbol.species]` and relevant prototype links retain their standard
behavior. External code must preserve the same invariant for values it supplies
and across calls. This is an explicit host assumption, like the restrictions on
proxies and accessors; it is not a theorem about arbitrary JavaScript.

The own-key part is stated in the existing array contract and realm invariant:
`RequestJson.arrayExcludedKeys` adds `constructor` to the prototype's declared
keys. Arrays cannot acquire it through an invariant-preserving allocation,
structural alias or write. The fragment also refuses custom species definitions,
array subclass construction and the unreviewed prototype-changing APIs. It
continues to allow an ordinary record's own `constructor` field. Standard native
construction therefore needs no extra promise on each callback. `map` returns
a sparse array of its unrestricted callback's result type; `filter` and `slice` create ordinary
arrays. Density after a callback is still a separate obligation.

The runtime controls beside `ordinary-array-construction` deliberately violate
the external assumption: a custom species gives `map`/`filter` a string-valued
`length` and `slice` a non-array result. They explain why the assumption matters;
these are not accepted executions of the admitted language. Custom species can
be modeled later with explicit construction contracts. See
[`ArraySpeciesCreate`](REFERENCES.md#ecma-262).

**Standard array conversion is an enforced restriction.** Arrays may not own
`toString`, `join` or `Symbol.toPrimitive`, and their standard prototype chain
must retain those members' behavior. The same rule applies to external code.
The existing own-key invariant enforces it; `ArrayProto` also states that
`Symbol.toPrimitive` is absent or undefined. A recursive native contract admits
primitives and arrays of convertible values. Default sorting and joining can
therefore convert numeric tuples and nested arrays without calling client hooks.
The actual route is `ToPrimitive` → standard `toString` → standard `join` →
recursive element conversion, not an inference from numeric contents alone.
Custom conversion on arrays is a deliberately excluded corner case; general
objects with conversion methods still need an explicit comparator. This follows
[the utility principle](#principles), and does not claim arbitrary JavaScript
arrays satisfy the restriction. The equations and native signatures are in
[prototype contracts](PROGRAM-TYPING.md#prototype-contracts).

`sort` with an explicit comparator accepts arbitrary element types. Its call
contracts are separate signatures of one quantified callable; passing undefined
selects the conversion-requiring contract. Existing subtyping and application
rules suffice. Native conformance remains audited, not proved against ECMA-262.

The native regression sources are also executed under Node. Source-contract
erasure is tested against both verifier entry points using a forged producer
proposal. These tests exercise premises and translation that the calculus
safety theorem does not prove. Intrinsics are collected on demand from the operations the source uses.

### Inferred call effects: elaboration and certification

A call signature may state the effect `preservesInputHeap`: on normal return,
the call leaves every previously allocated location's contents unchanged.
It may allocate fresh storage. An **effect-qualified signature** is a signature
carrying such a guarantee. `CallEffects.lean` defines its semantics; the
[effect contract](SEMANTICS.md#effect-qualified-call-contracts) and
[certification rules](PROGRAM-TYPING.md#certifying-inferred-call-effects)
state what a certificate must establish.

This extends the language of claims beyond TypeScript annotations. Three
operations must remain distinct:

1. **Annotation translation** preserves the source contract. An ordinary
   TypeScript arrow imposes no heap-preservation guarantee. It must never become
   an effect-qualified arrow merely because a consumer needs one.
2. **Inference** proposes a stronger type for a definition, including an effect
   on each call signature. This is untrusted producer work. It can use bodies
   and inferred contracts of callees; it need not change the source annotation.
3. **Elaboration and verification** attach the proposal to the lowered
   definition and discharge its additional obligation. Lowering emits proof
   obligations; it does not establish an effect by translating syntax. Lean must
   check both ordinary body safety and the claimed effect, with the original
   annotation obligations retained. Only certified types may justify uses.

At a call, the rule consumes the qualified type of the value. It does not
inspect its source body or recheck it for the observed call. The guarantee
must survive passing, returning, capturing and generic instantiation through
ordinary type operations. An explicit annotation may forget the guarantee;
that loses precision, not soundness. Overloads carry effects per signature.
An imported implementation needs checked evidence or an explicitly documented
external assumption: its TypeScript declaration supplies neither proof nor an
implicit effect. Built-in contracts remain separately audited assumptions.

The first guarantee preserves existing heap contents on normal return and
allows fresh allocation. A call that throws supplies no heap postcondition.
Consequently, a body checker cannot carry this guarantee through a caught
exception: it must check the handler with the possibly changed heap, or have
a separately justified guarantee for exceptional exits. The current pure-body
checker does not admit such calls. Graph composition checks normal-return
postconditions node by node and refuses handlers; the independent pure-graph
rule can still certify pure handlers. Qualified-call composition retains
this distinction. No stronger external assumption is implicit here.

The guarantee is sufficient but not necessary for safe dense
`map`: mutation of unrelated state can also be safe. Future footprint-sensitive
effects can express that without changing the inference/certification boundary.
The body-effect checker recognizes a subset of programs satisfying the
semantic contract. An unrecognized body therefore represents an inference or
checking limit, not a restriction on the meaning of heap preservation.

The source acceptance theorem includes effect checking. Pipeline controls
exercise qualified callbacks passed or returned as values, ordinary-call
fallbacks, and forged effect claims on bodies that mutate captured storage.

### Calls

Argument lists are native: the callee is evaluated first, then
the actuals left to right; a missing trailing actual binds `undefined`, so
`x?: T` is `T | undefined` and a default's position admits `undefined`;
extra actuals are discarded after evaluation. A function type promises which
actual lists a caller may write and what the call then guarantees
(`callsT`, `restsT`), independently of the code's arity
([one meaning for callable contracts](SEMANTICS.md#one-meaning-for-callable-contracts)).
A rest parameter makes the code variadic: invocation collects the remaining
actuals into a fresh array, viewed at the rest's type: an array or a tuple of
required positions, readonly or not, or a declared alias of one, a generic
alias read through its equation at the reference's arguments. A rest typed by a binder is an argument pack,
whose contracts are over lists at the actuals' own level
([argument packs](POSITIVE-TYPES.md#argument-packs)). A closure claimed at
several signatures is checked once per signature. A spread among the actuals
is replaced by its store's elements once every earlier actual is a value;
spreads may sit at any position of fixed parameters or feed a generic
signature's inference. Into a rest, a spread followed by an actual that runs
code is copied where it is written, so the later actual cannot change what it
passes; into fixed parameters such an actual is refused
([model limits](#model-limits)). A union callee is called at every
arm, its result the union of theirs; a method call on a union whose arms'
members differ reads and calls in one step dispatched on the receiver, where
every actual is a name or a literal. A union callee whose alternatives carry callable fields
is refused ([call rules](PROGRAM-TYPING.md#reading-the-source)).

### Primitive members

A member read on a primitive is read through the
realm's wrapper prototype (`String.prototype`, `Number.prototype`,
`BigInt.prototype`, `Boolean.prototype`) with the primitive as receiver; a
string's `length` and indices are its own
([prototype contracts](PROGRAM-TYPING.md#prototype-contracts)).

### Receivers

Every signature states its receiver and every call passes one:
`undefined` for a plain call, the object for a method call, the first
argument for `.call` and `.apply`. The receiver rule is strict mode's; a
sloppy function that reads no `this` is the strict one, its receiver being
unobservable. `.bind` allocates a forwarding descriptor whose
receiver a later `.bind` or `.call` cannot replace (`callsT_bound`).

### Generic types

A declaration is one equation, and a generic application a finite term over
the equations, unfolded one step when a check reads it, so a recursive family
of applications, however it grows, is finitely many heads
([one equation per declaration](PROGRAM-TYPING.md#one-equation-per-declaration),
[RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md)). A generic method is a
[member with quantified signatures](#method-members-are-host-relative), a
scheme whose binders its application owns; a binder intersected with ground
types is a meet label ([RECURSIVE-EQUATIONS §2.2](RECURSIVE-EQUATIONS.md#22-meaning)).

### Graphs

A body is a finite graph of nodes, each evaluating one term then
returning, binding, discarding or branching; destinations carry explicit slot
maps, checked on every edge; a node may name a handler for a throw out of its
term ([control-flow graphs](PROGRAM-TYPING.md#checked-control-flow-graphs)).
Global safety covers cycles without unrolling.

### Throws

`throw a` evaluates `a` and throws its value; a throwing term does not step,
and every evaluation context carries the throw out
([semantics](SEMANTICS.md#computations-and-recursive-types),
[rule](PROGRAM-TYPING.md#throwing)). The primitives JavaScript throws on step
to throwing an error object (`binopThrows`): a bigint division or remainder
by zero or a negative exponent, and, where the gate admits them at all, a
number mixed with a bigint or a symbol converted. A handler binds the thrown
value at `unknown`, under only the facts that hold without the heap
(`handlerFacts`), since the body may have run any effect before it threw. A
`finally` block is compiled on every way out, returns and jumps included: a
`break` or `continue` runs each `finally` it passes, innermost first, then
lands ([try](PROGRAM-TYPING.md#statement-forms)).

### Guards

A guard is a test JavaScript defines exactly. It is followed where the model
answers it as JavaScript does, as one more tag test (`Tag`, `tagHolds`), so
it narrows by the one mechanism of tag observations (`tagSlice`), and refused
with the reason where the model would answer otherwise
([rules](PROGRAM-TYPING.md#guards)). The tests are `typeof` (eight shapes,
`"object"` being `typeofObject`: `null` or an object without call code),
`key in o` (`hasKey`, along the prototype chain the model holds), truthiness
(`ToBoolean`), `== null`, strict equality against a singleton of any
primitive kind, `Array.isArray` and `instanceof Array` (`isArray`: owns the
store key; a record or dictionary arm is then the realm's `readonly
unknown[]`, by the [array invariant](#arrays)), and `x instanceof C` for a
class the file declares (`hasKey` of the key only `C`'s prototype owns; it
narrows a union's arms, never `unknown`, since JavaScript gives any object
`C`'s prototype without `C`'s constructor). A test of a field of an
immutable binding's object against a singleton, or of its truthiness where
an arm leaves the field optional (an `IteratorResult`'s `done`), narrows the
object's arms; a
key found present promotes an optional field to a field, since an object
keeps its keys. A test on a mutable cell refines the read, never the cell.
`&&`, `||` and `??` return an operand, as JavaScript's do, by the same
tests; a chain of one of them reads right-nested, so each operand sees what
every earlier one answered. `x instanceof C` of a class whose chain of bases
holds a static `[Symbol.hasInstance]` is a call of that method, its result
converted by `ToBoolean`, and narrows nothing.

### Async and iteration

`await`, an async function's return and completion, `for...of` and a
spread over a host iterable, an array pattern's slice rest and `for...in`
are calls of trusted **intrinsics**, values no source name spells, whose
signatures the declaration reader states
([async](PROGRAM-TYPING.md#async-functions-and-await),
[loops](PROGRAM-TYPING.md#loops-and-spreads-over-iterables)). A loop over a
host iterable steps one **iteration intrinsic** family, `%Iterate:K%`, picked
by TypeScript's type of the iterable: an array's (`%Iterate%`), a string's, a
`Set`'s, a `Map`'s and a host collection iterator's; a spread collects the
same iterator into a fresh array (`%Spread:K%`). A `for...in` whose body
reads the entry at its key, `o[k]`, where nothing that could change the entry
ran since the step, steps the dictionary's entries (`%Iterate:ForIn%`), a
fresh `[key, value]` array per key, read at its step, and the read is the
step's value: a dictionary holds no prototype, so the keys the loop visits
are its own ([statement forms](PROGRAM-TYPING.md#statement-forms)). None of these iterators has
a `return`, so leaving such a loop early calls nothing. An iterable the
program defines (an object with its own `[Symbol.iterator]`, an
`Iterable<T>`) runs the **iterator protocol** of
[ECMA-262](REFERENCES.md#ecma-262) as ordinary calls, each typed
by TypeScript's `Iterable`, `Iterator` and `IteratorResult` declarations: the
parser writes GetIterator, `next` read once and called per step, the result's
`done` tested (a truthiness test of a field, which refines the result to its
not-done arm) and its `value` bound. IteratorClose is a **closing region**
around the loop's body, a `finally` that runs on some ways out only: before
a `break` of the loop leaves it, before a `return` returns, and, its own
throws discarded, before a throw out of the body resumes; not at the body's
end, on a `continue`, or when the iterator is done. It calls the iterator's
`return` where it is not `undefined`, whose result must be an object. A
spread of such an iterable is collected before its statement, where nothing
the statement evaluates before it can change, and an array pattern over one
steps once per element and closes the iterator where no rest took it to its
end. No calculus rule changes: a call's callee is an assumption at its
declared type, or code the unit checks. An async function's
promise settles only to a primitive, the values that are never thenables
([nested promises](TRUST-REDUCTION.md#illustration-nested-promises)).
The model runs a body to its end; every point where other code can intervene
is an `await` or a call, across which only contracts survive.

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
| An imported value meets its declaration; a function declared with overloads meets every overload. | `IMPORT`, `OVERLOADS` in [PROGRAM-TYPING](PROGRAM-TYPING.md#imported-ambient-and-global-values) |
| An ambient declaration (`declare function`, `declare const`, `declare class`) holds of the value the environment supplies under that name; the declaration document lists it with the specifier `ambient`. | `AMBIENT`; `collectDeclarations` |
| A global variable outside the standard library (Node's `process`) meets its declaration at the members and calls the module selects, from the project's type packages, and no code the module does not see reassigns it. | `GLOBAL`; `selectGlobal` |
| Each standard library global meets its reviewed overlay entry: `console.log`; `BigInt`; `Symbol`, `Symbol.for`, `Symbol.keyFor` and five well-known symbols; `String` of a primitive; `Object.keys`, `Object.values`, `Object.entries` (and the generic two at a dictionary); `new Array()`; `Array.isArray` and `Array` as `instanceof`'s operand; `new Error(m)`; `new Set`, `new Map` of an array, `new Date` of nothing, a primitive or components, `Date.now`; the `Promise` statics and constructor, through the intrinsics below; `JSON.parse` of a string and `JSON.stringify` of a `JsonValue`. | `globalsOverlay` in [`tools/library-globals.mts`](tools/library-globals.mts); [rules](PROGRAM-TYPING.md#library-globals) |
| `Array.prototype` meets `ArrayProto`: its natives `forEach`, `map`, `reduce` and `reduceRight` (with an initial value), `every`, `some`, `filter`, `slice`, `join`, `toString`, `indexOf`, `lastIndexOf`, `includes`, `at`, `find`, `findIndex`, `sort`, `push`, `pop`, `shift`, `unshift`, `reverse` and `[Symbol.iterator]` meet the reviewed overlay contracts, at the listed receiver, without `thisArg`; result construction uses the ordinary-array invariant; `map` promises a sparse result for unrestricted callbacks and a readable result, freshly dense, for a dense input and certified heap-preserving callbacks; `find`/`findIndex` admit missing callback values unless the callback has that guarantee, and `join`, `toString` and default `sort` restrict elements to the recursive standard-conversion contract, with own conversion hooks excluded; comparator sorting checks the supplied callback. Units allocating arrays read it from the input slot `[[Array.prototype]]`. | `overlay` in [`tools/array-prototype.mts`](tools/array-prototype.mts) |
| `String.prototype`, `Number.prototype`, `BigInt.prototype` and `Boolean.prototype` meet `StringProto`, `NumberProto`, `BigIntProto` and `BooleanProto`, each member an own property of that prototype (`split`, `replace`, `replaceAll` stated at a string pattern; `toLocaleString` without `options`), read from the slot `[[String.prototype]]` and so on. | `primitiveOverlay` in `tools/array-prototype.mts` |
| `Set.prototype`, `Map.prototype` and `Date.prototype` hold the listed natives, unmodified (`keys`, `values` and `entries` giving a host iterator of the collection). | `interfaceOverlay` in `tools/array-prototype.mts` |
| The intrinsics meet their signatures: `%Await%` yields what a promise settles to or throws its rejection; `%AsyncReturn%` and `%AsyncComplete%` settle an async function's promise to a primitive or `undefined` (also `Promise.resolve`); `%PromiseAll%` (`Promise.all`), `%PromiseReject%` (`Promise.reject`), `%NewPromise%` (`new Promise`, calling its executor at once); `%Iterate%` steps an array's iterator, reading the current length at each step; `%Iterate:string%` a string's, by code point; `%Iterate:Set%` a `Set`'s, in insertion order; `%Iterate:Map%` a `Map`'s, a fresh `[key, value]` array per entry; `%Iterate:Iterator%` a `SetIterator` or `MapIterator`, which is its own iterator; `%Iterate:ForIn%` the keys a `for...in` over a dictionary visits, its own, a fresh `[key, value]` array per key with the value it holds under the key at the step; none of these iterators has a `return`; `%Spread:K%` is the fresh array of what `%Iterate:K%`'s step yields until it ends; `%RestFrom:k%` is the fresh array of an array's elements from `k` to its current length, as its iterator yields them after a pattern's `k` elements; `%ForIn%` gives the keys a `for...in` visits, strings; `%HasProperty%` answers `k in o` for a key TypeScript types as other than string literals, as the host's lookup does; `%ElementAt%` reads `xs[k]` of an array at a `number` key as the host does: the element at an index below the length, an own property at another numeric key, else `undefined`. The job queue and a promise that never settles are not modelled. | [`tools/intrinsics.mts`](tools/intrinsics.mts); [async](PROGRAM-TYPING.md#async-functions-and-await) |
| A thrown value is a value, of any type. | `Thrown` in `Safe` (`Semantics/Safety.lean`) |
| The runtime with the sound service binding meets its declarations: `InputCollections.get(definition)` returns the collection built from that definition at its types, or throws; resources are constructed with the request's `Json` parameters. | `pipeline/skip-runtime-sound-binding/` |
| In the SKJS test environment, SKJS's import stubs describe the modules a test imports, and `skjs-environment.d.ts` the host's `process`, `__SKJS_show`, `__SKJS_show_expanded` and `StringRecord<V>` as SKJS's builtins stub does, with the ES2022 library and no DOM (`console` restated); `Closed<T>` and `SKJS_Ignorable<T>` are read as `T`; an ambient class's untyped field is a readonly `unknown` field. These are premises of the coverage result only. | `pipeline/skjs-environment/`; `STUB`, `ENV` |

**Assumed of the host.** Properties of every value a unit receives, on which
the model's reading of an operation relies.

| Assumption | Where it is stated |
| --- | --- |
| The caller contract: a value conforming to a structural annotation (a parameter, an import, a library result) is a plain data object, its stated string-keyed fields own enumerable data properties, not accessors or proxies, which a spread copies, an optional field `f?: T` is absent or holds a `T` (the exact reading SKJS defines, as `exactOptionalPropertyTypes` does; a present `undefined` is stated as `f?: T | undefined`), and a class instance owns its private slots, keyed by their private names; a conforming function respects its contract across every future heap, callback effects included. Two such parameters may alias. `Error`'s `message` is the exception, held on a prototype the model gives it. | `RequestJson.verify_safe` quantifies over environments meeting the input types |
| A value whose trusted declaration types it `Function` has call or construct code. | [`Function`](PROGRAM-TYPING.md#library-types) |
| A value TypeScript types as `Set<T>`, `Map<K, V>`, `SetIterator<T>` or `MapIterator<T>` that a loop or spread iterates is the host's: its iterator is the realm's, and the prototypes it inherits (`%IteratorPrototype%` included) hold no `return` and are unmodified. Assumed of every such value a program receives; the fragment builds none but through the host: a `Set`'s and a `Map`'s type state their `[Symbol.toStringTag]`, a well-known symbol key no literal or class of the fragment writes, and no annotation of the fragment states a `SetIterator` or `MapIterator`. A host iterator a program's protocol steps (an array's, as an `Iterable<T>`) likewise has no `return` along its chain. | the iteration intrinsics' pick, `iterationKind` in `tools/declaration-graph.mts`; `writtenSymbol` in `tools/fragment-parse.mts` |
| Every object owning the array store key is a JavaScript array: every object the model allocates, and assumed of every object a program receives. `Array.isArray` is the native test. For `instanceof Array`, every array a program receives is of its realm and no object but an array inherits from `Array.prototype`. | `isArray` ([SEMANTICS](SEMANTICS.md#operational-language)); the `Array` entries of `library-globals.mts` |
| The array invariant: every object a unit receives at a record or dictionary type that owns the array store key is an array of the realm: its store may be sparse, it holds `Array.prototype` (meeting `ArrayProto`, which reads no parameter row), and it owns neither `constructor` nor any key declared by `ArrayProto`. Proved of every object the unit allocates; assumed of every value it receives, as the arrays it receives at array types already are. Nothing is assumed of a value at `unknown`, and no class invariant: an object whose prototype chain holds a class's prototype need not have the class's fields. | `realmInvariant` in the meaning of record and dictionary rows, so `EnvOk` in the premise of `checkJson_safe` ([SEMANTICS](SEMANTICS.md#the-array-invariant)) |
| An array a program receives owns neither `constructor` nor any key declared by `ArrayProto`. The realm keeps standard `Array.prototype.constructor`, `Array[Symbol.species]` and their prototype links; external code preserves that behavior across calls. | the own-key exclusion bound includes `constructor` (`RequestJson.arrayExcludedKeys`); standard native construction is a host assumption |
| An array a program receives owns, at a canonical numeric key that is no index below its length, only a data property holding a value of its element type, as `Array<T>`'s declared `[n: number]: T` says; the realm's `Array.prototype` owns no numeric key. What `%ElementAt%` reads rests on it; the arrays the model allocates own no such key. | `%ElementAt%` in `tools/intrinsics.mts` |
| The model's reserved keys (the store key `[]` and every name in double brackets) are spelled by no source key, and an object a program receives is represented with its own keys apart from them. | `Fragment.sourceKey`, `reservedSourceKey` |
| `Object.prototype`, `Array.prototype` and `Function.prototype` own no string key but those `inKeyRefusal` lists (node's `Object.getOwnPropertyNames`), none enumerable, so a `for...in` over a plain object visits its own keys only; `String.prototype`, `Array.prototype` and `Object.prototype` own no numeric key; `String.prototype` owns no `[Symbol.split]` or `[Symbol.replace]`; `Object.prototype` has no `toJSON`. | `inKeyRefusal` in `Source/Fragment.lean`; the overlay comments |
| Distinct JavaScript objects have disjoint field locations, which is how `===` on objects with a field is answered; only allocation creates an object value. | `Arith.eq` |
| Code outside a unit adds keys to an object it holds at a writable index only at that index's contract and only keys of its class, none the model keeps for itself (`[[proto]]`, `[]`: an object owning a property JavaScript spells so is one the model does not represent, as for any object it meets). The calculus has no step that adds a key; a program adds one by copying its own object. Every type the unit may hold such an object at stays true of it with the key: its own-key bounds by `ownKeysT_keeps` and `covers_writable_keeps` (a writable index some value meets is met only through bounds that keep its class; a literal meant for one is allocated at it, `allocDict`), its fields, views, indexes and optional fields by the covering premises a writable target states. | [index signatures](#writable-string-index-signatures) |
| The model's spread and `Object.assign` copy string keys only, where JavaScript's also copy an own enumerable symbol-keyed property: the copy's type states no symbol key and is open, so no typed read names one, and a key test for a symbol is the host's `%HasProperty%`, which answers from JavaScript's object and narrows nothing. | [object literals](#object-literals); [`in`](PROGRAM-TYPING.md#derived-source-forms) |
| The standard `Object.assign`, `Function.prototype.call`, `apply` and `bind` are the intrinsics the parser identifies by lexical provenance; the fragment cannot write those properties. | `tools/fragment-parse.mts` |
| A value of type `Promise<T>` is a realm promise, which resolution never fulfills with a thenable (it adopts one), so awaiting it yields a `T`: runtime and library promises, the program's `async` functions (`%AsyncReturn%` adopts), `Promise.resolve`, `new Promise`, `%PromiseReject%` and `%PromiseAll%`. A trusted generic signature (imported, ambient, library) is truthful about `Promise<T>` or `PromiseLike<T>` only at a `T` no thenable inhabits, so each type parameter such a position names is bounded by the non-thenable types. | `%Await%` and `nonThenable` in `tools/intrinsics.mts`, `promisedBinders` in `tools/declaration-graph.mts`; [async](PROGRAM-TYPING.md#async-functions-and-await) |

**Not yet proved.** Module composition: a unit's certificate assumes the
signatures of the module values it reads, each certified by its own unit;
the step-indexed argument that they compose is not a Lean theorem
([modules](#modules-and-code-units)).

## Fragment boundary

What the pipeline refuses, each with its reason, in the two classes the
coverage run counts (`CLASSES` in
[skjs-coverage.mts](pipeline/skjs-coverage.mts),
[refusal classes](pipeline/SKJS-COVERAGE.md#method)). A refusal is
**principled** only when the construct is unsound, not faithful to
JavaScript, rejected by TypeScript, or safe only under an assumption the
project declines; any other refusal is a **model limit**, a gap, with the
obstacle named. A search failure is neither.

### Refused on principle

| Construct | Refused because |
| --- | --- |
| `new Array(n)`, `new Array(x)` with one argument | A numeric argument constructs holes; a readable element contract excluding `undefined` cannot justify those reads. The source gate refuses the ambiguous one-argument form. |
| An element write at an index not proven in bounds or appending | It could create a hole. |
| A mutable `Dog[]` as an `Animal[]`, a mutable dictionary of `true` as one of `boolean`, a readonly view as a writable one | Mutable storage is invariant: a write through the wider alias breaks the narrower one's contract (TypeScript's covariance is unsound). |
| Method bivariance (`Handler<Dog>` as `Handler<Animal>`), an override with narrower parameters, a narrower constructor at a construct signature | The member may be invoked with the wider argument. |
| A method as a function-typed property, method extraction (`o.m.call(r)`, `.apply` and `.bind` of one included), a write to a method member; a function whose `this` is typed where a receiver-indifferent callback is expected | A method is host-relative: read off its host it loses its receiver, and TypeScript's typing of it is unsound. |
| A record type where an index signature or a dictionary is expected (TypeScript's implicit index signature); width subtyping into an optional field; an array where a number index is expected | A record is open: it may own further keys at any type; an array has a prototype a dictionary lacks. |
| A position past a mutable tuple's arity; its `length` read at the arity | `push` may have extended it: TypeScript's `undefined` there, and its literal length, are unsound. |
| Narrowing `unknown` by `instanceof C`, and a member read of the result | JavaScript gives an object `C`'s prototype without `C`'s constructor running (`Object.create(C.prototype)`, `Object.setPrototypeOf`, `Reflect.construct` with `C` as the new target), so "an object whose chain holds `C`'s prototype has `C`'s fields" is false of values a unit may receive. |
| `instanceof` of a constructor not declared at the file's top level (imported, ambient, a function, an expression) | Nothing in the file says which prototype it gives its instances; trusting it is an assumption declined. |
| A base class declared later, imported, ambient, or an expression | Nothing in the file says what its constructor allocates (TypeScript rejects the first). |
| `key in o` on an operand with a primitive arm or `unknown` | JavaScript throws on a primitive, and TypeScript rejects both. |
| A loop or an array pattern over an iterable whose iterator's type states no `return` | Leaving it early, or a throw out of its body, calls whatever `return` the iterator owns, and an open record type says nothing of that property. |
| An async function returning an object other than a promise of a primitive, a void async function returning a value, `await` of a non-promise object at its own type | JavaScript adopts thenables, and a record type does not rule out a `then`. |
| An object literal, class or parameter property the source builds with a `then` member, which could be claimed as a `Promise` | A value of type `Promise<T>` is assumed a realm promise; the source must not forge one. |
| `String(o)`, `o + ""`, `new Date(o)`, `new Set(it)` of a non-array iterable, `JSON.parse` with a reviver, `JSON.stringify` with a replacer, of an array or an open record; a relational comparison with an object operand | The host runs client code (`toString`, `valueOf`, an iterator, a callback, a `toJSON`). |
| `+` on a bigint, number–bigint arithmetic, a symbol in a concatenation; a relational comparison of a string with a number | TypeScript refuses these operations. |
| `==` or `!=` that may convert an object to a primitive, including an array | Conversion may invoke client hooks and mutate aliases. Standard array string conversion does not justify default-hint conversion, which calls `valueOf` first. TypeScript reports an array compared with a primitive as having no overlap, so only a union reaches the conversion: too rare to justify a `valueOf` restriction and a runtime array dispatch ([utility](#principles)). |
| `this` before `super(...)` | TypeScript rejects it, and JavaScript throws. |
| A read of a local above its declaration or in its own initializer; a parameter default reading a later parameter | JavaScript throws there (the temporal dead zone), and TypeScript rejects it (TS2448, TS2373). |
| An assignment to a module function's binding | TypeScript rejects it (TS2630). |
| A call of a `Function` value | It states no signature to call it at: TypeScript calls it at `any`, which states no contract. |
| A fresh callable given a field `call`, `bind`, `name`, `length`, `caller` or `arguments` (`Object.assign(f, { name })`) | An own `call` or `bind` would replace the intrinsic the parser identifies by lexical provenance ([trust surface](#trust-surface)); a function owns `name` and `length` unwritable and inherits `caller` and `arguments` as accessors that throw, so JavaScript's copy throws where TypeScript types the callable with the field. |
| A class extending `Array` | Its instances' `constructor` is the subclass, so `map`, `filter` and `slice` construct their results through it (`ArraySpeciesCreate`), which [ordinary array construction](#arrays) excludes (`invalid-array-subclass`). |
| A catch binding annotated other than `unknown`, or destructured | Anything may be thrown; TypeScript's alternative is `any`. |
| TypeScript's `any` in the checked module's own annotations; a contextual closure parameter TypeScript types `any` | It states no contract. |
| A rest parameter typed by what is no array | TypeScript rejects it (TS2370). |
| A rest parameter typed by an intersection (`...xs: T[] & (number[] \| string[])`) | Its declared contract can be empty at an instance TypeScript admits: at `T := boolean` no array is both a writable `boolean[]` and a `number[]`, writable storage being invariant, yet TypeScript accepts `f<boolean>()`, and a body writing through one operand's view returns a number as a `boolean` (`invalid-rest-intersection`, executed under Node by `test.mts`). |
| A type that normalizes to nothing as a whole (`string & { a: number }`, `(() => void) & number[]`, `number[] & { map: number }`); as an arm of a union such an intersection adds nothing | No value of the model inhabits it (TypeScript keeps a branded primitive); it is refused rather than verified vacuously. |
| An empty module (no function, no initialization code) | Accepting it would check nothing. |

### Model limits

Sound JavaScript that TypeScript accepts, refused because the model or its
representation cannot state it yet; the paths are in
[next steps](#next-steps).

| Construct | Obstacle |
| --- | --- |
| A write adding a key (`o.x = 5` where `o`'s type does not state `x`, a writable optional field, a key of an index) to an object another reference may hold: a parameter, a module constant, a local whose object was passed, stored, captured, returned, copied to another binding or written into itself, or a write in a loop the declaration does not enclose | The model's objects keep their keys, and a key is added by copying the object: another reference would still see the object without the key, where JavaScript's sees it with. |
| A write at a string key known only at run time (`d[k] = v`), even on a local's own dictionary | The string may spell a key the model keeps for itself (`[]`, `[[proto]]`), which JavaScript owns as an ordinary property. |
| A write of `__proto__`; adding a symbol key | The first runs the prototype's setter and adds no key; the copy that adds a key copies string keys only. |
| `Object.assign` onto an object other than a fresh literal or, as a statement, a local's own object; from a source whose type does not rule out an own `__proto__` | Its value is its target, and another reference would see the keys it adds; it sets `__proto__` through the prototype's setter, which replaces the prototype. |
| `===` or `!==` between two operands neither known to be a primitive or an object (`unknown`, a type parameter's value); narrowing by object identity | Two such values may be of no kind the operator decides; a statement entry states no slot equality. |
| A relational comparison converting a primitive (`undefined`, a Boolean) | The model's comparison is of two numbers or two strings; the refusal does not tell this conversion, which runs no code, from an object's. |
| `keyof T`, `T[K]` over a function's own type parameter (an alias computed from its parameters is evaluated at each application) | They are functions of the type an instance names (its declared, optional and readonly keys); a parameter row denotes a value set, which does not determine a key set. |
| A template literal type with a `${string}` hole; `keyof` with a unique-symbol key; `typeof` of a binding whose inferred type is not an object literal's record of literals and primitives, or of a class with statics | No term of the fragment states it exactly. |
| An intersection with a union holding a type parameter, `(T \| null) & A`; a function type met with a record of readonly or optional fields, methods or an index | It distributes into meets known only at an instance; no clause states such a callable. |
| `declare let`, `declare var`, a module-level `let` or `var` | A unit's module inputs are immutable slots; module storage needs cells every call may write. |
| An ambient `declare enum`; an enum member TypeScript computes no value for; a NaN or infinite member; a reverse key naming a member; an empty enum | An enum type is its value set, which an ambient declaration need not state; the other keys are known only at run time, or have no literal type, or leave no record. |
| A `this` read in sloppy code | The receiver rule is strict code's; sloppy receiver conversion (the global object, a wrapper) has no term. |
| A library class other than `Array` as a base (`extends Map`) | Construction allocates an ordinary object at the class's fields; a library constructor's instance has no construction rule. |
| `key in o` for a string literal key the realm's prototypes hold (another key is the host's `%HasProperty%`, a Boolean narrowing nothing); a class value as the operand of `in`; `key in x` on an `unknown` a `typeof` test found an object (`typeof x === "object" && x !== null`) | The model holds no key of the realm's prototypes and would answer otherwise than JavaScript; a class's statics are bound apart; a `typeof` test answering `"object"` gives `unknown` no narrower type, and `in` needs an operand of object types, as it throws on a primitive. |
| A user-defined type guard (`x is T`) or assertion function (`asserts x is T`), with a body or declared | Its promise relates the result, or the completion, to the argument, which no function type states. |
| An array assignment pattern writing a field (`[o.f] = e`) | Its target's reference is evaluated before its position is read and defaulted; the lowering writes locals only. |
| An accessor (`get`/`set`), `__proto__`, a computed key in a literal other than a `unique symbol` constant, a spread of a string or of a value that may be a class | The heap has data properties only; the key or copy is known only at run time (a string's characters); a class's static fields are bindings of the model, not properties of the class value a copy reads. |
| A literal or class member keyed by a well-known symbol other than `Symbol.iterator` (`Symbol.toStringTag`, `Symbol.toPrimitive`, …), but a class's static `[Symbol.hasInstance]` method, which `instanceof` calls | It changes how the host treats the object, which the model does not state; a tag would let it pass for a host collection, whose iteration is trusted. |
| An element read past a readonly tuple arm's length (`const [a, b] = t` with `t: readonly [number] \| readonly [number, string]`) | No element rule reads `undefined` beyond an exact length. |
| A rest parameter of a definition typed by a type parameter; one typed by a tuple with optional or rest elements | A definition has no allocation rule for an array only an instance fixes (a function type's is a pack); several lengths are several signatures. |
| A written `let` pattern in a `for` head, or a written `let` in a `for...of` head; a test of a written `let` holding a union of objects; a `let` captured by a closure in a `for` loop | Its bindings are cells, which only a statement of a block lowers them to; a cell's known contents are primitive or merely no `undefined`; JavaScript copies the binding per iteration, which the lowering does not. |
| An array pattern over a value that may not be an array | The pattern reads an array's positions; over a host non-array iterable it would step `%Iterate:K%`, which the lowering does not place. |
| A generic or optional method declaring `this: T`; an optional method of a type literal nested in a declaration; a generic class method with a bounded binder; a constructor's rest parameter; a constructor parameter default, or a statement, reading `this` before the instance is complete | A generic method's member is a scheme its member bound to the host meets at every receiver, which states no type the host must meet, and an optional method is an optional field, whose function takes its declaration as receiver, which a nested literal is not; a generic class method's bounded binder, whose row its bound names; no rule constructs at a variadic construct signature; the instance is allocated at the end of the constructor. |
| A class member with a computed key other than a method's `unique symbol` constant or a static `[Symbol.hasInstance]`; an index signature in a class; a static block reading `this`; a class extending a generic class other than at the base's own binders | A method is a binding and a prototype key named by its plain name or its symbol; instances are what construction allocates; the block's receiver is the class value, whose statics are bindings of their own; a generic base's construction is at its binders' rows ([classes](PROGRAM-TYPING.md#classes)). |
| A class with a private name in inheritance; `#x in o` | A derived instance's base part is a copy, and a copy holds no private slot; the test asks for an own slot, where the model's key test walks the prototype chain. |
| An instance member or constructor reading a static of its own class; a static method that reads `this`; `super` in a static member; a mutable static field | Statics are bindings the class defines after its methods and constructor, whose closures cannot hold them, exact only when immutable; a static method's receiver is whatever its call passes, and its `super` the base's constructor. |
| `o.m?.()` | It would call the tested value with a receiver the lowering does not save. |
| A generator function (`function*`); `for await` | A body suspended at `yield` is no term of the calculus; an async iterator's steps are promises the model does not adopt. |
| An array literal spread (`[...xs]`) other than the one element over a program's or a host's iterable | No literal lowering takes a spread. |
| A library global both constructed and read through members, or both called and read through a method (`new Date()` beside `Date.now()`, `Symbol()` beside `Symbol.for`); an object type with construct signatures and other members | A class value or callable object with members has no clause. |
| Any library signature the overlays do not list (`Math.random`, `concat`) | Not reviewed; nothing is trusted by default. |
| A non-library global read other than through a member or a call (`const p = process`) | A global is assumed at the members and calls its references select; a read of the value selects none. |
| A module function without a result annotation | Its slot is its annotated signature, at which its unit is checked and every call reads it. |
| A mention, in a closure written above it, of a local that shadows an outer binding | JavaScript gives the name to the local from its block's start, and the closure reads it once it is initialized; the parser's renaming binds it from its declaration on ([shadowing](PROGRAM-TYPING.md#derived-source-forms)). |
| A name declared in one `switch` clause and read in another | The clauses share one scope, where the lowering gives each clause's statements a scope of their own; a read reached by falling through, or through a closure, finds the binding initialized. |
| A function declaration after a statement that always jumps | The lowering drops what follows a jump; the declaration is hoisted, so live code may name it. |
| An actual that runs code after a spread into fixed parameters | The call reads a spread's elements once every actual is evaluated; the lowering copies a spread where it is written only into a rest. |
| A spread of a program's iterable after an operand that runs code; a default or a nested pattern in an array pattern over a program's iterable | The iterator is run before the statement, and a pattern's names are bound after its steps: the operand's or the default's code would run in another order than JavaScript's. |
| A call through a union of functions carrying fields | The producer claims a call through one arrow the actuals call, which such a union does not offer. |
| A constructor writing a field that has an initializer, or writing one field twice | The instance is allocated at the constructor's end, from one value per field. |
| A generic class's instance member or constructor reading its own class | The class value is quantified over its declaring unit's binders, which the unit reads as parameter rows, and a module value is read only at ground instances. |
| An unannotated `let` of `null`, `undefined` or `[]` whose writes grow with it (`r = { tail: r }`) | Its contract is the union of what is written into it, which has no fixed point there. |
| A `let` with neither an initializer nor an annotation (`let y;`) | TypeScript types it as an evolving `any`; the pipeline reads a local's contract from its annotation or its initializer, and infers none from its later writes. |
| An imported interface its module declares more than once | The declaration reader resolves an import to one declaration; the merge of an interface declared twice is read for the checked file's own declarations ([interface merging](PROGRAM-TYPING.md)). |
| A closure parameter without an annotation that TypeScript types by an object type written nowhere by name | The parameter's annotation is TypeScript's contextual type, which the parser writes only through primitives, literals, arrays, type parameters and declarations by name. |
| A read through a field holding an object beside `null`, after a guard found the object (`x.child !== null`, then `x.child.b`) | What a location is known to hold is a union of primitives or its contract less `undefined` ([current contents](#current-content-assertions)): the guard states nothing of the object. |
| `unknown` used as an array after `Array.isArray` or `instanceof Array` | The array invariant is stated of record and dictionary members; `unknown`, which a handler binds a thrown value at, carries none ([next steps](#next-steps)). |
| `Object.assign` onto an array | The copy takes the target's fields but its store, so its result would be no array. |
| `\|\|=` or `&&=` on a target other than a Boolean | The lowering tests the value read as a Boolean. |
| A source key spelling one the model keeps for itself (`"[]"`, a name in double brackets) | The model holds an array's store and an object's prototype under those keys: an object owning one would be read otherwise than JavaScript reads it. |

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
  every assignment; no second typing mechanism for records over binders.
- **One row per generic application**, lowered from an empty visit.
- **Wire formats carry no version and have one shape**; producers and
  consumers are typed against one declaration.
- **Strings' lengths are not tracked**: `s[i]` is `string | undefined`.
- **Relational comparison admits only operands compared in their primitive
  order.**
- **`Closed<T>` is read as `T`**: less than SKJS's meaning, and true of every
  closed value.
- **A number is its double's bit pattern; a bigint its integer.** Distinct
  spellings of one value are one singleton ([values](#values)).
- **An omitted closure result is the producer's claim**; an annotation adds a
  requirement at the annotated signature and never removes a check.
- **`<T>e` is `e as T`**, and a type reference to a name that is also a function resolves to the type.
- **A type assertion decides nothing**: `e as T` is an obligation that the
  operand meets `T`.
- **Two model laws stay refused**: distributing arrow results over an
  intersection, and collapsing eventually incompatible reference contracts to
  bottom ([retained constraints](SEMANTICS.md#two-retained-design-constraints);
  contrast [Frisch, Castagna and Benzaken 2008](REFERENCES.md#frisch-castagna-and-benzaken-2008)).
- **Graph evidence is certified at every assignment of parameter rows**
  (`Parametricity.accept_reassign`); a checker that read the assignment could
  not be given its `_reassign` lemma.

## Next steps

Open design work, each a known gap with the reason it is open. How many
units each gap stops is in
[SKJS-COVERAGE](pipeline/SKJS-COVERAGE.md#refusals-by-class).

### Status

Progress is recorded here and nowhere else. A commit that moves an item
updates its row. The prose below describes each item's design, not its
progress.

**One producer.** The OCaml producer is the pipeline's one producer, which the
cases, the corpus and the report viewer run. The shared control-flow IR
separates execution structure from type-directed expression elaboration.
The Fragment supplies source-oriented type inference; graph points and edges
supply the producer's data-flow equations. Mutable declaration contracts and
point-specific contents have separate claim identities.

| Item | State | Closed when |
| --- | --- | --- |
| 1. Delete the TypeScript producer (`tools/tsc-claims.mts`): the OCaml producer is the pipeline's one producer, the corpus and the report viewer run it | done | compared per function on the corpus's 303 (2026-10-05): the OCaml producer's claims verify for 301, the TypeScript producer's for 276, every one of those among the 301; the producer, `--producer`, the viewer's producer choice, the report writer's generic report input and per-function collection metadata deleted; TypeScript's own verdict per function (`typescriptVerdicts`) beside the verifier's in the corpus and the viewer |
| 2. The producer reads the shared control-flow IR: design and validation. Lean constructs claim-independent execution points and edges, final lowering consumes that IR, and the producer proposes environments and current contents per point. Type-directed expression elaboration consumes those proposals; mutable declaration contracts have separate identities | done: `FlowGraph`, `ExpressionPlan` and `BindingPlan` supply the shared execution schedule; entry and expression claims have owner-qualified point identities, expression sites also retain source spans, and mutable lifetime contracts have separate identities; forged point and contract associations are refused | the design states the graph wire, the claims keyed by node and the checks on that association; a prototype over a subset of the cases (control flow, `try`/`finally`, iterator close, closures) reaches the same outcomes as the source-level producer, with forged node keys refused |
| 3. The producer reads the shared control-flow IR: cutover | done: all 847 cases and independent forged-claim/report controls pass; the 53-file corpus has the same per-function outcomes as its baseline (303 accepted, 301 derived, 2 not derived); all six protected runtime traces pass; source-level control-flow, compound-expression and binding/default execution mirrors are retired | every `cases.mts` outcome and the corpus's per-function results unchanged or better; the producer's source-level control-flow mirror and association by source position alone deleted; expression claims identified by execution point and source span |

**Decomposition and state ownership.** This checklist covers the producer,
source lowering and their documentation. Completion counts milestones, not
equal amounts of effort.

| Milestone | State | Closed when |
| --- | --- | --- |
| M1. OCaml proposal decomposition | done | pass coordination, execution, expression families and publication have separate modules |
| M2. Lean typed source lowering decomposition | done | recursive lowering operations have responsibility-specific modules and explicit callbacks |
| M3. Lean claim decoding and acceptance decomposition | done | decoding, site validation, extraction and certification have separate owners |
| M4. Lean equation lowering decomposition | done | equation construction stages have separate modules |
| M5. Lean nested graph frame | done | closure compilation restores one enclosing graph frame |
| M6. OCaml execution analysis interface | done | the interpreter receives explicit lookups and operations without mutable pass-state access |
| M7. OCaml speculative frame | done | speculative inference restores one local record on every exit, retaining shared proposals and diagnostics |
| M8. OCaml claim collection interface | done | claim collection receives lookup, publication and speculation operations |
| M9. Node output and path scopes | done | named output records and scoped execution replace paired checkpoint callbacks and restore enclosing output and metadata on every exit |
| M10. Overload-row claim scope | done | each signature collects its claims through one scoped operation with restoration on every exit |
| M11. Typing-context scopes | done | block return context, observation roots, active point and rigid bounds have explicit scope operations |
| M12. Remaining OCaml access restrictions | done | the seven expression modules, binding analysis, statement analysis and closure offers use responsibility-specific interfaces; their unrestricted pass-state views are retired |
| M13. Lean lowering access restrictions | done | temporary contexts have scoped operations and consumers cannot access or replace the complete construction state |
| M14. Documentation organization | open | calculus rules, source elaboration, host contracts, protocol definitions, architecture decisions and the work ledger have clear owners; large mixed-subject documents are split, prerequisites are explicit, and links resolve |

**Upstream sum example.** `reactive-sum-prettier-ignore`, Skip's sum service
as published, against the pinned upstream runtime. The program is safe; the
items are the verifier limits it meets and the runtime's declared service
types, which do not state why it is safe.

| Item | State | Closed when |
| --- | --- | --- |
| 1. An intersection with no member inside a union is that union's bottom arm: `number & DepSafe`, distributed to `number \| (number & Managed)`, is `number` | done | `union-empty-intersection-arm` verifies, an annotation and a contextual callback parameter; `array-shadow-refused` stays refused; `reactive-sum-prettier-ignore` reaches item 2 |
| 2. A named function passed where a callback type binds more parameters: JavaScript calls it with the extra arguments, which it ignores | open | `process.on(sig, shutdown)` verifies, `shutdown` checked at its own annotated signature |
| 3. `runService(service, …)`: the upstream service types admit the service only by method bivariance, and do not relate what `createGraph` returns to what each resource reads | open | a design for runtime types stating that relation, against which the published service source is checked |

**Boundary-repair cleanup: done.** Restore the original positive sources that the
soundness boundary repairs refused ([steps](#restoring-completeness)). Closed
when every step is done and a full coverage run is back to at least the former
mechanism's 2,444 verified units and 121 gaps (current counts:
[SKJS-COVERAGE](pipeline/SKJS-COVERAGE.md): 2,466 verified, 110 gaps).
`sum-process-alias` stays a gap for a cause outside Promise (a global read
only through its members).

| Step | State | Closed when |
| --- | --- | --- |
| Loose equality coverage | done | `loose-equality`, `object-identity-equality` and `equality-deciding-operand` verify: primitive pairs, nullish operands and object pairs compared by allocation identity, and an operand known to be a primitive, an object or nullish against a type parameter's value; `invalid-loose-equality-narrowing` is rejected; `==` converting an array or an open record to a primitive stays refused ([row](#refused-on-principle), `loose-equality-array-conversion-refused`, `loose-equality-conversion-refused`); the upstream sum example reaches the shared refusal of the empty intersection `number & Managed` |
| 1. Explicit-comparator sorting | done | `native-sort-contracts` and the tuple-valued sorts verify; the optional-comparator negative is rejected |
| 2. Sparse results | done | `native-map-sparse`, `testTupleArrayMethod` and `isarray-record-array` verify; `invalid-map-hole-coalescing` is rejected |
| 3. Density-sensitive calls | done | `array-methods`, `array-library`, `array-generic-name`, `closure-contextual-parameters`, `testArrowOptional` and `testMapReturnsArray` verify; `mapArr`/`testMapCallback` stay refused, their written contract being false |
| 4. Standard array conversion | done | `sum-local-closure`, `sum-values-tuple` and `local-closure-result` verify; the coercion counterexamples are rejected |
| 5. Recursive quantified contracts (Promise) | done | the Promise table below is done |
| Coverage group "destructuring and rest/default parameters" (14 gaps) | done: 6 principled, 8 gaps | a rest typed by an intersection refused on principle ([row](#refused-on-principle), `invalid-rest-intersection`): `arraysAreInvariant` and `variance`'s `interWithTop`/`interWithTopS` units; coverage run 2,444 verified (2,444), 135 gaps (141), 85 principled (79). The 8 left are a binder used both as a pack and as an array value , whose design is in [remaining source forms](#next-steps) |
| Coverage group "classes: modifiers, inheritance, fields, parameter properties, receivers" (13 gaps) | done: 8 verified, 4 principled, 1 gap | a method declaring `this: T` is a member whose host must meet `T` ([method members](#method-members-are-host-relative), `method-receiver`; `invalid-method-receiver` and `invalid-method-receiver-widened` rejected at their own obligations): the 8 `this-parameter*` units verify. A class extending `Array` is [refused on principle](#refused-on-principle) under [ordinary array construction](#arrays) (`invalid-array-subclass`, with a Node run of `map` constructing through the subclass): the 4 `class-extends-generic-constructor` units. Coverage run: 2,452 verified (2,444), 123 gaps (135), 89 principled (85). The 1 left, `spread-callable#indexedOwnCopy`, is an index signature in a class, whose next blocker is method extraction (`read: source.read`) |
| Coverage group "a non-null assertion on a read at a for...in key" (8 gaps) | done: 8 verified | a `for...in` over a dictionary whose body reads the entry at its key where nothing that could change it ran since the step steps the dictionary's entries (`%Iterate:ForIn%`), each such read the step's value ([statement forms](PROGRAM-TYPING.md#statement-forms), `for-in-entry`); a read after a call, after a write of the enumerated chain and after rebinding the enumerated name are rejected at the cast (`invalid-for-in-entry-call`, `-field`, `-rebound`, each returning `undefined` under Node) |
| Coverage group "object literal members (methods, accessors, spreads)" (10 gaps) | done: 5 verified, 5 gaps | `Object.assign(arrow, literal)` at the two type arguments TypeScript infers (`function-fields-inferred`); the last merge of a literal at its claim, a written field allocated per arm of the expected union (`spread-field-per-arm`, `invalid-spread-field-per-arm`); a spread of a function copies its own fields, a created function's identity field being under `[[code]]`, which no source spells (`spread-function`, `invalid-spread-function-length`). Coverage run: 2,466 verified (2,452), 110 gaps (123), 88 principled (89: `callability#testSpreadTypeofFunction`, which TypeScript refuses, verifies). The 5 left are [model limits](#model-limits): a spread of a value that may be a class, whose statics are bindings of the model (`spreadConstructor`, `copyStaticData`, and `spreadFieldsAfterSpread`'s `{}`, which also admits a string), of an array, whose own numeric keys other than its elements its type does not bound (`restArrayEntries`), and of a symbol-keyed property, which the copy does not take (`symbolBranch`) |

**Promise (step 5).** Closed when `promise-covariance` verifies and
`invalid-promise-covariance` is rejected at its own obligation; the
`library-promise*`, `async-await`, `promise-instance`, `class-async-method`
and `sum-*` framework cases verify with their negatives rejected at their own
obligations; and `sum-sound-binding` verifies unchanged. The Promise gaps are
the `cases.mts` entries refused as unsupported recursive generic contracts.

| Item | State | Closed when |
| --- | --- | --- |
| a. Recursive equations | done | the table below is done |
| b. A callback returning a promise instantiates `then`'s binder through `PromiseLike<TResult>` | done | `promise-then`, `named-promise-catch` and `promise-then-promise` verify; `invalid-promise-then`, `invalid-promise-then-promise` and `invalid-promise-catch-promise` are rejected at their return contracts |
| c. `await` on realm promises, forged promises refused | done | decided; `forged-promise-refused` stays refused on principle |
| d. A binder no actual, receiver or expected type constrains takes its declared default (`then`'s `TResult2 = never`), which the declaration document states for each scheme binder | done | `promise-then-chained` verifies; `invalid-promise-then-chained` is rejected at its return contract |

**Recursive equations (Promise a).** Closed when
`generic-growing-application` and `generic-growing-application-push` verify
unchanged ([design](#recursive-quantified-contracts)).

| Item | State | Closed when |
| --- | --- | --- |
| Shared rows (`GraphRow`, `NormalGraph.ofRowMap`) | done | proved |
| Equation graphs, one-step unfolding (`EquationGraphs`) | done | proved |
| Free support (`EquationSupport`) | done | proved |
| Application congruence (`EquationCongruence`) | done | proved |
| Checked substitution (`EquationSubstitution`, `substitutionTableOk`) | done | proved |
| One proved image checker for subtyping, expression typing and program certificates (`checkUsing`, `HasTyUsing`) | done | proved |
| Formal specification ([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md)): motivation, meet labels, quantified-α, family subtyping, lowering, wire format, acceptance statement | done | reviewed; corrected to the pipeline |
| Thread the image checker through heap, context, control-flow and certificate-production proofs | done | proved; no finite-only premise left on the program path |
| Kernel: quantified-α, family entries, per-head variance declarations and `Var`, writable invariance kept ([§4](RECURSIVE-EQUATIONS.md#4-subtyping)) | done | proved, with the §7.7 controls as tests; `promise-covariance` and its negative move with S7 |
| S1. Source-claims wire with tree labels ([encoding](SOURCE-CLAIMS.md#encoding)); a temporary Lean adapter keeps the finite path | done | every `cases.mts` outcome unchanged; tamper and field-name tests pass |
| S2. Diagnostics show labels through a finite projection | done | identical diagnostics on every case |
| S3. Kernel: meet labels, equation validator, tree codec and hashing | done | proved; no pipeline change |
| S4. Source layer generic in its label type, still over the finite table | done | bit-identical evidence on the corpus |
| S5. Equation lowering module ([§5](RECURSIVE-EQUATIONS.md#5-from-source)), not yet wired | done | lowers `Promise`, `PromiseLike`, `Pair` and the upstream declarations with no budget |
| K2. Kernel: family hypotheses reach meet parts, so `meet(x,B) ≤ meet(y,B)` holds under `x ≤ y` (the framework's `T & DepSafe` heads, [§4.3](RECURSIVE-EQUATIONS.md#43-variance)) | done | proved; the `sum-collections` heads' variances check |
| S6. Cutover: lowering wired, `DeclarationGraph`, its budgets and the adapter deleted, `checkJson_safe` over `Equations.graph` | done | `generic-growing-application`, the Promise/async core, `sum-main` and `sum-run-service` verify; no negative verifies |
| R1. Fix: a bound framework method's claimed signature refused, the judgment holding. Equation lowering names a declaration's type literal by a head lifted over its binders, so the literal at an instance and the producer's own row for the same type are two labels with equal unfoldings. Two components required one label where the rule admits either. (a) Proof search's instance of a quantified member (`instanceCandidates`) offers the claimed operand as the image of a scheme operand spelled otherwise, which the image check accepts once proved equal, for fixed and variadic signatures: `map`'s constructor parameter `new (...p: P) => Mapper<…>` at its instance (`sum-map-array`, `sum-serializable-map`, `sum-add-index`, `class-value-generic-method`). (b) The checker's `bindMember` required a claimed variadic signature to be the member's by label (`merge`'s rest `EagerCollection<K, V>[]`); it covers it by subtyping proofs of the fixed parameters, the rest and the result, as a fixed one ([rule](PROGRAM-TYPING.md#judgments-and-constructor-views); `sum-collections`, `sum-resource`, `sum-sound-binding`) | done | the seven cases verify; `invalid-sum-map`, `invalid-sum-resource-mapper` and `invalid-class-value-generic-method` are rejected at their own obligations, and a rest claim wider than the member's at the bound member, by search and by the checker (`test.mts`); coverage run 2,441 verified (2,440 before), 142 gaps (142), 2 unexplained (3): `eagercollection-deep-value-no-oom#build` verifies; `json-generated-service#GraphResource` stops before any call, at its declarations, a record as `EagerCollection`'s `V extends Json` |
| R2. Fix: producer claims refused as outside their source annotation. Two causes, both in how the claims were written or read, the comparison being right. (a) The producer spelled a bounded binder `T` as `T & B`, while a binder label already denotes `T` within its bound as its unit reads it, the meet `T ⊓ B`: the claim read `T ⊓ B ⊓ B`, with `B` distributed when a union (`V extends Json`). Semantically within the annotation, but a second spelling the checker's meet rule does not relate (`generic-graph-bounds`; `class-ctor-tparam-unsound`, `generic-class-union-constraint`). The producer writes a binder by its name alone ([encoding](SOURCE-CLAIMS.md#encoding)). (b) A generic closure's scheme row for its annotations read the enclosing binders in claim-form parameters but not in graph labels (a class's generic method's receiver `C<T>`), so its annotations and its claim named two scheme rows' binders (`clauses-diff-subset`); `closureRows` reads them as its claims do | done | `generic-graph-bounds` verifies and `invalid-generic-graph-bound` is rejected; coverage run 2,438 verified (2,430 before), 144 gaps (155): the 8 `class-ctor-tparam-unsound` and `generic-class-union-constraint` units verify; of the 3 `clauses-diff-subset` units, 2 reach a later obligation, a class's generic method at the class's instance type (`class-generic-method`'s block, R3), and 1 is refused where TypeScript refuses it |
| R3. Fix: a class's generic method refused where the judgment holds. The prototype's closure and the instance type's member are two quantified signatures binding rows of their own (each scheme's binders are its head's), and the checker related a scheme received by the host to a target member only when both bind the same rows (`SchemeBinds`): incomplete for the quantified rule, which holds up to renaming ([RECURSIVE-EQUATIONS §4.1](RECURSIVE-EQUATIONS.md#41-quantified-signatures)). `SchemeBinds` renames the target's binders to the closure's, as `SchemeRenames` does for two declared schemes, proved in `covers_by_scheme_sound` ([rule](POSITIVE-TYPES.md#clause-coverage)) (`class-generic-method`, `clauses-diff-subset`) | done | `class-generic-method` verifies; `invalid-class-generic-method` is rejected at its own obligation, and a class declaration tampered so that the closure does not cover the member after renaming is refused at the construct code's return (`test.mts`); coverage run 2,444 verified (2,442 before), 141 gaps (141), 0 unexplained (2): `clauses-diff-subset#Helper` and `#testExplicit` verify |
| R4. Fix two stale `pipeline/test.mts` checks. The nested closure claim `() => boolean` over a body of type `T` is refused: proof search finds no derivation of its return-contract obligation, and the original evidence does not decode against the forged claims' equations; the check expected a message the equation labels no longer produce. `async-await` verifies, and the reader shows it verified; the check expected it refused as an unsupported Promise contract. The nested claim check asserts the search refusal at the body; the reader checks `invalid-default-invocation` as a whole-file unsupported source result before claims exist | done | both checks pass |
| S7. Variance by the checker ([§4.2–4.3](RECURSIVE-EQUATIONS.md#43-variance)): recursive instance discharge, variances computed per definition (traversal; guarded self-assumption on cycles), `Var` in request certificates, fallback coinduction up to renaming of bound variables; lowering's variance proposal and the front's variance gate removed | done | proved; tracing (`--trace-subtyping`) and the measurement script (`tools/subtyping-trace.mts`) in place; `promise-covariance`, `generic-growing-application-push`, `promise-like`, `framework-binding-sound`, `framework-binding-unsound` verify; `invalid-promise-covariance` and `invalid-framework-binding-sound` rejected at their own obligations |
| D. Decidability of subtyping in this model, studied in mathematics before any Lean | done | a note stating the problems precisely, what is proved, and what is open |
| S8. Coverage and performance, including the subtyping trace: work per question against type size ([§4](RECURSIVE-EQUATIONS.md#4-subtyping), linear-work conjecture) | done: 2,430 verified, 155 gaps, 1 unexplained; evidence median 44 kB, check median 32 ms; checker work at most 8.2 steps per unit of type size over 169 questions, consistent with the linear-work conjecture, not proving it ([measurements](pipeline/SKJS-COVERAGE.md#performance-on-the-pipeline-cases)) | coverage run remeasured; evidence size and decode time recorded; the conjecture confirmed or refuted on the examples, with the trace's counts |
| C. Delete the SKJS claim path, manual claim editing and the finite-table label store | done | no verifier mode, suite, tool, corpus column, report viewer feature or Lean module consumes SKJS's exported claims, edits claims, or uses the finite table as a label store; every `cases.mts` outcome unchanged |
| P. Fix: evidence production on `sum-sound-binding` and `reactive-sum-sound` costs 15 s at any search depth. Their one failing coercion (`Array<row 53>` to its meet with a readonly array) exhausts every search strategy, two of which prune a core table over the whole vocabulary (199 types, about 4600 candidate rows, 5–6 rounds), each table membership a scan of the row list. Search reads the table through a hash set of its rows (`CertificateProducer.RelIn`); the checker reads the list | done | both cases reach their expected refusal in under 5 s alone; every other `cases.mts` outcome unchanged |
| Q. The producer's subtyping search is §4's algorithm; the strategy cascade and pool-wide tables deleted. The search starts from the pair only: the premise judgment, an instance of a quantified signature (binder instances read through a meet among the matched row and the target's operands), or the fallback, which the checker decides itself: the pairs reachable from the pair, the uncovered ones deleted, the producer supplying only prototype-member instances. No certificate holds a table: `core`, `trans`, `table` and `gen` are deleted with `checkCore`, `Core`, `Valid` and `Sub`, and an instance's bounds are decided | done | `lake build` green, every `cases.mts` outcome unchanged but the two gap cases blocked on the meet `Array<row 53> & ReadonlyArray<…>`, which is now proved and moves their block to a later obligation; the case run 55 s (104–144 s before, loaded machine), `sum-sound-binding` 1.2–1.4 s alone (5.5–7.0 s before) |

**Follow-ups.** Engineering work not on the goal's path.

| Item | State | Closed when |
| --- | --- | --- |
| K3. Lowering: a unit bound naming another binder of the unit (`U extends T`). A function's or class's binder is its head's owned binder met with its lowered bound, which names the other owned binder (`EquationLowering.enterUnit`); a declared generic method's bound naming its own binders is refused ([request protocol](REQUEST-PROTOCOL.md)) | done | `generic-dependent-bounds` verifies (a function and a class); `invalid-generic-dependent-bound` and `invalid-generic-dependent-class-bound` are rejected at their own obligations |
| O5. The decoder convention ([AGENTS](AGENTS.md#conventions)) holds on the node side: each assertion that stood in for a check is replaced by it (a type predicate, a `typeof` or kind narrowing, `tools/syntax.mts` for the children a node of unasked kind carries, a restructured loop or destructuring), and `node verification/tools/unchecked.mts` fails on a written `any`, `as` or `!` without a `// asserted:` reason, a suite of `test-all.sh` | done | 81 `as` and 24 `!` in 20 files before; 7 `as` in 5 files, each a decoder's last line with its reason |
| O7. Divergence found by grouping the cases by requirement: requirements the cases guard that no document stated, source refusals in neither fragment-boundary table, and statements the pipeline contradicts | done: each requirement stated where it is owned, its group justified there: a type literal of call or construct signatures only, a rest over a union of tuples and the library's `Iterator` ([library types](PROGRAM-TYPING.md#library-types), [iterator protocol](PROGRAM-TYPING.md#the-iterator-protocol)); declaration merging ([one equation per declaration](PROGRAM-TYPING.md#one-equation-per-declaration)); object shorthand ([derived source forms](PROGRAM-TYPING.md#derived-source-forms)); `unique symbol` constants ([library globals](PROGRAM-TYPING.md#library-globals)); logical assignment and a `.call` receiver ([judgments](PROGRAM-TYPING.md#judgments-and-constructor-views)); a `Promise` method's binder through `PromiseLike` ([async](PROGRAM-TYPING.md#async-functions-and-await)); a closure's offers wherever it flows ([source closures](PROGRAM-TYPING.md#source-closures-and-their-annotations)); a `typeof` test of a type parameter's value ([refinement](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)). Every source refusal is a row of its table (4 principled rows, 18 limit rows, 4 limit rows widened), its case in that table's group with the row's kind (4 gaps made negatives, 14 negatives made gaps; `pattern-method-refused` and `mutable-tuple-position-refused` stay gaps under O8). Contradictions resolved: the class list admits generic inheritance at the base's binders and constructor defaults; a spread before an effect is copied into a rest and refused into fixed parameters; generic members relate up to renaming, the producer's reason corrected; `invalid-isarray-record`'s row removed, a typing rule's search failure; the symbol-key copy stated as the model's, beside JavaScript's | each requirement stated in the section owning it, each refusal a row of its table, each case's kind agreeing with its row |
| O8. Fix: two principled refusals, a method read off its object by a pattern and a position past a mutable tuple's arity, were thrown by source extraction as bare messages, so the report viewer had no obligation to show and their cases could not be negative controls. Both go through `locatedRefusal` at the pattern element (`Pattern.span`) | done | both refusals located at their source span; `pattern-method-refused` and `mutable-tuple-position-refused` negatives, the reader showing each |
| C2. Write the source layer directly over its one store, `EquationStore.State`: `EquationLowering` and `EquationStore` precede the modules written over them in the import order, which call the store's operations and `equationFront` directly. `StoreView` and `Labels` stay classes, each with two instances: the growing store and the frozen equations | done | the three classes deleted; `lake build` green; every `cases.mts` outcome and diagnostic unchanged |
| E. Fix: the declaration reader erased a generic method whose signature it could not read to an `unknown` member, so a produced value met the declaration at any field (`return { run: 42 }` as a `Runner` whose `run` takes a type literal with a generic method). The reader refuses the declaration at such a method; a declaration's generic function type, the form behind most such erasures (`EagerCollection.mapReduce`'s result), is a scheme term whose signatures take any receiver ([request protocol](REQUEST-PROTOCOL.md)). The other `unknown` readings in the parser, the OCaml producer and Lean are stated meanings (a declaration's `any`, an ambient class's untyped readonly field, a receiver no signature states), none a fallback for a contract the reader cannot read | done | `invalid-generic-method-nested-scheme` refused at its declaration, and 42 in `run`'s place throws under Node; `generic-method-nested-method` and `generic-function-type-member` verify, `invalid-generic-function-type-member` is rejected at its return contract and returns the unpaired argument under Node; coverage run 2,466 verified (2,466), 110 gaps (110): no unit loses verification; `testUnionWithGenerics` and `testGenericTupleConstraint` stay gaps, blocked at their own generic function values |
| U1. [Unified subtype engine](#subtype-engine-cleanup-plan): one comparison operation and its soundness boundary | done: checked structural dependencies and completed results share one comparison state; cached successes carry proofs at every parameter assignment, with a fresh cache for each equation environment; full Lean build and eight pipeline suites pass; the source case suite passes | the operation handles the existing subtype rules over equations, with checked internal justification and explicit resource exhaustion |
| U2. Route subtype consumers through that operation | done: lowering, extraction, proposal search and certificate checking use the common operation for bounds, arguments, results, receivers and image equality; explicit instances share its checked state; declaration gates retain located outcomes; Promise, 205-field record and callable-bound positive/negative controls pass | bounds, arguments, results, receiver checks and instance-image equality use the same engine; producers supply inference choices |
| U3. Resource accounting and diagnostic integration | done: explicit frontier budgets retain typed exhaustion through required source comparisons, proposal search, expression/heap checks, graph/code validation and source bundles; acceptance equivalence is proved; both CLI modes and the shared report viewer presentation pass insufficient/sufficient-budget controls with located judgments and inconclusive exhaustion | the 200-comparison acceptance cap is absent; exhausted work is located and visibly inconclusive through the CLI, runner and viewer |
| U4. Retire superseded paths and validate the cleanup | done: public evidence supplies instance choices; separate subtype strategies, finite bound search, producer image prechecks and stateless instance helpers are retired; rule inventory and documentation checks pass; full Lean build and eight suites pass; the source case suite passes and per-function outcomes agree with the recorded coverage run; five alternating binary benchmarks have comparable search/check timings; a forged instance bound citing its unfinished comparison is refused during evidence search and checking | strategy-selection evidence and duplicate searches are deleted; the closure checks below pass; documentation and coverage measurements agree with the implementation |

The stages' order and dependencies: S1, S3 and the kernel rows may run in
parallel; S4 follows S1; S5 follows S3 and S4's interface; S6 needs all of
them and the image-checker row; S7 follows S6; S8 follows S7. K2 and K3
block the framework cases, not the cutover.

<a id="subtype-engine-cleanup-plan"></a>
### Subtype comparison

A subtype comparison asks whether every value of one type also belongs to
another, under the stated type-parameter bounds. The engine operates over
recursive type equations. Identity, checked variance, quantified instantiation,
binder renaming and structural unfolding contribute to one comparison operation.
Equality of types requires inclusion in both directions.

The engine uses a work queue and records dependencies between comparisons.
A completed positive comparison carries a sound justification at every
admissible assignment of the type parameters. Unfinished recursive work cannot
be reused as an established result. Cached results belong to one equation
environment and its bounds.

Public evidence supplies choices such as generic instances. The checker derives
the required comparisons and validates those choices. Both typing search and
certificate checking use the comparison operation. The result distinguishes:

- an established inclusion, which may justify a typing step;
- an inclusion the supported search did not establish;
- resource exhaustion, which identifies an incomplete obligation.

The last two results cannot authorize acceptance. They are not proofs of
semantic non-inclusion. The [recursive-equation rules](RECURSIVE-EQUATIONS.md#4-subtyping)
own the algorithm and its soundness statement; the status table records the
implementation and validation milestones.

### Open work

**A connection to ECMA-262.** Proving the host's stated types as lemmas of a
mechanized specification would turn the ECMA rows of the trust surface into
theorems; the lemmas and their cost are in
[TRUST-REDUCTION](TRUST-REDUCTION.md#the-host).

**Constructor rests.** A constructor's rest parameter is refused. The code
could collect it as a closure's does, but no rule constructs at a variadic
construct signature: `ctorRestsT` has neither an introduction from code nor
an elimination by `new`, so that rule and its `construction` for code with a
rest (whose padded actuals would reach the store) come first.

<a id="generic-methods-left"></a>
**Generic methods left.** A class's generic method with a bounded binder:
the member's binder row is named by its bound, which the parser does not
spell for the closure (`class-generic-method-bounded-refused`). Members of
two declarations, or of two instances of one, binding as many binders relate
up to renaming ([generic methods](PROGRAM-TYPING.md#generic-methods)); two
binding different numbers of binders (`m<U, V>` at `m<W>`), which TypeScript
relates by instantiating the source at the target's binders, need an instance
table naming each source signature's image at the target's binders, inside
the family entry's table. A binder a member's result accumulates
(`catch`'s `Promise<T | TResult>`) grows its family by one binder per call:
each is an application of the one equation, unfolded only when read
([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md)), never truncated. Members of
two declarations, or of two instances of one, bind different parameters; the comparison operation relates their signatures up to binder
renaming ([RECURSIVE-EQUATIONS §4.2](RECURSIVE-EQUATIONS.md#42-parametric-assumptions)).

<a id="restoring-completeness"></a>
**Contract completeness.** Array presence, callback effects and conversion
contracts impose separate obligations. Their current designs are stated under
[arrays](#arrays), [native contracts](#exact-contracts-and-native-effects) and
[effect certification](#inferred-call-effects-elaboration-and-certification).
A future inference improvement must preserve these distinctions: density is
stronger than readable elements; readonly aliases do not prevent callback
mutation; and a written callback annotation cannot silently acquire a stronger
effect. A program with an arbitrary callback promising readable `U[]` for every
`U` must justify that promise even when the callback shrinks the source.

Effect inference remains conservative for some rest wrappers, call forms and
nested heap operations. Expression scheduling alone does not supply the missing
effect derivation. Keep the source targets and their negative controls when
extending the body-effect checker; report coverage using the measured results
in [SKJS-COVERAGE](pipeline/SKJS-COVERAGE.md).

<a id="recursive-quantified-contracts"></a>
**Recursive quantified contracts.** Generic declarations are parameterized
equations. Their finite syntax can describe an unbounded family of instances;
comparison unfolds only what an obligation needs. Parameter identities must
remain local to their applications, substitution must preserve bounds and
effects, and writable positions must remain invariant. These requirements are
specified in [RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md).

A universally quantified native prototype is an audited host contract. It
cannot replace an arbitrary structural interface whose method may capture the
interface's type parameter. Any future simplification must preserve that
semantic difference.

**The array invariant at `unknown`, and a record's `length`.** `Array.isArray`
on `unknown` needs the invariant of every value, a thrown one included: the
throw outcome of `Safe` would carry it, which makes it relative to the graph's
realm. `length` read on a union of an array and a record naming `length`
needs a dispatch on `Array.isArray`, the store's length on one arm and the
field on the other, with the invariant excluding an own `length` key, which
the model's arrays never have. Until then both are located search failures.

**Keys known only at run time.** A key-adding write at one of several literal
keys needs a dispatch on the key, one copy per key; at a number or a symbol,
a one-key allocation at a computed key, and for a symbol a copy that takes
symbol keys. A write adding a key to an object another reference holds needs
the heap to map an object's identity to its keys, which it does not.

**Module composition** as a Lean theorem: the step-indexed argument that
units certified against each other's signatures compose.

**Iteration left open.** An array literal spread needs a literal lowering
that appends a spread's elements (the `%Spread:K%` array, or an array's
store) after the positions before it. An array pattern over a host
non-array iterable needs the pattern's reads as steps of `%Iterate:K%`, or of
the protocol. A spread of a program's iterable where the statement evaluates
code before it, and a default or nested pattern in an array pattern over one,
need the protocol's steps interleaved with that code, in the expression, not
before the statement. A generator needs a state-machine lowering, as
TypeScript's downlevel emit writes one: a closure over the suspension
point's number and the live locals, whose `next` resumes at a `switch` on
it. An element read past a readonly tuple arm's length needs a rule
reading `undefined` beyond an exact length.

**Remaining source forms.** Assignment patterns into fields: each
element's target reference (receiver, computed key) evaluated into slots
before the position is read and defaulted, then a field write, which the source parser restricts to local-variable targets. A method call on a union of primitives,
which needs one callee contract its receiver meets. A source binder used both
as a pack and as an array value (`...args: T`, `args: T`): a binder whose instances are
arrays or tuples of required positions, its pack meaning that tuple contract's lists, so an
entry collects the fresh store at it and a spread of its value gives a list in the pack. Explicit type arguments on an element call,
which reach an element only as a generic closure's quantified claim.
User guards and assertion functions: the promise is a contract a
conjunction of arrows states, `(x: A) => boolean` with
`(x: Exclude<A, T>) => false` (an assertion function's `=> never`), which the
body is checked at, as a closure at each of its signatures; a caller narrows
through a fact the call leaves tying its result slot to its argument slot,
"an argument in `Exclude<A, T>` gave `false`", which the branch on the
result turns into a slice of the argument. Such a fact is about a type's
meaning, world- and level-indexed, where current-content facts are not; it
needs its own place in the knowledge a statement entry states. A class's
statics read by its own methods, which needs them read late, from the class
value, rather than as bindings its closures capture; private names in
inheritance, which needs the derived construction's copy of its base part to
carry the base's private slots; a prototype member keyed by a symbol.

**Model limits of one form each.** Module storage (`declare let`, a
module-level `let`) needs cells every call may write, read at their declared
type. Sloppy code's `this` needs the receiver conversion (the global object,
a wrapper). A library class as a base needs a construction rule for what its
constructor allocates. An ambient enum needs an enum type that is not its
value set. `keyof T` and `T[K]` over a function's own binder need a row whose
meaning fixes a key set, which a value set does not. A relational comparison
converting `undefined` or a Boolean needs the conversion's rule, and the
refusal a reason apart from an object's. `o.m?.()` needs the receiver saved
across the test. `key in o` at a key the realm's prototypes hold needs those
prototypes' keys in the model.

**Precision.** Retaining heap facts across calls needs a proved
reachability or noninterference statement; set-valued clause covering (an
arrow against a union of arrows) needs a covering relation of another arity;
a vacuity escape for contradictory reference conjunctions
(`Ref null ∧ Ref bool ≤ Ref (null ∨ bool)`) is true and not derivable; the
producer's arrow search builds no nested `combine`. An element read keeps no
heap fact: it reads the heap only, but the value it finds is a value only
where the store's contract says so, which the frame rule would have to take
from the read's typing (a length is a number, and keeps them). A module function of fixed
arity meets a longer signature (it discards the actuals past its parameters,
`restsT_of_graph`), but its slot is its annotated signature: the slot would
carry the padded promise, a claim its own unit checks.

**A semantics of the Fragment.** The parser's rewrites and extraction rest
on review. The Fragment moves close to source JavaScript, the rewrites move
into extraction, and the Fragment gets a direct semantics in Lean: an
executable interpreter that reads it as JavaScript does, with types erased.
Extraction is proved a simulation of it. The interpreter's faithfulness to
JavaScript is tested against node, not proved: the target is fixed, so
testing converges without a mechanized specification. A rewrite chosen by a
type (`%Iterate:K%`, `%ElementAt%`) is correct under that typing premise.
The reading of declared types and the host remain trusted; the remaining
options are in [TRUST-REDUCTION](TRUST-REDUCTION.md).
