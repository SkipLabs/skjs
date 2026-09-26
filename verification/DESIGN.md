# Independent verification of SKJS results

The pipeline checks type claims about TypeScript programs with a small,
independently justified consumer. A producer proposes the types of a
module's expressions and the environments at its program points; Lean checks
that those claims are derivable in a calculus whose rules are proved sound
against an execution model. The OCaml producer, which reads TypeScript's own
declarations, is the one that moves; SKJS's exporter and the older
TypeScript-checker exporter are frozen ([below](#skjs-is-frozen)). No
producer is trusted.

This document states the current design and what comes next: the principles,
the architecture, the model in brief, the trust surface, the fragment's
boundary, the lasting decisions and the open work. It does not restate
rules. The [documentation map](README.md#documentation-ownership) assigns
them: terms, values and execution to [SEMANTICS](SEMANTICS.md), types and
subtyping to [POSITIVE-TYPES](POSITIVE-TYPES.md), program and source rules to
[PROGRAM-TYPING](PROGRAM-TYPING.md), wire formats to
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) and [SOURCE-CLAIMS](SOURCE-CLAIMS.md).
How much of SKJS's own test suite verifies, and what stops the rest, is
[SKJS-COVERAGE](ocaml-producer/SKJS-COVERAGE.md). Works the design draws on
are cited from [REFERENCES](REFERENCES.md).

**The experiment's boundary.** The pipeline checks SKJS; it does not change
it. SKJS's acceptance, inference and diagnostics stay as they are, and only
extraction that preserves them belongs here. A safe program SKJS rejects is
an incompleteness finding to keep, and a claim the verifier refuses is a
finding about SKJS or about the pipeline, never a reason to weaken a rule.

## Principles

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

**Lean is the authority; OCaml proposes.** Every claim, contract, instance,
loop head and construction hint the producer supplies is a proposal that Lean
checks against the source it reads itself. Search strategy, fuel and hints
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

**Evidence is syntax-directed.** Claims attach to source spans and
statement entries; loop heads and joins are supplied, and every incoming edge
must justify them. The checker infers no invariant and computes no join. What
a producer states at a program point is exactly what is checked there, and
source maps, which say how a node reads in the source, never reach evidence.

## Architecture

![Architecture: source extraction and associated claims form a request; an untrusted producer supplies certificates, and the proved consumer checks both before establishing modeled safety.](diagrams/architecture.svg)

[Open the full-size diagram](diagrams/architecture.svg). Green nodes are
connected by Lean proofs; amber nodes are source and model meaning that is
reviewed, not proved. The producer is outside the soundness argument, and the
request reaches the consumer directly: evidence cannot substitute another
program or weaker requirements.

### Stages

- **The parser** (`tools/fragment-parse.mts`, trusted) reads a file with
  TypeScript's own compiler API. Its gate admits the fragment and refuses
  everything else with a located reason; it lowers source rewrites (unbraced
  arms, `switch` as labeled blocks, templates as concatenations, enums, async
  forms as intrinsic calls) and emits the Fragment AST. Its declaration
  reader (`tools/declaration-graph.mts`, `type-term.mts`,
  `computed-types.mts`) writes the declaration document: every type the
  module names, as source terms, with imported, ambient and global values,
  the prototype contracts and the intrinsics the module uses.
- **The OCaml producer** (`ocaml-producer/`, untrusted) proposes claims: an
  expression type at every span Lean asks about, an environment at every
  statement entry, loop heads, the storage contract of an unannotated `let`,
  instances of generic calls, and rows it reserves for arrays, applications
  and meets it names without computing. Where TypeScript types by context,
  the producer proposes what TypeScript would: an unannotated closure's
  result widened, or the contextual return type where the body fits it; a
  fresh literal at a union built at the one arm its keys, length and literal
  members select; an unannotated constant's fresh array built at the array
  type its first use expects; a binder in `A | null` inferred from the
  actual's other atoms; a loop head found by running the body until what it
  claims of each cell is stable. Each is a construction hint Lean checks, and
  adds no trust.
- **Lean** (`lean/Verification/Model/`) reads the AST and declarations,
  lowers every annotation once to claim form (`DeclarationGraph.prepare`),
  lowers each code unit to a graph request (`SourceExtraction`), searches for
  evidence (`--produce-source-claims`) and checks it
  (`--check-source-claims`). Only the check is part of acceptance.

### Claims and the claim reader

A claim is a type at a source site, in one claim form shared by producers,
annotations and the declaration graph: rows of the request's type table,
built from clauses. Annotations become claims in `DeclarationGraph.prepare`,
so there is one reader of types, not one per producer; a claim-shaped
annotation in the source tree is refused. Claims are per unit, keyed by
source identity; each site has at most one, a required site without one is
refused, and extra or duplicate claims are refused. A producer's claim is
compared with the source's annotation by meaning, not by label: a function's
claimed signature must mean its annotation, a closure's claimed signatures
must lie within it, and the body is checked at each claimed signature
([claims against annotations](PROGRAM-TYPING.md#modules-and-code-units)).
SKJS's exports are imported into the same sidecar form
([SOURCE-CLAIMS](SOURCE-CLAIMS.md)) and read by the same consumer.

Positions associate claims with syntax; they authorize no edit and establish
no truth. Alongside the graph, the extractor records a **source map**: how to
describe each node and its bindings in the source's words, for diagnostics
only ([obligation diagnostics](OBLIGATION-DIAGNOSTICS.md#node-and-expression-obligations)).
It has no decoder and never reaches a request or evidence.

### Search

Search (`CertificateProducer`, `--produce-source-claims`) finds evidence for
the claimed program; it is untrusted and replaceable, and the check runs none
of it. A node whose term the extractor built with known evidence (a closure
creation, an array literal, an element read) carries that plan, which is
rendered, not searched; elsewhere search tries a sequent's own types before
the vocabulary, which is only what the file's request mentions. Subtype
search proposes finite core tables, instance tables and arrow certificates,
first over the types near the pair, and prunes rows that no table could make
valid. None of this changes what is checked: orderings and pruning decide
only how soon evidence is found, and the checker validates every table
([producing evidence](PROGRAM-TYPING.md#producing-evidence-from-supplied-claims)).
A failed search is refused by name for display only: `producer --explain`
lists the forms with a known reason and their spans, the innermost one that
meets the failed obligation is shown first, and with `--typescript-errors`
code TypeScript also refuses is named by its nearest error. Nothing of this
is a premise; Lean decides on the ordinary proposal
([a failed search refused by name](OBLIGATION-DIAGNOSTICS.md#a-failed-search-refused-by-name)).

### The one entry

`ocaml-producer/check.mts` is the one entry for a file: parser, producer,
Lean search, Lean check, each a phase with its own log and a wall-clock
limit (`stepTimeoutMs`). The outcome is `verified` (the check accepted),
`unsupported` (a located refusal by the gate or the producer), `unverified`
(search or check found no derivation; never a disproof) or `error` (a step
failed or timed out; never a verdict). `--project` names the TypeScript
project the file belongs to, whose `tsconfig.json` must be strict.
`run-cases.mts`, `test.mts` and the coverage run (`skjs-coverage.mts`) go
through it; only the frozen corpus (`examples.mts`) runs the SKJS and tsc
producers on its own.

### What "verified" means

`SourceClaimJson.checkJson_safe` is the headline theorem. Its premise is the
exact CLI success condition; its conclusion is that every extracted plan was
certified, and that for every accepted unit's request, every assignment
$\eta$ of its parameter rows, and every environment meeting the unit's
inputs at $\eta$ in an admissible world with a satisfying heap, the graph is
safe at its declared result read at $\eta$ (`SafeGraph`; each generic plan
additionally carries its universal certificate). The inputs are the unit's
parameters, the module values it reads, and every assumed value: imports,
ambient declarations, globals, prototypes, intrinsics. Every plan reaches
acceptance through one exhaustive conversion to `CertifiedPlan`; no variant
can be dropped. The proofs use no `sorry` and no project axioms. What the
definitions mean is reviewed, not proved; see
[what the checked development establishes](SEMANTICS.md#what-the-checked-development-establishes).
How the theorem relates to a JavaScript run, and what a connection to a
mechanized ECMA-262 semantics would add, is sketched in
[ECMA-CONNECTION](ECMA-CONNECTION.md).

### Modules and code units

A source file is a module, and the module is the unit of verification.
Obligations stay per code unit, so a failure points at one place: each
function, and the module's initialization, which runs its constants, classes,
enums and expression statements in order and checks every class's methods
and constructor. A module function is checked at its annotated signature, a
source-fixed slot no producer claims; a module constant is read at its
annotation or at the initialization unit's claim for its initializer, which
that unit checks. The initialization unit refuses a call that can read a
constant before it is initialized. Values the module does not define (imports,
ambient declarations, globals) join its scope at their declared types as
assumptions ([rules](PROGRAM-TYPING.md#imported-ambient-and-global-values)).

Composition is not yet a Lean theorem: a unit's result is relative to the
signatures of the module values it reaches, each certified by its own unit.
`--function` selects one unit; the rest of the module stays its scope. The
viewer shows one unit at a time, with the module's units as an outline.

### Generic bodies

A generic unit is an ordinary graph request whose binders are **parameter
rows**: rows the graph's assignment interprets and no rule reads.
`Parametricity.accept_reassign` proves acceptance independent of that
assignment ([Reynolds 1983](REFERENCES.md#reynolds-1983)), so one derivation is safe at every instantiation
([Generic-Body](PROGRAM-TYPING.md#overloads-polymorphism-and-binding)).
Records, tuples, arrays, field reads and writes, literals, calls of other
generic functions at a binder: whatever the graph checks for ground types it
checks over a binder, with no rule of its own. A bounded binder is the meet
of its row and its bound. A generic class's binders belong to the
initialization unit that declares it, so its constructor and methods are
certified at every instantiation. A call of a generic module value names its
instance, checked against the value's signature and bounds
([instances](PROGRAM-TYPING.md#imported-ambient-and-global-values)).

Two older paths remain. The direct rigid checker (`GenericSource`) is tried
first for variable-copy bodies and dependent bounds (`U extends T`), which it
states located obligations for; a body outside its forms goes to the graph.
One local quantified closure per function has its introduction checked once
under rigid binders (`ClosureCertificate`) and its eliminations compiled to
ordinary arrows ([quantified schemes](POSITIVE-TYPES.md#quantified-scheme-layer)).

### Closures are graph code

A closure's body is a graph, as a function body is (`funGraph`,
[graph code](SEMANTICS.md#graph-code)), checked by its own certificate at
each signature its claim offers, entered with its receiver, parameters and
captured slots. Mutable locals, loops, `switch`, `try` and patterns inside a
closure are the same graph shapes as anywhere. Five kinds of closure still
keep term code (`funE`, `funRest`, `ctorE`, `makeCallable`): a generic
closure, one with a rest parameter, one with a parameter default, a class
constructor, and a callable object built by `Object.assign`. A statement
form not admitted in term code is refused there ([next steps](#next-steps)).

### SKJS is frozen

Past the tag `skjs-frozen`, the parser → OCaml producer → Lean pipeline is
the one that moves. The SKJS producer, the claims converted from it and the
suites built on its fixtures stay as they were at the tag;
`verification/run.sh` runs them only with `--suite all`, and they may fail on
arrays, which past the tag hold `Array.prototype`.

### SKJS operation contracts

Beyond checking SKJS's conclusions, the model can give its individual
operations semantic contracts, so a repair is judged against meaning rather
than the current implementation. `--check-skjs-operations` checks closed
subtype and expansion judgments SKJS exports under the substitution in force
at each ([closed operation export](REQUEST-PROTOCOL.md#closed-operation-export)).
The contracts:

1. **Substitution preserves meaning.** Substituting type arguments into
   syntax means the same as interpreting the syntax under the corresponding
   assignment.
2. **Expansion and normalization have explicit guarantees.** An exact
   expansion preserves denotation; an approximation establishes the
   appropriate inclusion; a cache preserves that guarantee in the state it is
   reused in.
3. **Successful subtyping establishes semantic inclusion**, `Δ ⊢ A ≤ B`
   implying `⟦A⟧η ⊆ ⟦B⟧η` for every `η` satisfying `Δ`, as the calculus's
   own `Sub.sound` does.
4. **Inference cannot invalidate earlier checks**: commitments are stable,
   preserved across state changes, or revalidated.

A generic parameter (every admissible `T`), an inference variable (a `T`
the checker may choose) and an object's hidden type argument (a fixed `T` it
may not choose) are different obligations and must not be confused. SKJS
repair progress is tracked in
[docs/skjs-improvement.md](../docs/skjs-improvement.md).

## The model in brief

Each section names what the model has and links the rules; none is
restated here.

### Values

`null`, `undefined`, Booleans, numbers (a number is the bit
pattern of its IEEE-754 double; the literal type `0` denotes both zeros),
bigints (the integer), strings, symbols (opaque identities), objects (a map
from property keys, strings or symbols, to locations), arrays, and functions
with call or construct code. Binary operators are one term, `arith`, whose
meaning is JavaScript's operation where it converts nothing: `+` concatenates
a string with any primitive but a symbol by `ToString` exactly (`Number::toString`
digit for digit), `%` is the exact remainder, relational operators compare
two numeric values or two strings, and `===` is `IsStrictlyEqual`
([operational language](SEMANTICS.md#operational-language)).

### Heap and contracts

Every location carries a stable invariant contract in
the world; heap satisfaction ties contracts to contents, and a write must
meet the location's contract. References are invariant views of storage, not
covariant containers. Functions are safe in every admissible future world
([types, worlds and heaps](SEMANTICS.md#computations-and-recursive-types);
[Ahmed 2004](REFERENCES.md#ahmed-2004)).
Recursive types are finite guarded graphs, interpreted by a budget-indexed
fixed point ([POSITIVE-TYPES](POSITIVE-TYPES.md); [Appel and McAllester 2001](REFERENCES.md#appel-and-mcallester-2001)).

### Current-content assertions

What a location holds now is separate from its contract. `{ value: boolean =
true }` records a Boolean contract and currently true contents. Observations
are duplicable facts: they neither narrow the contract nor grant writes
([semantics](SEMANTICS.md#current-content-assertions-and-postconditions),
[rules](PROGRAM-TYPING.md#current-content-rules-semantic-layer)). A
statement entry is an exact interface: its supplied types and observations
are the whole starting context, plus the distinct-location links the
extractor states (a private cell is a fresh allocation, apart from the fields
of older bindings and later literals). A write of a known primitive
establishes new contents, and one of a value whose type rules `undefined`
out that the cell holds some other value, read at its contract less
`undefined` (so `let x: T;` assigned an object on every path reads at `T`);
a call forgets every heap fact, since a callee may
write any location its operands reach and the model states no reachability.
Immutable values and slot equalities survive. A closure's entry claims must
follow from contracts, never from creation-time contents. Loop heads are
supplied, and every back edge must establish them
([checkpoints](PROGRAM-TYPING.md#source-observation-checkpoints)).

### Mutable bindings

A `let` and an assigned parameter are private cells
with a storage contract fixed where they are declared: the annotation, or
the producer's proposal (TypeScript's widened or evolved type), against which
the initializer and every write are checked. A closure holds the cell's
identity; a `const` copy holds a snapshot, and an unannotated constant of a
named union is held at the union's arms, as an annotated one is
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
$\alpha$-conversion, for `const`, `let`, parameters, patterns, closure
parameters, `for...of` and `catch` bindings in any body
([shadowing](PROGRAM-TYPING.md#derived-source-forms)). A mention above the
declaration, a closure's included, or in its own initializer is refused, as
JavaScript's temporal dead zone throws there.

### Objects and prototypes

An object's keys are fixed at its allocation; a
write stores at an existing location and never adds a key. A record type is
open: it constrains the keys it names and says nothing of others. An
**own-key bound** says which keys an object may own, $\mathsf{among}\,K$ or
$\mathsf{outside}\,N$ ([records](POSITIVE-TYPES.md#records)); a fresh
literal's own keys are exactly its written ones, which is how it meets a
dictionary or leaves out an optional field. An object may hold a prototype
under the reserved key `[[proto]]`, and a read of a key the object lacks
continues there (`readProto`). A class instance holds its class's prototype
object, whose methods it reads; a derived class's prototype links to its
base's. A private name `#x` is a key no code outside its class spells, a
symbol of its own: a private field an own key of each instance, a private
method the prototype's, a static one a binding; a copy takes none
([classes](PROGRAM-TYPING.md#classes)). Optional fields read an absent key as `undefined`, which holds only
without a prototype, so they require none. `readonly` is a view: a read
capability that withholds writes through that view without retyping the
location.

### Object literals

A literal allocates one object owning exactly the properties it writes, in
order. A spread of a literal is its fields; a spread of any other value is an
allocation from parts, copying the value's own enumerable string-keyed data
properties when it is evaluated
([allocation from parts](PROGRAM-TYPING.md#allocation-from-parts)): a class
instance's methods are its prototype's and are not copied, nor is an
`Error`'s non-enumerable `message`, nor a symbol-keyed property. A numeric
key is the property its `ToString` spells, and a computed key naming a
`unique symbol` constant (`Symbol.iterator`, or one the program makes) is that
symbol's key; `__proto__`, any other computed key and accessors are refused. An object pattern's rest is the same copy less the
named keys.

### Arrays

An array is one store of element locations under the reserved
store key and one object holding `Array.prototype` under `[[proto]]`, read
through the one array shape (`arrayClauseOf`,
[arrays](POSITIVE-TYPES.md#arrays)). Its own keys are outside $N$, the keys
`ArrayProto` provides, so `xs.map` reaches the prototype; it may own others,
as Skip's runtime tags managed arrays with a symbol key. Arrays are
**dense**: every index below the length holds an element, so an element write
is typed only in bounds or appending. Mutable arrays are invariant;
`readonly T[]` reads only and is covariant. Arrays are `Iterable<T>` through
their prototype's `[Symbol.iterator]`, a tuple through the readonly array of
its positions. An array's `length` is read from its store, in a statement and
in a closed expression alike. An array pattern's rest over a tuple of
required positions is reads; any other is a slice, a call of the trusted
`%RestFrom:k%` ([patterns](PROGRAM-TYPING.md#patterns)).

### Index signatures

A dictionary is a `dict` clause of index contracts, each over a **key class**:
every string key, the canonical numeric keys (a string some number's
`ToString` spells), or every symbol key
([records](POSITIVE-TYPES.md#records),
[source forms](PROGRAM-TYPING.md#index-signatures)). A read at a key the
object may lack is `V | undefined`. A mutable index is a **writable index
contract**.

#### Writable string index signatures

A mutable index signature lets code holding the dictionary add keys and
overwrite values at `V`, and TypeScript also treats it covariantly. Lowering
it to the readonly view would be unsound: a caller handed a dictionary of
`true` at `{ [key: string]: boolean }` could store `false` where the program
still reads `true`. So every present field under its class holds exactly
`V` (`dictCellT`), a mutable dictionary is invariant, and a readonly one is
never mutable. No program rule writes through an index. That code outside
the unit adds keys to a writable dictionary only at its contract, and only
keys of its class, is an assumption ([trust surface](#trust-surface)). Every
capability the checker grants on such an object is implied by the writable
contract, so a key added at `V` keeps them: covering a writable index
requires every index and optional field of the source over its keys to admit
`V`. This argument is informal.

A read `o[k]` whose key is one of several string or number literals tests
`k` against each and reads that member (NaN excluded).

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
  binding (`offersArity`); no subtyping widens an arrow's parameters.

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
alias read through its equation at the reference's arguments. A rest typed
by a function's type parameter in a definition, by an intersection, by a
tuple of several lengths or by what is no array is refused by its form. A rest typed by a binder is an argument pack,
whose contracts are over lists at the actuals' own level
([argument packs](POSITIVE-TYPES.md#argument-packs)). A closure claimed at
several signatures is checked once per signature. A spread among the actuals
is replaced by its store's elements once every earlier actual is a value;
spreads may sit at any position of fixed parameters or feed a generic
signature's inference, and an actual after a spread that runs code is refused
(the elements are read after every actual). A union callee is called at every
arm, its result the union of theirs; a method call on a union whose arms'
members differ reads and calls in one step dispatched on the receiver, where
every actual is a name or a literal. A callee that is a callable with fields
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
argument for `.call` and `.apply`. The receiver rule is strict mode's; `this`
in sloppy code is refused, and a sloppy function that reads no `this` is the
strict one, its receiver being unobservable. A class method declaring
`this: T` is refused: a method member is [host-relative](#method-members-are-host-relative),
its signatures stating no receiver apart from the host. `.bind` allocates a forwarding descriptor whose
receiver a later `.bind` or `.call` cannot replace (`callsT_bound`).

### Generic types

A generic application with methods is one row per
declaration and arguments for the module, lowered from an empty visit, so a
recursive family of applications is a finite graph
([one row per application](PROGRAM-TYPING.md#one-row-per-application)). A
generic method is a scheme row whose binders are coloured parameter rows; a
binder intersected with ground types is a meet row
([rows](POSITIVE-TYPES.md#parameter-and-scheme-rows)).

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
store key), and `x instanceof C` for a class the file declares
(`hasKey` of the key only `C`'s prototype owns). A test of a field of an
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
same iterator into a fresh array (`%Spread:K%`). None of these iterators has
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
end. A generator is refused: its body suspends at `yield`, which no term
expresses. No calculus rule changes: a call's callee is an assumption at its
declared type, or code the unit checks. An async function's
promise settles only to a primitive, the values that are never thenables
([nested promises](ECMA-CONNECTION.md#illustration-nested-promises)).
The model runs a body to its end; every point where other code can intervene
is an `await` or a call, across which only contracts survive.

## Trust surface

Everything the safety theorem does not establish. Each assumption enters as
a premise: an input slot of the unit at a declared type (`EnvOk` over the
unit's inputs, in the premise of `checkJson_safe`), a property of the host
the model's reading of an operation relies on, or the correctness of a
trusted tool. Where an item is stated in code, that code is the reviewed
text.

**Trusted tools.**

| Assumption | Where it is stated |
| --- | --- |
| The parser represents the source faithfully: it admits only the fragment, and its lowerings (unbraced arms, `switch`, `for`, templates, enums, optional chains, async forms, patterns, dead code, a shadowing local's renaming by the declaration TypeScript binds each reference to, a `let` nothing writes as a `const`, a written `let` pattern as a `const` pattern and `let`s, a static block as a closure called at once, `instanceof` of a class with a static `[Symbol.hasInstance]` as its call, a private name as its member's symbol, a rest parameter's alias equation, the iterator protocol of a program's iterable in a `for...of`, a spread and an array pattern, with its closing region) preserve JavaScript's execution. | `tools/fragment-parse.mts`, `fragment.mts` |
| Source extraction preserves control flow, lexical binding, evaluation order and annotations: which program point a claim is attached to is unproved. No source-to-graph preservation theorem exists. | `Source/Fragment.lean`, `Source/SourceExtraction.lean` |
| Decoding represents the submitted AST, declarations, claims and evidence faithfully. | `RequestJson.lean`, `SourceClaimJson.lean` |
| TypeScript's checker resolves each name to its declaration in the file's project, whose strict `tsconfig.json` (paths, links, library set, type packages) reflects the real build; a TypeScript error in a collected declaration or on an import it passes through refuses the graph. The parser checks TypeScript read the bytes it parsed. | `tools/declaration-graph.mts` |
| TypeScript's evaluation is trusted as its resolution is: a computed type (`typeof`, `keyof`, `T[K]`, template literal types, primitive intersections, mapped keys) means what its checker computes; an enum member's value is `getConstantValue`'s, which its emit writes; a `const enum` read is the member TypeScript binds it to; global member and overload resolution selects which declared signatures are assumed. | `tools/computed-types.mts`, `declaration-graph.mts` |
| The execution model agrees with JavaScript on the supported operations, including that Lean's compiled `Float` operations are IEEE-754's and `Float.pow` is C's `pow`, which `binop` corrects where `**` differs. | `Semantics/Calculus.lean`; edge cases in `Tests/SourceExtractionTests.lean` |
| Lean's kernel, its compiler (including the `@[csimp]` replacements, each proved equal to its definition) and the executed verifier binary are correct. | — |

**Assumed values.** Each is an input slot of the units that use it, at its
declared or stated type; nothing checks the code behind it, and each may
throw, which safety admits, but never return a wrong value.

| Assumption | Where it is stated |
| --- | --- |
| An imported value meets its declaration; a function declared with overloads meets every overload. | `IMPORT`, `OVERLOADS` in [PROGRAM-TYPING](PROGRAM-TYPING.md#imported-ambient-and-global-values) |
| An ambient declaration (`declare function`, `declare const`, `declare class`) holds of the value the environment supplies under that name; the declaration document lists it with the specifier `ambient`. | `AMBIENT`; `collectDeclarations` |
| A global variable outside the standard library (Node's `process`) meets its declaration at the members and calls the module selects, from the project's type packages, and no code the module does not see reassigns it. | `GLOBAL`; `selectGlobal` |
| Each standard library global meets its reviewed overlay entry: `console.log`; `BigInt`; `Symbol`, `Symbol.for`, `Symbol.keyFor` and five well-known symbols; `String` of a primitive; `Object.keys`, `Object.values`, `Object.entries` (and the generic two at a dictionary); `new Array()`; `new Error(m)`; `new Set`, `new Map` of an array, `new Date` of a primitive, `Date.now`; `JSON.parse` of a string and `JSON.stringify` of a `JsonValue`. | `globalsOverlay` in `tools/library-globals.mts`; [rules](PROGRAM-TYPING.md#library-globals) |
| `Array.prototype` meets `ArrayProto`: its natives `forEach`, `map`, `reduce` and `reduceRight` (with an initial value), `every`, `some`, `filter`, `slice`, `join`, `indexOf`, `lastIndexOf`, `includes`, `at`, `find`, `findIndex`, `sort`, `push`, `pop`, `shift`, `unshift`, `reverse` and `[Symbol.iterator]` behave as TypeScript declares them, at the listed receiver, without `thisArg`. Units allocating arrays read it from the input slot `[[Array.prototype]]`. | `overlay` in `tools/array-prototype.mts` |
| `String.prototype`, `Number.prototype`, `BigInt.prototype` and `Boolean.prototype` meet `StringProto`, `NumberProto`, `BigIntProto` and `BooleanProto`, each member an own property of that prototype (`split`, `replace`, `replaceAll` stated at a string pattern; `toLocaleString` without `options`), read from the slot `[[String.prototype]]` and so on. | `primitiveOverlay` in `tools/array-prototype.mts` |
| `Set.prototype`, `Map.prototype` and `Date.prototype` hold the listed natives, unmodified (`keys`, `values` and `entries` giving a host iterator of the collection). | `interfaceOverlay` in `tools/array-prototype.mts` |
| The intrinsics meet their signatures: `%Await%` yields what a promise settles to or throws its rejection; `%AsyncReturn%` and `%AsyncComplete%` settle an async function's promise to a primitive or `undefined` (also `Promise.resolve`); `%PromiseAll%` (`Promise.all`), `%PromiseReject%` (`Promise.reject`), `%NewPromise%` (`new Promise`, calling its executor at once); `%Iterate%` steps an array's iterator, reading the current length at each step; `%Iterate:string%` a string's, by code point; `%Iterate:Set%` a `Set`'s, in insertion order; `%Iterate:Map%` a `Map`'s, a fresh `[key, value]` array per entry; `%Iterate:Iterator%` a `SetIterator` or `MapIterator`, which is its own iterator; none of these iterators has a `return`; `%Spread:K%` is the fresh array of what `%Iterate:K%`'s step yields until it ends; `%RestFrom:k%` is the fresh array of an array's elements from `k` to its current length, as its iterator yields them after a pattern's `k` elements; `%ForIn%` gives the keys a `for...in` visits, strings. The job queue and a promise that never settles are not modelled. | `tools/intrinsics.mts`; [async](PROGRAM-TYPING.md#async-functions-and-await) |
| A thrown value is a value, of any type. | `Thrown` in `Safe` (`Semantics/Safety.lean`) |
| The runtime with the sound service binding meets its declarations: `InputCollections.get(definition)` returns the collection built from that definition at its types, or throws; resources are constructed with the request's `Json` parameters. | `ocaml-producer/upstream-sound/` |
| In the SKJS test environment, SKJS's import stubs describe the modules a test imports, and `skjs-environment.d.ts` the host's `process`, `__SKJS_show` and `__SKJS_show_expanded` as SKJS's builtins stub does, with the ES2022 library and no DOM (`console` restated); `Closed<T>` and `SKJS_Ignorable<T>` are read as `T`; an ambient class's untyped field is a readonly `unknown` field. These are premises of the coverage result only. | `ocaml-producer/skjs-environment/`; `STUB`, `ENV` |

**Assumed of the host.** Properties of every value a unit receives, on which
the model's reading of an operation relies.

| Assumption | Where it is stated |
| --- | --- |
| The caller contract: a value conforming to a structural annotation (a parameter, an import, a library result) is a plain data object, its stated string-keyed fields own enumerable data properties, not accessors or proxies, which a spread copies, and a class instance owns its private slots, keyed by their private names; a conforming function respects its contract across every future heap, callback effects included. Two such parameters may alias. `Error`'s `message` is the exception, held on a prototype the model gives it. | `RequestJson.verify_safe` quantifies over environments meeting the input types |
| A value whose trusted declaration types it `Function` has call or construct code. | [`Function`](PROGRAM-TYPING.md#library-types) |
| A value TypeScript types as `Set<T>`, `Map<K, V>`, `SetIterator<T>` or `MapIterator<T>` that a loop or spread iterates is the host's: its iterator is the realm's, and the prototypes it inherits (`%IteratorPrototype%` included) hold no `return` and are unmodified. Assumed of every such value a program receives; the fragment builds none but through the host: a `Set`'s and a `Map`'s type state their `[Symbol.toStringTag]`, a well-known symbol key no literal or class of the fragment writes, and no annotation of the fragment states a `SetIterator` or `MapIterator`. A host iterator a program's protocol steps (an array's, as an `Iterable<T>`) likewise has no `return` along its chain. | the iteration intrinsics' pick, `iterationKind` in `tools/declaration-graph.mts`; `writtenSymbol` in `tools/fragment-parse.mts` |
| Every object owning the array store key is a JavaScript array: every object the model allocates, and assumed of every object a program receives. `Array.isArray` is the native test. For `instanceof Array`, every array a program receives is of its realm and no object but an array inherits from `Array.prototype`. | `isArray` ([SEMANTICS](SEMANTICS.md#operational-language)); the `Array` entries of `library-globals.mts` |
| An array a program receives owns no key its prototype provides. | the $\mathsf{outside}\,N$ bound of the array shape |
| The model's reserved keys (the store key `[]` and every name in double brackets) are spelled by no source key, and an object a program receives is represented with its own keys apart from them. | `Fragment.sourceKey`, `reservedSourceKey` |
| `Object.prototype`, `Array.prototype` and `Function.prototype` own no string key but those `inKeyRefusal` lists (node's `Object.getOwnPropertyNames`); `String.prototype` and `Object.prototype` own no numeric key; `String.prototype` owns no `[Symbol.split]` or `[Symbol.replace]`; `Object.prototype` has no `toJSON`. | `inKeyRefusal` in `Source/Fragment.lean`; the overlay comments |
| Distinct JavaScript objects have disjoint field locations, which is how `===` on objects with a field is answered; only allocation creates an object value. | `Arith.eq` |
| Code outside a unit adds keys to a dictionary it holds at a writable index only at that index's contract and only keys of its class. The calculus has no step that adds a key. | [index signatures](#index-signatures) |
| A spread does not copy an own enumerable symbol-keyed property, which JavaScript copies; the result states no symbol key and is open, so nothing typed reads one. | [object literals](#object-literals) |
| The standard `Object.assign`, `Function.prototype.call`, `apply` and `bind` are the intrinsics the parser identifies by lexical provenance; the fragment cannot write those properties. | `tools/fragment-parse.mts` |
| A value of type `Promise<T>` is a realm promise, which resolution never fulfills with a thenable (it adopts one), so awaiting it yields a `T`: runtime and library promises, the program's `async` functions (`%AsyncReturn%` adopts), `Promise.resolve`, `new Promise`, `%PromiseReject%` and `%PromiseAll%`. A trusted generic signature (imported, ambient, library) is truthful about `Promise<T>` or `PromiseLike<T>` only at a `T` no thenable inhabits, so each type parameter such a position names is bounded by the non-thenable types. | `%Await%` and `nonThenable` in `tools/intrinsics.mts`, `promisedBinders` in `tools/declaration-graph.mts`; [async](PROGRAM-TYPING.md#async-functions-and-await) |

**Not yet proved.** Module composition: a unit's certificate assumes the
signatures of the module values it reads, each certified by its own unit;
the step-indexed argument that they compose is not a Lean theorem
([modules](#modules-and-code-units)).

## Fragment boundary

What the pipeline refuses on principle, each with its reason. Forms simply
not yet taken are [next steps](#next-steps); a search failure is neither.

| Construct | Refused because |
| --- | --- |
| Object growth: a write of a key the object's type does not have (`o.x = 5` on `{}`), a write of a writable optional field, a computed write through an index signature | Keys are fixed at allocation; the calculus has no key-adding write. |
| `new Array(n)`, `new Array(x)` with one argument | It makes an array with holes; an array type promises none. |
| An element write at an index not proven in bounds or appending | It could create a hole. |
| A mutable `Dog[]` as an `Animal[]`, a mutable dictionary of `true` as one of `boolean`, a readonly view as a writable one | Mutable storage is invariant: a write through the wider alias breaks the narrower one's contract. |
| Method bivariance (`Handler<Dog>` as `Handler<Animal>`), an override with narrower parameters, a narrower constructor at a construct signature | The member may be invoked with the wider argument. |
| A method as a function-typed property, method extraction, a write to a method member, `o.m?.()` | A method is host-relative; `o.m?.()` would call the tested value with a receiver the form does not save. |
| A record type where an index signature or a dictionary is expected (TypeScript's implicit index signature); width subtyping into an optional field; an array where a number index is expected | A record is open: it may own further keys at any type; an array has a prototype a dictionary lacks. |
| `declare let`, `declare var`, a module-level `let` or `var` | Module storage outside code may write during any call; the fragment has none. |
| An ambient `declare enum`; an enum member TypeScript computes no value for; a NaN or infinite member; a reverse key naming a member; an empty enum | The object is the environment's, or its keys are known only at run time, or it has no literal type. |
| Narrowing `unknown` by `instanceof C`, and a member read of the result | "An object whose chain holds `C`'s prototype has `C`'s fields" is a world invariant over every allocation, not a fact about a value of `unknown`. |
| `instanceof` of a constructor not declared at the file's top level (imported, ambient, a function, an expression); a class value as the operand of `in` | Nothing in the file says which prototype it gives its instances; its statics are bound apart. |
| `key in o` for a key the realm's prototypes hold, an array index, a `string` or numeric key; an operand with a primitive arm or `unknown` | The model would answer otherwise than JavaScript, or JavaScript throws. |
| Narrowing `number[] \| Foo` by `Array.isArray` to drop `Foo` | An array may carry `Foo`'s keys. |
| `===` between two operands that may both be objects without a field (functions, records of optional fields, `unknown`); narrowing by object identity | Such values have no identity in the model; a statement entry states no slot equality. |
| A user-defined type guard (`x is T`) or assertion function (`asserts x is T`), with a body or declared | Its promise relates the result, or the completion, to the argument, which no function type states. |
| An array assignment pattern writing a field (`[o.f] = e`) | Its target's reference is evaluated before its position is read and defaulted; the lowering writes locals only. |
| An accessor (`get`/`set`), `__proto__`, a computed key in a literal other than a `unique symbol` constant, a spread of a string, a function or a class value | The heap has data properties only; the key or copy is known only at run time; the model gives a closure a field JavaScript's lacks. |
| A literal or class member keyed by a well-known symbol other than `Symbol.iterator` (`Symbol.toStringTag`, `Symbol.toPrimitive`, …), but a class's static `[Symbol.hasInstance]` method, which `instanceof` calls | It changes how the host treats the object, which the model does not state; a tag would let it pass for a host collection, whose iteration is trusted. |
| An element read past a tuple arm's length (`const [a, b] = t` with `t: [number] \| [number, string]`); a slice rest in a closure's directly checked body | The read is `undefined`, which no element rule gives; the slice's call is graph code. |
| A rest parameter of a definition typed by a type parameter; one typed by an intersection, by a tuple with optional or rest elements, or by what is no array | A definition has no allocation rule for an array only an instance fixes (a function type's is a pack); the fresh array's meet has no representation; several lengths are several signatures; the collected array is no value of it. |
| A written `let` pattern in a `for` head; a test of a written `let` holding a union of objects | Its bindings are cells, which only a statement of a block lowers them to; a cell's known contents are primitive or merely no `undefined`. |
| An array pattern over a value that may not be an array | It would step the value's own iterator. |
| A class method declaring `this: T`; a generic class method; a constructor parameter with a default | A method member is host-relative; the closure's claim would be a quantified callable, which the claim format does not encode; construct code is a term over plain parameters with no default schedule. |
| A class member with a computed key other than a method's `unique symbol` constant or a static `[Symbol.hasInstance]`; an index signature in a class; a static block reading `this`; a generic class in inheritance | A method is a binding and a prototype key named by its plain name or its symbol; instances are what construction allocates; the block's receiver is the class value, whose statics are bindings of their own; a generic base's construction is quantified. |
| A class with a private name in inheritance; `#x in o` | A derived instance's base part is a copy, and a copy holds no private slot; the test asks for an own slot, where the model's key test walks the prototype chain. |
| A loop or an array pattern over an iterable whose iterator's type states no `return` | Leaving it early, or a throw out of its body, calls whatever `return` the iterator owns, and an open record type says nothing of that property. |
| A generator function (`function*`) | Its body suspends at each `yield` and resumes there on the next `next`, which no term of the calculus expresses. |
| `for await` | Its iterator's steps are promises the model does not adopt. |
| An array literal spread (`[...xs]`) other than the one element over a program's iterable | No literal lowering takes a spread ([next steps](#next-steps)). |
| An async function returning an object other than a promise of a primitive, a void async function returning a value, `await` of a non-promise object at its own type | JavaScript adopts thenables, and a record type does not rule out a `then`. |
| `String(o)`, `o + ""`, `new Date(o)`, `new Set(it)` of a non-array iterable, `JSON.parse` with a reviver, `JSON.stringify` with a replacer, of an array or an open record | The host runs client code (`toString`, `valueOf`, an iterator, a callback, a `toJSON`). |
| Relational comparison converting its operands (a string and a number, an object, two Booleans); `==` other than `== null`; `+` on a bigint, number–bigint arithmetic, a symbol in a concatenation | The conversion runs code or is not the primitive order; TypeScript refuses the throwing ones. |
| A library global both constructed and read through members, or both called and read through a method (`new Date()` beside `Date.now()`, `Symbol()` beside `Symbol.for`) | A class value or callable object with members has no clause. |
| Any library signature the overlays do not list (`Math.random`, `concat`) | Not reviewed; nothing is trusted by default. |
| A `this` read in sloppy code | Sloppy receiver conversion is not modelled. |
| An object literal, class or parameter property the source builds with a `then` member, which could be claimed as a `Promise` | A value of type `Promise<T>` is assumed a realm promise; the source must not forge one. |
| A `let` binding captured by a closure in a `for` loop | JavaScript copies it per iteration. |
| `this` before `super(...)`; a statement reading `this` before the instance is complete | The instance is allocated at the end; no term stands for the uninitialized binding. |
| A base class declared later, imported, ambient, a library class (`extends Array`), or an expression | Nothing in the file says what its constructor allocates. |
| A static method that reads `this`; `super` in a static member; a mutable static field | Statics are module bindings, exact only when immutable; a static method's receiver is whatever its call passes, and its `super` the base's constructor, not the prototype `super.m(...)` reads. |
| A catch binding annotated other than `unknown`, or destructured | Anything may be thrown. |
| A template literal type with a `${string}` hole; a computed type over a type parameter; `keyof` with a unique-symbol key; `typeof` of an unannotated binding or of a class with statics | No term of the fragment states it exactly. |
| TypeScript's `any` in the checked module's own annotations; a contextual closure parameter TypeScript types `any` | It states no contract. |
| An intersection Lean cannot represent, or that normalizes to nothing (`number[] & { map: number }`) | Refused rather than verified vacuously. |
| An empty module (no function, no initialization code) | Accepting it would check nothing. |

## Lasting decisions

One line each; the reason is the one the design keeps.

- **Arrays are dense.** Accepted programs never create a hole, so iteration,
  spreads, `.apply`, `find` and `T[]`-into-rest need no `undefined`.
- **Arrays own none of `ArrayProto`'s keys and may own others.** An exact
  bound would make every tagged array type empty and verify its readers
  vacuously.
- **A fresh literal has exact keys; an existing record is open.** Only
  allocation establishes absence.
- **Enum types are their value sets.** Any number is not a numeric enum;
  two enums with the same values are one type.
- **`in` tests own keys along the prototype chain the model holds**, and
  refuses keys the realm's prototypes hold.
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
  spellings of one value are one singleton; the literal type `0` is both
  zeros.
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

Open design work, each a known gap with the reason it is open. Coverage
numbers and the tasks sized for agents are in
[SKJS-COVERAGE](ocaml-producer/SKJS-COVERAGE.md#proposed-tasks).

**A connection to ECMA-262.** Proving the calculus faithful to the
specification and the host's stated types as lemmas would turn most of the
trust surface into theorems; the expected results and their cost are in
[ECMA-CONNECTION](ECMA-CONNECTION.md).

**Closures still on term code.** Each should become graph code, so that
`Expr.termBody` and the term closure rules go away:

- a rest parameter needs variadic graph code: invocation collecting the
  actuals past the fixed parameters into a fresh store in slot 0, as
  `variadic` does, and a `restsT` lemma for it where `restsT_of_graph` now
  discards them;
- a parameter default needs entry nodes, a tag dispatch on `undefined` at the
  parameter's slot first in the graph, as a function's default already is,
  with `parameterOrder`'s deferred closures as statements;
- a generic closure needs its code checked universally, one code request at
  its binders' parameter rows (`checkCodes_reassign` already makes the table
  assignment-free); a throw inside one then comes for free;
- a class constructor needs construct-only graph code, a `ctorE` for graph
  code at construct signatures with `undefined` for the receiver; constructor
  defaults and rests follow;
- a callable object built by `Object.assign` needs `makeCallable` over graph
  code, one table entry per advertised overload.

**Generic methods with their own binders**, and a generic closure inside a
generic body: typing one needs scheme introduction in the program typing, a
closure at a scheme row whose body is checked at every reassignment of the
scheme's binders. With it, the direct rigid checker (`GenericSource`) can be
retired once the graph path reads dependent bounds (`U extends T`).

**`Promise<A> ≤ Promise<B>`**, and generally two applications whose methods
are generic: relating them needs a subtyping rule for quantified signatures,
instantiating the target's binders rigidly and the source's at them.

**The array-coherence heap invariant.** `Array.isArray` narrowing a record
arm to `readonly unknown[]`, and `instanceof C` narrowing `unknown`, need an
invariant of every object a program receives or allocates (an object owning
the store key holds a dense store and `Array.prototype`; an object whose
chain holds `C`'s prototype meets `C`'s type). That is a change to the
safety theorem's heap premise; until then such uses are located search
failures, never wrong verdicts.

**A key-adding write.** Object growth and writes through an index signature
need a calculus step that adds a key, typed where no other reference to the
object exists, changing its own-key bound. `Object.assign(t, s)` and a
spread into an index signature (a result clause with an index, every copied
location at its type) follow.

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
it. An element read past a tuple arm's length needs a rule reading
`undefined` beyond an exact length.

**Remaining source forms.** Assignment patterns into fields: each
element's target reference (receiver, computed key) evaluated into slots
before the position is read and defaulted, then a field write, where
`arrayAssigns` writes locals only. A method call on a union of primitives,
which needs one callee contract its receiver meets. A source binder used both
as a pack and as an array value. Explicit type arguments on an element call,
which reach an element only as a generic closure's quantified claim. An
instance method reading its class's statics, which are bound after the
methods, and a compound assignment of an instance field (`this.n++`).
User guards and assertion functions: the promise is a contract a
conjunction of arrows states, `(x: A) => boolean` with
`(x: Exclude<A, T>) => false` (an assertion function's `=> never`), which the
body is checked at, as a closure at each of its signatures; a caller narrows
through a fact the call leaves tying its result slot to its argument slot,
"an argument in `Exclude<A, T>` gave `false`", which the branch on the
result turns into a slice of the argument. Such a fact is about a type's
meaning, world- and level-indexed, where current-content facts are not; it
needs its own place in the knowledge a statement entry states.

**Precision.** Retaining heap facts across calls needs a proved
reachability or noninterference statement; set-valued clause covering (an
arrow against a union of arrows) needs a covering relation of another arity;
a vacuity escape for contradictory reference conjunctions
(`Ref null ∧ Ref bool ≤ Ref (null ∨ bool)`) is true and not derivable; the
producer's arrow search builds no nested `combine`.

**Source-to-graph preservation.** Structural properties of the lowering
(successor validity, freshness, binding resolution) can be proved in Lean
over the AST it already has; semantic preservation needs an execution
semantics for the source fragment. Either moves trust from the extractor to
definitions that are easier to review.

**SKJS operations.** Extend the closed operation export beyond the
primitive, cell and arrow fragment, so a failing SKJS judgment is located at
the operation rather than at a later program-point claim.
