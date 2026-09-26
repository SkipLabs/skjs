# SKJS coverage by the OCaml pipeline

How much of what SKJS accepts in its own test suite the pipeline
(`check.mts`: parser → OCaml producer → Lean search and check) verifies, what
stops the rest, and where the two disagree because SKJS is wrong.

**2,444 verified + 88 refused on principle = 2,532 of 2,674 done;
142 gaps, 0 unexplained.**
Of the 88 refused on principle, 10 are units of confirmed SKJS
unsoundnesses; the classes are defined in the method
([refusal classes](#method)) and counted [by class](#refusals-by-class).

**2,444 of 2,674 SKJS-accepted units verify (91.4%); 1,821 of 2,026 accepted
functions (89.9%).** 291 of the 377 files with an accepted unit verify entirely.
Five families of SKJS-accepted functions that the pipeline reaches and refuses
are real SKJS unsoundnesses, each with a runtime witness that SKJS accepts and
node crashes on ([below](#suspected-skjs-unsoundnesses)).

Rerun:

```sh
node verification/ocaml-producer/skjs-coverage.mts --skjs --width 3   # about 220 s
```

It writes [skjs-coverage.json](skjs-coverage.json) (summary, one row per unit,
one line per row, so a rerun's movement is a line diff). `--skjs` runs SKJS in
Docker from the main checkout (`SKJS_ROOT`, `SKJS_BIN`, `DOCKER_IMAGE`,
`SKIP_DIR` override); without it the expectation markers alone decide.
`--only <substring>` narrows the corpus, `--keep` keeps check artifacts,
`--out` places the derived files (default `$TMPDIR/skjs-coverage`). The script
is not part of `verification/run.sh`.

## Method

**Corpus.** Every TypeScript file the SKJS harness type-checks with a verdict:

| Suite | Harness verdict | Files | Units | Accepted | Verified | Accepted functions | Verified functions |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `tests/expect-error` | `@ts-expect-error` / `@skjs-expect-error` name the next non-annotation line (`tests/Helpers.sk` `findExpectErrors`); `@skjs-expect-warning` is not an error | 399 (374 with units) | 3,883 | 2,458 | 2,230 | 1,863 | 1,660 |
| `tests/callgraph` | no error allowed | 25 | 59 | 59 | 57 | 51 | 49 |
| `tests/constprop` | no error allowed | 14 | 66 | 66 | 66 | 49 | 49 |
| `tests/deadcode` | no error allowed | 7 | 27 | 27 | 27 | 16 | 16 |
| `tests/cfg` | no error allowed | 7 | 22 | 22 | 22 | 21 | 21 |
| `tests/projects` | expect-error markers, under the project's tsconfig | 24 of 68 | 44 | 34 | 34 | 23 | 23 |
| `tests/ts-conformance/cases` | lines listed in `reference/*.errors.txt` | 4 | 9 | 8 | 8 | 3 | 3 |
| **total** | | **480** | **4,110** | **2,674** | **2,444** | **2,026** | **1,821** |

Excluded (79 files, listed in the JSON with reasons): `ts-conformance/not-supported`
(31) and `callgraph-unsupported` (4) assert only that SKJS reports errors;
project files that import each other (26), whose tsconfig disables strictness,
a strict sub-option or sets a non-default truthiness (11), or extends another
config (5); and 2 files the project's own tsconfig does not check.
`examples/src` is also SKJS-validated but outside this corpus.

**Units.** The pipeline verifies whole files and stops at the first blocker,
and SKJS test files mix accepted and rejected functions, so each file is split.
Every top-level value-level statement (function with a body, class, variable
statement, top-level code other than an empty `;`) is a unit. Its derived file holds it plus, in source
order, every top-level statement it reaches by name, transitively (aliases,
interfaces, ambient declarations, other functions, overload signatures). A
unit is marker-accepted when no statement of that closure has an error line
(1,364 units are rejected themselves, 70 through a dependency).

**SKJS confirmation.** SKJS (`check --import-stubs import-stubs`, default
truthiness, as the harness runs it) is run once over all 2,676 derived files of
marker-accepted units. It rejects 2: two `*-prettier-ignore.ts` files whose
expected *parse* errors the markers attribute to the wrong statement. They are
not counted. The remaining 2,674 are the accepted corpus.

**Environment.** SKJS checks a test in the environment its stubs give
(`--import-stubs import-stubs`); the pipeline gives each derived file the
same one, a project of its own extending
[`skjs-environment/tsconfig.json`](skjs-environment/tsconfig.json): a bare
import specifier resolves in `import-stubs`, and
[`skjs-environment.d.ts`](skjs-environment/skjs-environment.d.ts) restates the
builtins stub's globals TypeScript's library lacks (`__SKJS_show`, `process`,
`StringRecord<V>`, and `Closed<T>` read as `T`). These declarations are
assumptions of the result, as an import's are
([trust surface](../DESIGN.md#trust-surface)).

**Pipeline.** Each derived file goes through `checkApart` (exactly
`node check.mts <file> --project <its project>`), 10 at a time, with
`check.mts`'s 30 s step timeout.
A unit whose run ends in an infrastructure error (a step timeout, the
TypeScript service's "context canceled" under load — seen once) is run again
alone; no timeout remained. Outcome rows: `verified`, or the first blocker with its phase
(`source` = parser gate, `proposal` = producer `unsupported:`, `search` =
Lean found no derivation or refused a source form, `error`), its normalized
reason, its feature group, and where it lies: in the unit's own statement
(`self`), in a statement its closure brought (`dependency`), or `unknown`.

**Attribution.** A verified run counts for a unit only when it checked the
unit's own code: a function unit is among the functions `check.mts` reports
verified, and any other unit (a class, a variable statement, top-level code)
contains a statement of the module initialization it reports checked
(`initialization`, the spans of the initialization unit Lean checked). A
verified run that checked neither would be the row `unverified`,
"attribution: the verified run checked none of this unit's own code"; none
is.

| Phase of first blocker | Units |
| --- | ---: |
| verified | 2,444 |
| source (gate) | 85 |
| proposal (producer) | 32 |
| search (Lean) | 113 |

**Refusal classes.** The project's goal is that every accepted unit either
verifies or is refused for a specific, principled reason. Each accepted unit
that does not verify is put in one class, by its first blocker's key
(`class` on its row, `summary.byClass`), through the table `CLASSES` in
[skjs-coverage.mts](skjs-coverage.mts), one entry per reason with its
justification; the first entry matching the key decides:

- **principled** (P): the pipeline refuses because the construct is unsound,
  not faithful to JavaScript, or rejected by TypeScript itself, or because
  its soundness would need an assumption the project declines; nothing else.
  Each such entry is a row of the fragment boundary's
  [refused on principle](../DESIGN.md#refused-on-principle): TypeScript's
  implicit index signature, covariant writable storage, method extraction,
  `instanceof` narrowing `unknown` (an object gets a class's prototype without
  its constructor), a constructor or base class from outside the file, an
  iterator whose type states no `return`, thenable adoption, a contextual
  `any`, an empty intersection, and code or declarations TypeScript rejects.
- **gap** (G): a sound construct the pipeline does not yet support: a
  [next step](../DESIGN.md#next-steps), or a [model limit](../DESIGN.md#model-limits)
  whose obstacle the entry names (a representation limit, "no term of the
  fragment states it exactly", object identity without fields, sloppy
  receivers, module storage, a computed type over a binder); so is any reason
  the table does not match (`summary.unmatchedReasons`, so a new refusal is
  seen, never counted done).
- **unexplained** (U): a refusal that names no cause: Lean's search found no
  derivation (`evidence search failed`, `cannot establish …`), which names
  the failed obligation and, on its `obligation:` line, what was not
  established, but not why; a crash, a timeout, a verified run that checked
  none of the unit's code.
- **SKJS unsound** (S): a unit of a
  [confirmed SKJS unsoundness](#suspected-skjs-unsoundnesses) family with a
  witness that SKJS accepts and node crashes on (`SKJS_UNSOUND`, by unit).
  Its refusal is correct: it counts as done, beside the principled ones. A
  unit of that list that verifies is reported as a warning.

For an accepted unit $u$ with first blocker key $k(u)$, and `CLASSES` the
list $(c_1, r_1), \dots, (c_n, r_n)$ of a class and a pattern:

$$
\mathrm{class}(u)=
\begin{cases}
\mathsf{verified} & \text{if } u \text{ verifies}\\
\mathsf{S} & \text{else if } u \in \texttt{SKJS\_UNSOUND}\\
\mathsf{U} & \text{else if } u \text{ ended in an error}\\
c_i & \text{else if } i=\min\{\, j \mid r_j \text{ matches } k(u) \,\}\\
\mathsf{G} & \text{otherwise}
\end{cases}
$$

Done is verified, principled or SKJS unsound: $V + P + S$ of the accepted
$N = V + P + S + G + U$.

**Caveats on the method.**

- Counts are *first* blockers. A group's count is an upper bound on what
  widening it alone unlocks; the next blocker is not measured.
- Name-based closure over-approximates (a local shadowing a top-level name
  drags that declaration in) and drops unreferenced top-level statements. SKJS
  confirmation guards acceptance, not the pipeline's view.
- A derived file of a module is written as a script (`export {}` is itself
  outside the fragment).
- A derived file is written beside the others, not beside its source, so a
  relative import of a sibling test file (`symbols.ts` importing
  `./symbols-export.js`) does not resolve: 1 unit.
- `where` is `unknown` for 13 refusals, 12 of them the producer's, which
  name no location.

## Refusals by class

Every accepted unit that does not verify, by the class and reason its first
blocker's key is given (`summary.byReason` and `summary.byClass` of
[skjs-coverage.json](skjs-coverage.json); definitions in the method,
"Refusal classes"). P principled, S SKJS unsound, G gap, U unexplained.
*Review* marks a gap that could be argued otherwise.

| Class | Units |
| --- | ---: |
| verified | 2,444 |
| principled (P) | 78 |
| SKJS unsound (S) | 10 |
| gap (G) | 142 |
| unexplained (U) | 0 |
| **accepted** | **2,674** |

| Class | Reason | Units | Files | Why |
| --- | --- | ---: | ---: | --- |
| P | TypeScript refuses the code | 37 | 23 | TypeScript itself rejects the program or a declaration it depends on |
| P | `instanceof` of a constructor from outside the file | 7 | 3 | nothing in the file says which prototype it gives its instances (Fragment boundary) |
| P | `instanceof` narrowing `unknown` | 7 | 3 | an object gets C's prototype without C's constructor running (`Object.create(C.prototype)`, `Object.setPrototypeOf`, `Reflect.construct`): the brand is no evidence of C's fields, and assuming it of every value a unit receives is false of ordinary JavaScript (Fragment boundary) |
| P | implicit index signature | 7 | 2 | TypeScript's implicit index signature is unsound: a value of a type literal may carry other keys of any type |
| P | `await` of a non-promise object, an async result that may be an object: thenable adoption | 5 | 4 | JavaScript adopts thenables and a record type does not rule out `then`, its own or its prototype's: an awaited value is a realm promise or a primitive, an async result a primitive (Fragment boundary) |
| P | iterator without a stated `return` | 3 | 3 | IteratorClose calls whatever `return` an open record owns (Fragment boundary) |
| P | method extraction | 3 | 2 | a method read off its object loses its receiver; TypeScript's typing of it is unsound (Fragment boundary) |
| P | an empty intersection | 2 | 2 | no value of the model has both operands' shapes (a branded primitive, a callable array, an array owning a prototype's key): TypeScript keeps such a type, and verifying it would be vacuous (Fragment boundary) |
| P | a mutable tuple's `length` at its arity, a position past it | 2 | 2 | `push` is allowed on a mutable tuple: TypeScript's literal length, and its `undefined` past the positions, are unsound |
| P | invariance of writable storage | 2 | 1 | TypeScript relates writable storage covariantly, which is unsound (Fragment boundary) |
| P | a base class from outside the file | 1 | 1 | nothing in the file says what its constructor allocates; trusting it is an assumption declined (Fragment boundary) |
| P | a contextual `any` parameter | 1 | 1 | `any` states no contract (Fragment boundary) |
| P | a `this`-typed function as a receiver-indifferent callback | 1 | 1 | the callback type admits any receiver, the function requires its own: TypeScript's relation is unsound |
| S | aliased views of an empty object literal | 6 | 1 | witnessed below |
| S | `typeof c === "function"` on a class instance is `never` | 1 | 1 | witnessed below |
| S | an inferred literal type through a generic declaration is closed | 1 | 1 | witnessed below |
| S | `await` passes a record through | 1 | 1 | witnessed below |
| S | a body falling off its end at a binder bounded by `void` | 1 | 1 | witnessed below |
| G | generics: generic closures, methods, function types, dependent bounds | 16 | 10 | generic closures, generic methods and binders as packs are open (Next steps) |
| G | rest parameters (intersection, type parameter, declaration binder) | 14 | 5 | a representation limit: no allocation rule for the collected array at that type |
| G | `keyof` with unique symbols, `typeof` of inferred bindings, template patterns | 9 | 5 | no term of the fragment states the type exactly (a singleton symbol type, an inferred method, a string pattern): a representation limit |
| G | a named function at a longer signature | 8 | 4 | sound: a function declaration of fixed arity discards the actuals past its parameters, so its code meets the padded signature (`restsT_of_graph`); its slot is its annotated signature, checked by its own unit, and needs to carry that promise too (the slot a claim its unit checks, as a closure's offered signatures are) |
| G | a key-adding write on an object another reference may hold | 8 | 4 | typed only on an unaliased local; alias tracking beyond that is open (DESIGN, Next steps) |
| G | a method with a `this` parameter | 8 | 3 | sound: TypeScript checks the receiver at each call; a method member is host-relative, its contract states no receiver apart from the object it is read from, so a member usable only on hosts of another type needs a member form stating it (DESIGN, Method members are host-relative) |
| G | object identity without fields | 8 | 2 | a model limit: `===` on objects is identity, and the model's objects without a field (closures, records of optional fields) carry no location to compare; a statement entry states no slot equality (DESIGN, Next steps, Keys known only at run time) |
| G | a read at a `for...in` key under `!` | 8 | 1 | sound where nothing runs between the loop's step and the read: a plain data object inherits no enumerable key (Object.prototype owns none), so the key the loop yields is one the object owns then, at its index's contract; adding it needs a fact relating the key's slot to the object's own keys, which no statement entry states (a relation, as a user guard's is, DESIGN Next steps) |
| G | object literal spreads of functions, class values, arrays, strings | 6 | 4 | the copy's keys are known only at run time (a string's or an array's indices, what was assigned to a function), and the model's closure and class value are no objects of JavaScript's own properties (a closure's code, a class's statics bound apart): a merge would copy what JavaScript does not; a representation limit |
| G | `this` in sloppy code | 6 | 3 | a model limit: the receiver rule is strict code's; sloppy code's replacement of an undefined or primitive receiver by the global object or a wrapper has no term |
| G | enum forms: computed members, an empty enum | 5 | 1 | keys known only at run time; an empty object has no record: representation limits |
| G | cells after a step that may write them | 4 | 3 | a call forgets heap facts: needs a reachability statement (Next steps, Precision) |
| G | `extends` a library constructor | 4 | 1 | a model limit: construction allocates an ordinary object at the class's fields; a library constructor's instance (an array holding the subclass's prototype) has no construction rule, and its members are read at the library type's meaning |
| G | `Array.isArray` on `unknown` | 4 | 1 | the array invariant is a fact of record and dictionary types; `unknown` is also a handler's binding type, and the throw outcome states nothing of a thrown value: needs the throw outcome to carry the invariant (Next steps) |
| G | a guard finding an object where a field or cell holds one beside a primitive | 3 | 2 | what a location is known to hold is a union of primitives, or its contract less `undefined`: a guard's `!== null` of one holding an object states nothing (DESIGN, Current-content assertions); needs a contents fact of its contract less the primitives the guard excludes |
| G | a spread argument to `new` | 3 | 2 | the call's lowering of a tuple's spread into its positions is not written for `new`; into a variadic construct signature no rule constructs (`ctorRestsT` has neither an introduction from code nor an elimination by `new`, DESIGN Next steps, Constructor rests) |
| G | class forms: constructor rests and defaults reading `this`, computed members, index signatures, statics, private names | 3 | 1 | no rule constructs at a variadic construct signature, the instance is allocated at the constructor's end, statics read late, private slots in inheritance (Next steps) |
| G | `length` over an array-or-record union | 2 | 2 | needs a dispatch on `Array.isArray` reading an array's length from its store and a record's from its field, with the array invariant excluding an own `length` key (Next steps) |
| G | source forms left | 2 | 2 | remaining source forms (Next steps) |
| G | absent-key and dictionary presence facts | 2 | 2 | needs a clause stating an absent key or dictionary presence |
| G | a key-adding write of a symbol key, a spread of a symbol-keyed property | 2 | 2 | the copy step copies string keys only (Trust surface: JavaScript also copies an own enumerable symbol-keyed property) |
| G | relational comparison of operands not both numbers or both strings | 2 | 1 | a model limit: the model's comparison is of two numbers or two strings; `undefined` or a Boolean converts without running code (to NaN, to 0 or 1), which no rule states (an object's conversion runs code and stays refused, but the refusal does not tell them apart) |
| G | calls: spreads, `Object.assign`, array literal spreads | 2 | 1 | iteration and call forms left open (Next steps) |
| G | well-known symbol keys | 2 | 1 | the model does not state how the host treats them |
| G | generic methods: `then` through a callback returning a promise, `catch` | 2 | 1 | producer inference through an application (a callback returning a promise); an accumulating binder's family is truncated a level early under instantiation (Next steps) |
| G | `.call`, `.apply`, `.bind` of a function value read from an object | 2 | 1 | they are Function.prototype's only by lexical provenance (a local function, whose properties the fragment cannot write): a function value read from an object may own a `call` of its own; needs the caller contract to state that a received function owns none of them (a method's is principled: extraction) |
| G | an ambient enum | 1 | 1 | a representation limit: an enum type is its value set, which an ambient declaration need not state, and the declaration reader has no ambient enum value |
| G | a spread of a dictionary | 1 | 1 | needs the key-adding write's spread into an index (Next steps) |
| G | a key-adding write at a runtime string key | 1 | 1 | the model reserves `[]` and `[[proto]]`; a representation choice, not unsoundness |
| G | a key-adding write at one of several literal keys | 1 | 1 | needs a dispatch on the key |
| G | a spread's written field typed per arm of the expected union | 1 | 1 | a copy's field is allocated at one type for every arm of its operand; a copy per arm, at that arm's contract, is not lowered |
| G | library globals not reviewed | 1 | 1 | a library signature is trusted only once reviewed |
| G | reads the producer holds on no object | 1 | 1 | producer typing of the receiver: a bounded binder instantiated at its bound where TypeScript infers an object literal's type |

No reason is unmatched (`summary.unmatchedReasons` is empty), and no unit of a
confirmed SKJS unsoundness verifies (`summary.skjsUnsoundVerified`).

## Groups

Units whose first blocker is in the group, by language feature, from
`summary.byGroup` of [skjs-coverage.json](skjs-coverage.json) (the table
`GROUPS` in [skjs-coverage.mts](skjs-coverage.mts); `self`: in the unit's own
statement; `dep`: in a dependency; a unit whose blocker names no location is
in neither). A group mixes classes: which of its units are principled is the
table above.

| Group | Units | self | dep | Files |
| --- | ---: | ---: | ---: | ---: |
| TypeScript refuses the code too (the pipeline follows TypeScript's types) | 38 | 30 | 8 | 24 |
| destructuring and rest/default parameters | 14 | 9 | 5 | 5 |
| in / instanceof / typeof tests | 14 | 7 | 0 | 6 |
| classes: modifiers, inheritance, fields, parameter properties, receivers | 14 | 7 | 7 | 6 |
| implicit index signatures: a record at an index signature (`Closed<T>` read as `T` among them) | 14 | 14 | 0 | 3 |
| type forms: literal types, keyof, indexed access, mapped, object, index signatures, intersections, method signatures | 11 | 10 | 1 | 7 |
| generics: constraints, explicit type arguments, rigid types, generic function types | 11 | 8 | 2 | 8 |
| object growth: a key-adding write on an object another reference may hold, a dynamic index write | 11 | 11 | 0 | 5 |
| object literal members (methods, accessors, spreads) | 10 | 9 | 0 | 5 |
| calls: overloads, .call, spread arguments, Object.assign, arrow callee | 10 | 6 | 3 | 6 |
| a named function at a signature binding more parameters, or indifferent to the receiver it requires (its type is its annotated signature) | 9 | 8 | 1 | 5 |
| arrays and open records: `Array.isArray` on `unknown`, `length` of an array read as a record's | 8 | 8 | 0 | 5 |
| a non-null assertion on a read at a for...in key (that the object owns the key relates two values) | 8 | 8 | 0 | 1 |
| cells read at their contract (contents known only as primitives or as no `undefined`, and forgotten across a step that may write them) | 7 | 5 | 0 | 5 |
| tests on a value of a type parameter or `unknown` (no rule narrows a parameter row to its meet `T & number`; no object identity) | 7 | 7 | 0 | 4 |
| enums | 6 | 0 | 6 | 1 |
| equality: objects without a field (no identity), loose equality | 6 | 6 | 0 | 2 |
| sloppy (non-strict) code | 6 | 4 | 2 | 3 |
| iterables the program defines: an iterator whose type states no `return`, a spread or a pattern the protocol's lowering does not place, a well-known symbol key other than `Symbol.iterator` | 5 | 4 | 1 | 4 |
| await of non-promises and unions (the await bound) | 5 | 5 | 0 | 4 |
| relational operators (< <= > >=) and ** | 2 | 1 | 1 | 1 |
| dictionaries: a spread of one, a key `in` found in one | 2 | 2 | 0 | 2 |
| generic methods: two declarations' instances related, a binder inferred beside an application of it or accumulated in one (Promise) | 2 | 2 | 0 | 1 |
| reads on unions/primitives (field/index read on non-object, string keys) | 2 | 1 | 0 | 2 |
| invariance: a writable element or field at a wider one (TypeScript relates them covariantly) | 2 | 2 | 0 | 1 |
| search: no derivation found (evidence search failed) | 1 | 1 | 0 | 1 |
| compound and update assignments (x++, \|\|=, ??=, a[i] op=) | 1 | 1 | 0 | 1 |
| an optional key found `undefined` (the key may be absent) | 1 | 1 | 0 | 1 |
| other source forms | 1 | 1 | 0 | 1 |
| type aliases and names the declaration reader cannot resolve | 1 | 0 | 1 | 1 |
| library globals as values (Array, Symbol, Error, Promise, Set, Map, Date, JSON, …) | 1 | 1 | 0 | 1 |
| **total** | **230** | | | |

## Suspected SKJS unsoundnesses

Divergences: SKJS-accepted units the pipeline parses and proposes, and Lean
then refuses (113 units in `search`, `summary.reachedButRefused`). The
source-form refusals Lean states explicitly are fragment boundaries. The rest
were read obligation by obligation: all read are pipeline incompleteness
except four families below; the fifth is refused by the producer.

### Confirmed: aliased views of an empty object literal (`tests/expect-error/obj-literal-indexes.ts`)

Two annotated views of one `const t = {}` with incompatible field or index
types are both accepted, so a write through one is read at the wrong type
through the other. SKJS's own comments mark these lines `TODO(#678): main
accepts this`; the pipeline refuses them in search (`binding-annotation`
obligation on the second view): `testAliasMutableOptionalThenIndex`,
`testAliasReadonlyOptionalThenIndex`, `testAliasWidenedGrantThenIndex`,
`testSameViewInBranchThenAfter`, `testViewInsideLoop`,
`testAliasNeverIndexThenMutableOptional`. (Its `testAliasMutableOptionalThenOptional`
and `testAliasTwoReadonlyOptionals`, disjoint or read-only views, are sound and
also refused: incompleteness.) `testAliasMutableSymbolOptionalThenIndex` is the
same shape with a symbol key.

Witnesses. SKJS (`skjs check`, default truthiness) reports no error for each;
`node` throws `TypeError` at the marked line:

```ts
function n1(): string {            // straight line: index view, then optional view
  const t = {};
  const f: { [k: string]: number } = t;
  f["a"] = 1;
  const g: { a?: string } = t;
  const v = g.a;
  if (v === undefined) return "";
  return v.toUpperCase();          // TypeError: v.toUpperCase is not a function
}
const r: string = n1();
```

```ts
function w6(): string {            // testAliasReadonlyOptionalThenIndex
  const t = {};
  const f: { readonly a?: number } = t;
  const g: { [k: string]: boolean } = t;
  g["a"] = true;
  const a = f.a;
  if (a === undefined) return "";
  return a.toFixed(1);             // TypeError: a.toFixed is not a function
}
const r6: string = w6();
```

Also accepted and crashing: optional view then string index view
(`testAliasMutableOptionalThenIndex` + a write), widened optional then index
(`testAliasWidenedGrantThenIndex`: `h.a = "x"` read as `number`), the index
view inside an `if` or a loop followed by an optional view
(`testSameViewInBranchThenAfter`, `testViewInsideLoop`), and the symbol-keyed
variant. Not witnessed: `testAliasNeverIndexThenMutableOptional`, because SKJS
refuses any read through a `never` index (the closed type), so the bad value
cannot be observed through `b`.

### Confirmed: `typeof c === "function"` on a class instance is `never` (`tests/expect-error/callability.ts#testInstanceTypeofFunction`)

SKJS narrows a class-instance type to `never` under `typeof … === "function"`
("a class instance is not callable"), but accepts a callable value at that
class type when it comes from `Object.assign(arrow, fields)`. The pipeline
refuses `const n: never = c` (it cannot derive `never`). An interface type is
not narrowed this way (SKJS rejects the same witness with `interface I`), so
the defect is class-specific:

```ts
class C {
  a: number = 1;
}
function g(c: C): string {
  if (typeof c === "function") {
    const n: never = c;
    const s: string = n;
    return s.toUpperCase();        // TypeError: s.toUpperCase is not a function
  }
  return "ok";
}
function mk(): C {
  const f = Object.assign(() => 1, { a: 1 });
  return f;
}
const r: string = g(mk());
```

Either the narrowing or the assignment of `Object.assign`'s callable result to
`C` is wrong; SKJS does reject a callable with a call signature at `C`
directly (`{ (): number; a: number }`: "Unexpected call signature").

### Confirmed: an inferred literal type through a generic declaration is closed (`tests/expect-error/obj-literal-indexes.ts#testEscapedInferredLiteralStaysClosed`)

SKJS reads the result
of `idObj({ x: 1 })`, with `declare function idObj<T>(x: T): T`, as the closed
literal `{ x: 1 }` and accepts it at `{ [k: string]: number }`. The
declaration promises only a `T`, `{ x: number }`, which may carry further
keys; the pipeline refuses the assignment in search. The test's own comment
marks it `TODO(#678): main accepts this`. Witness: SKJS reports no error for

```ts
declare function idObj<T>(x: T): T;
export function escaped(): string {
  const r = idObj({ x: 1 });
  const v: { [k: string]: number } = r;
  const n = v["y"];
  return n === undefined ? "none" : n.toFixed(1);   // TypeError: n.toFixed is not a function
}
```

and `node` throws at the marked line when `idObj` is this implementation,
which `tsc --strict` accepts at the declaration:

```ts
export function idObj<T>(x: T): T {
  return x !== null && typeof x === "object" ? Object.assign(x, { y: "s" }) : x;
}
```

### Confirmed: a body falling off its end at a binder bounded by `void` (`tests/expect-error/void.ts#returningConstrainedVoid`)

SKJS accepts
`function returningConstrainedVoid<T extends void>(): T {}`, whose body
returns `undefined` at every `T`; TypeScript refuses it (TS2355: a function
whose declared type is neither `undefined`, `void` nor `any` must return a
value). `never` is below `void`, so a caller may instantiate `T := never`.
The pipeline refuses the body (`generic return contract: cannot establish
undefined ≤ T under [T ≤ unknown]`). Witness: SKJS reports no error for

```ts
function returningConstrainedVoid<T extends void>(): T {}

export function witness(): string {
  const n: never = returningConstrainedVoid<never>();
  const s: string = n;
  return s.toUpperCase();   // TypeError: Cannot read properties of undefined
}
```

and `node` throws at the marked line.

### Confirmed: `await` passes a record through (`tests/expect-error/promise-object.ts#testAwaitPlainObject`)

SKJS, like TypeScript, types `await o` at `o`'s own type when `o` is a record
that names no `then` (a lint warning only), and `testAwaitAliasContract`
states that awaiting a plain object preserves its identity. Record types are
open, so the record may own a `then`, and `await` then calls it and yields
what it passes. The pipeline awaits only a promise or a primitive
([DESIGN.md](../DESIGN.md#async-and-iteration)) and refuses the unit.
Witness: SKJS reports no error for

```ts
async function testAwaitPlainObject(o: { a: number }): Promise<number> {
  const r = await o;
  return r.a;
}
export async function witness(): Promise<string> {
  const o = {
    a: 1,
    then(resolve: (v: string) => void): void {
      resolve("s");
    },
  };
  const n = await testAwaitPlainObject(o);
  return n.toFixed(1);   // TypeError: Cannot read properties of undefined
}
const s: string = await witness();
```

and `node` throws at the marked line: `r` is `"s"`, and `r.a` is `undefined`.

### Undetermined

None of the other search refusals looked like SKJS errors on reading their
source and obligation; the candidates checked and found sound are
`array_literal_examples.ts#arrayCommittedTypeTest` (SKJS rejects the aliasing
variant), `tparam_shadow.ts` (read-only fields, so covariance is sound),
`function-intersection.ts`/`function-subtyping.ts` (fewer parameters),
`unsound-refinement.ts` snapshots, `void.ts#unsafeInTypescript`. Units refused
*before* Lean (source/proposal) were not examined for unsoundness; widening
the fragment will expose more divergences, so a rerun's new `search`
refusals are read.
