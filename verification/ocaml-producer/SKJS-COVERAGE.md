# SKJS coverage by the OCaml pipeline

How much of what SKJS accepts in its own test suite the pipeline
(`check.mts`: parser → OCaml producer → Lean search and check) verifies, what
stops the rest, and where the two disagree because SKJS is wrong.

**2,291 of 2,674 SKJS-accepted units verify (85.7%); 1,689 of 2,026 accepted
functions (83.4%).** 254 of the 377 files with an accepted unit verify entirely.
Five families of SKJS-accepted functions that the pipeline reaches and refuses
are real SKJS unsoundnesses, each with a runtime witness that SKJS accepts and
node crashes on ([below](#suspected-skjs-unsoundnesses)).

Rerun:

```sh
node verification/ocaml-producer/skjs-coverage.mts --skjs   # ~140 s on 12 cores
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
| `tests/expect-error` | `@ts-expect-error` / `@skjs-expect-error` name the next non-annotation line (`tests/Helpers.sk` `findExpectErrors`); `@skjs-expect-warning` is not an error | 399 (374 with units) | 3,885 | 2,458 | 2,081 | 1,863 | 1,531 |
| `tests/callgraph` | no error allowed | 25 | 59 | 59 | 56 | 51 | 48 |
| `tests/constprop` | no error allowed | 14 | 66 | 66 | 64 | 49 | 48 |
| `tests/deadcode` | no error allowed | 7 | 27 | 27 | 27 | 16 | 16 |
| `tests/cfg` | no error allowed | 7 | 22 | 22 | 21 | 21 | 20 |
| `tests/projects` | expect-error markers, under the project's tsconfig | 24 of 68 | 44 | 34 | 34 | 23 | 23 |
| `tests/ts-conformance/cases` | lines listed in `reference/*.errors.txt` | 4 | 11 | 10 | 8 | 3 | 3 |
| **total** | | **480** | **4,110** | **2,674** | **2,291** | **2,026** | **1,689** |

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
| verified | 2,291 |
| source (gate) | 130 |
| proposal (producer) | 62 |
| search (Lean) | 191 |

**Caveats on the method.**

- Counts are *first* blockers. A group's count is an upper bound on what
  widening it alone unlocks; the next blocker is not measured.
- Name-based closure over-approximates (a local shadowing a top-level name
  drags that declaration in) and drops unreferenced top-level statements. SKJS
  confirmation guards acceptance, not the pipeline's view.
- A derived file of a module is written as a script (`export {}` is itself
  outside the fragment). Three "Duplicate identifier" TypeScript diagnostics
  (DOM `Event`, `Response`) are artifacts of that, in the "names the reader
  cannot resolve" group.
- A derived file is written beside the others, not beside its source, so a
  relative import of a sibling test file (`symbols.ts` importing
  `./symbols-export.js`) does not resolve: 1 unit.
- `where` is `unknown` for 33 producer refusals, which name no location.

## Groups, by value

Units whose first blocker is in the group, from `summary.byGroup` of
[skjs-coverage.json](skjs-coverage.json) (`self`: in the unit's own
statement; `dep`: in a dependency; a unit whose blocker names no location is
in neither). Cost: S (one layer, local rule), M (two layers or a new rule
family), L (new calculus concept or several layers). Layers: P = parser gate
/ Fragment (`verification/tools/fragment-parse.mts`, `fragment.mts`), D =
declaration reader (`tools/declaration-graph.mts`, `declaration-types.mts`,
Lean `Source/DeclarationGraph.lean`), O = OCaml producer (`proposal.ml`,
`environment.ml`, `inference.ml`, `source.ml`), L = Lean lowering, rules or
search (`Source/SourceExtraction.lean`, `Source/Fragment.lean`,
`Semantics/Calculus.lean`, `Programs/ProgramTyping.lean`,
`Programs/CertificateProducer.lean`, `Types/*`). A group marked "refused" is
refused on principle ([fragment boundary](../DESIGN.md#fragment-boundary)),
each unit naming its reason; widening it is design work, not a rule to add.

| # | Group | Units | self | dep | Files | Cost | Layers |
| ---: | --- | ---: | ---: | ---: | ---: | --- | --- |
| 1 | `Array<T>` / `ReadonlyArray<T>`, `Record`, `Function` from the library — done | 0 | | | | | |
| 2 | Relational operators `< <= > >=`, `**` — done | 0 | | | | | |
| 3 | Producer claim differs from annotation — done | 0 | | | | | |
| 4 | Ambient declarations (`declare function/const/class`) — done | 0 | | | | | |
| 5 | Control-flow forms (`else if`, unbraced arms, bare `return`, falling off the end, dead code) — done | 0 | | | | | |
| 6 | `switch`, with case narrowing — done | 0 | | | | | |
| 7 | Unary `-`/`+`/`~` — done | 0 | | | | | |
| 8 | `void e` and the comma operator — done | 0 | | | | | |
| 9 | Template literals and string `+` — done | 0 | | | | | |
| 10 | Mutable bindings — done but a closure assigning its parameter | 1 | 1 | 0 | 1 | S | O |
| 11 | Compound and update assignment — done but an assignment pattern's target | 1 | 1 | 0 | 1 | S | P |
| 12 | Destructuring, rest and default parameters — done; left refused by reason: slices, rests typed by a type parameter or an intersection, `...x: number`, an assigned `let` pattern, a pattern over a non-array iterable | 22 | 17 | 5 | 11 | M | P O L |
| 13 | Library globals — the reviewed overlay done; left: `new Date` with two arguments, `Symbol` both called and read through members | 2 | 2 | 0 | 2 | M | D L |
| 14 | Reads on primitives and unions — done; left: a field or index read on what the producer holds as no object, a numeric key not proved an array index | 16 | 7 | 0 | 9 | M | O L |
| 15 | Equality — done; left refused: two operands that may both be objects without a field | 6 | 6 | 0 | 2 | M | L |
| 16 | Discriminated-union narrowing — done; left: `length` after `Array.isArray` keeping a record (refused), `m.keys()` of a `Map` | 3 | 3 | 0 | 2 | M | O L |
| 17 | `in` / `instanceof` / `typeof` — done for the tests JavaScript defines exactly; left refused: static `[Symbol.hasInstance]`, `instanceof` of what is not a class of the file or narrowing `unknown`, numeric and `string` `in` keys | 31 | 22 | 2 | 10 | L | P O L |
| 18 | Search: no derivation found | 139 | 131 | 8 | 59 | L | L O |
| 19 | Classes — done; left refused: `this` parameters on methods, extending a library class, generic methods, constructor defaults, computed keys, a base not declared earlier in the file, generic inheritance, an index signature | 25 | 13 | 12 | 12 | L | P O L |
| 20 | Generic classes — done | 0 | | | | | |
| 21 | Generics — done for records, tuples, arrays and field reads and writes over a binder; left: a binder typing both a value and an argument list, dependent bounds, generic function and constructor types as annotations | 10 | 7 | 2 | 7 | L | P O L |
| 22 | Type forms — done; left: intersections with no representable meet, forms over a type parameter, `keyof` with a unique symbol part, `typeof` of an unannotated binding | 48 | 36 | 11 | 24 | L | P D L |
| 23 | Loops — done but a `for...of` binding other than one `const` | 1 | 1 | 0 | 1 | S | P |
| 24 | Exceptions — done; left refused: a jump through a `finally` | 1 | 1 | 0 | 1 | M | P L |
| 25 | Calls — `.call`/`.apply`/`.bind`, `this` parameters, spreads done; left: array literal spreads, `.call` other than on a local function, spreads into `new` or of no fixed length, `Object.assign` forms | 11 | 7 | 2 | 8 | M | P O |
| 26 | `await` of a thenable at a closure's bound | 4 | 4 | 0 | 3 | M | L |
| 27 | Object literals — done; left refused: string, array, function and class-value spread operands, computed keys | 8 | 7 | 0 | 6 | L | P O L |
| 28 | Library `Function` methods, `Record` — done | 0 | | | | | |
| 29 | Optional chaining — done | 0 | | | | | |
| 30 | Sloppy code — done without a `this` read; left refused: reading `this` | 6 | 4 | 2 | 3 | S | P |
| 31 | Other forms — `<T>e`, top-level `;`, shadowing done; left: generic closure bodies the rigid checker does not read, a contextual `any` parameter (refused) | 3 | 3 | 0 | 2 | S | P L |
| 32 | bigint — done but a non-decimal numeric literal type | 1 | 1 | 0 | 1 | S | P |
| 33 | Enums — done; left refused: computed members, an ambient and an empty enum | 7 | 0 | 7 | 1 | | |
| 34 | Module initialization and SKJS's test environment — done | 0 | | | | | |
| 35 | Object growth: a write adding a key (refused) | 21 | 20 | 0 | 8 | L | L |
| 36 | TypeScript errors in declarations, names the reader cannot resolve | 6 | 0 | 6 | 2 | | D |
| 37 | Single refusals, one unit each | 10 | 8 | 0 | 9 | | O L |

### Group details

Each entry: what the group now verifies, what is left with its reason, and
examples (`file#unit`, under `tests/expect-error` unless another suite is
named).

1. **Library types.** `Array<T>`/`ReadonlyArray<T>` are `T[]`/`readonly T[]`,
   `Record<K, V>` the library's mapped type at its arguments, `Function`
   callable-or-class ([library types](../PROGRAM-TYPING.md#library-types)).
2. **Relational operators.** Operands compared in their primitive order;
   `**` is number arithmetic. A comparison that converts its operands is
   refused ([fragment boundary](../DESIGN.md#fragment-boundary)).
3. **Claim differs from annotation.** The literal type `0` denotes both
   zeros; a record intersection with readonly fields is lowered by the
   declaration meet, as views
   ([record-meet](../PROGRAM-TYPING.md#library-types)).
4. **Ambient declarations.** `declare function`, `declare const` and
   `declare class` join the module's values like an import (specifier
   `ambient`); overloads are the conjunction of their signatures;
   `declare let`/`var` is refused as module storage
   ([ambient](../PROGRAM-TYPING.md#imported-ambient-and-global-values)).
5. **Control-flow forms.** An unbraced arm is its block, `else if` a nested
   `if`, `return;` is `return undefined`, a block closure falling off its end
   returns `undefined`, and statements after one that always jumps are dropped
   unless a name they declare is hoisted or read live
   ([statement forms](../PROGRAM-TYPING.md#statement-forms)).
6. **`switch`.** Labeled blocks, one per clause, with a dispatch of `===`
   tests: fall-through is exact, `break` leaves the switch, and each case
   narrows the scrutinee (a field discriminant is re-read at each case).
7. **Unary operators.** `-`, `+` and `~` through the one operator rule; a
   negated bigint literal is its integer.
8. **`void e`.** The comma form `e, undefined`, also the comma operator
   ([values](../DESIGN.md#values)).
9. **Template literals and string `+`.** `+` with a string operand
   concatenates any primitive but a symbol, converted by `ToString` exactly;
   a template is the parser's left-nested concatenation of its parts. Finite
   template literal types evaluate; a `${string}` hole is refused
   ([computed types](../PROGRAM-TYPING.md#computed-types)).
10. **Mutable bindings.** A `let` or an assigned parameter is a cell with a
    storage contract (its annotation, or TypeScript's widened or evolved
    type); module constants read by functions verify ([mutable bindings](../PROGRAM-TYPING.md#mutable-bindings-and-module-constants)).
    Left (1): a closure assigning its own parameter
    (`captured-local-write.ts#paramReassignNarrowsInLambda`, producer:
    "assignment to immutable binding").
11. **Compound and update assignments.** `x++`, `+=`, `||=`, `??=` and array
    destructuring assignment verify. Left (1): an assignment pattern whose
    target is neither a field nor a local
    (`destructuring-assignment.ts#keyBeforeDefault`), one of the
    [remaining source forms](../DESIGN.md#next-steps).
12. **Destructuring and parameters.** One recursive pattern for object and
    array patterns, nesting, holes, a tuple's rest and defaults, in
    statements, closure bodies and parameters; rest parameters over arrays,
    tuples of required positions and aliases of either, generic aliases read
    through their equations ([patterns](../PROGRAM-TYPING.md#patterns)).
    Left (22), each refused by its reason: a rest parameter typed by an
    intersection (6, `arraysAreInvariant.ts#interWithTop`), by a function's
    type parameter (6, `generic-spread-params.ts#bareSpread`) or by a
    declaration's own type parameter (2,
    `rest-inference-stability.ts#RestRunner`); an array rest of unknown
    length, a slice (5: `array-destructuring-rest.ts#restFromArray`,
    `destructuring-tuple-rest-union.ts#declaredRest`, `#emptyRemainder`,
    `#assignedRest`, `destructuring-assignment.ts#restTargetOfArrayAccepted`);
    `...x: number` (1, `function-args.ts#restNotArray`); an assigned `let`
    pattern (1, `captured-read-stability.ts#checkedDestructuredDefault`); an
    array pattern over a value that may not be an array (1,
    `callgraph/destructuring-iterator.ts#test`). Slices are a
    [next step](../DESIGN.md#next-steps).
13. **Library globals.** A standard library global is read only through the
    reviewed overlay ([library globals](../PROGRAM-TYPING.md#library-globals)):
    `BigInt`, `Symbol`, `String`, `console.log`, `Array.isArray` and
    `instanceof Array`, `new Error`/`Array`/`Set`/`Map`/`Date`/`Promise`, the
    `Promise`, `JSON` and `Object` statics, and `Set`/`Map`/`Date` members
    through `interfaceOverlay`. Left (2): `new Date("2020-01", 1)`, which
    TypeScript rejects (`date-constructor-string.ts#testWrongStringMonthCombination`),
    and `Symbol` both called and read through members, a callable object with
    methods (`symbols.ts#symbolAtRuntime`, refused). Loops over a `Set` or
    `Map` count in 18; `instanceof Array` narrowing `unknown` in 17.
14. **Reads on primitives and unions.** Truthiness is a tag test
    (`ToBoolean`); a string's `length` and code units are calculus reads
    (`s[i]` is `string | undefined`); every other member of a primitive is
    read through its realm prototype's contract
    ([prototype contracts](../PROGRAM-TYPING.md#prototype-contracts)). Left
    (16): a field read on a value the producer holds as no object (8, e.g.
    `destructuring.ts#checkedNestedPattern`,
    `recursive-type-absorption.ts#nestedExpansionDeep`, and
    `promise-object.ts#testAwaitPlainObject`, an
    [SKJS unsoundness](#confirmed-await-passes-a-record-through-testsexpect-errorpromise-objecttstestawaitplainobject));
    a numeric key on a value not proved an array with that index (7,
    `algebraic-data-types-comprehensive.ts#countDataValues`); an indexed read
    on a non-object (1, `instanceof-generic-skolem-args.ts#arrayRead`).
15. **Equality.** A singleton operand of every primitive kind selects a tag
    test that narrows the other operand on both edges; any other `===` is the
    strict-equality operator, exact where one operand is a primitive or an
    object with a field; `x == null` is the nullish test and other `==` is
    refused ([guards](../PROGRAM-TYPING.md#guards)). Left (6, refused): two
    operands that may both be objects without a field (`equality.ts#weakObjects`,
    `#funDisjoint`, `void.ts#x7`): such values have no identity in the model.
16. **Discriminated-union narrowing.** A test of a field of an immutable
    binding's object against a singleton keeps the arms whose field admits
    the outcome; a `let` nothing assigns is a `const`. Left (3): `length` read
    after `Array.isArray` on a union with a record, which the test keeps
    (2, `array-isarray-refinement.ts#testArrayMethodsAfterRefinement`,
    `#testEarlyReturnWithLength`, refused: an open record may be an array),
    and `m.keys()` of a `Map` in a `for...of` (1,
    `symbols.ts#testForOfMapIterator`: `MapIterator` is not read).
17. **`in`/`instanceof`/`typeof`.** `typeof` as a value and in guards
    (`typeofObject` for `"object"`), `key in o` as `hasKey` along the
    prototype chain the model holds, and `x instanceof C` for a class the file
    declares ([guards](../DESIGN.md#guards)). Left (31), each refused by its
    reason: a static `[Symbol.hasInstance]`, which makes `instanceof` a call
    (12: 8 declaring one, e.g. `instanceof-hasinstance.ts#WithHasInstance`, 4
    testing such a class, `implicit-instanceof-effects.ts`); `instanceof` of a
    right operand that is not a class of the file (7,
    `instanceof-rhs.ts#instanceofFunction`); `instanceof` narrowing
    `unknown`, a world invariant over every allocation (7,
    `instanceof-generic-skolem-args.ts#observe`; the array-coherence invariant
    of the [next steps](../DESIGN.md#next-steps)); `in` with a numeric key,
    an array element (3, `in.ts#literalInTupleAlwaysTrue`); `in` with a key
    that is not a union of string literals (2, `in.ts#stringInRecord`).
18. **Search found no derivation.** 139 units in 59 files. The message names
    the failed obligation and why (`… evidence search failed: no derivation
    of its return-contract claim`), and `check.mts` adds the reader's summary
    as an `obligation:` line, which the rows carry
    ([OBLIGATION-DIAGNOSTICS.md](../OBLIGATION-DIAGNOSTICS.md)). By the failed
    obligation: return contract 46, binding annotation 39, node typing 38,
    cast 8, a closure expression's claim 5, a `for...of` iterator 3.

    Causes, read obligation by obligation. Kind: (a) the producer does not
    propose the claim, (b) Lean's rules or search do not derive it, (c) a
    sound refusal, the model or TypeScript answering otherwise than SKJS,
    (d) an SKJS unsoundness.

    | Cause | Examples | Kind | Reason |
    | --- | --- | --- | --- |
    | Index signatures: `v[k]!` of a `for...in` key, writes and numeric keys on a string index, `Closed<T>` (read as `T`, an open record) into a dictionary or `Json` | `forin-exclamation.ts` (8), `index-signatures.ts#bracketAssignOnStringIndex`, `local-objects.ts#testWithIndexSignature`, `closed-type.ts` (5), `json-named-object-type.ts` (2) | (b)/(c) | a `for...in` key is a `string`, not a key of the object; `Closed<T>` is read as less than SKJS's meaning ([lasting decisions](../DESIGN.md#lasting-decisions)) |
    | Cells written in a `try` or before a call, read after it | `catch-entry-writes.ts` (2), `jump-through-finally.ts#jumpBeforeTheTryIsUntouched` | (b) | a call forgets every cell: no reachability is stated, so no capture analysis can be justified ([current-content assertions](../DESIGN.md#current-content-assertions)) |
    | Object identity: `x.child !== narrow`, then a read at `narrow`'s type; a computed key assigning its own receiver | `unsound-refinement.ts#stableMemberScalar`, `#capturedReceiver`, `destructuring.ts#identityPatternScalar` | (c) | a statement entry states no slot equality, nor what a field of a mutable local's object holds; TypeScript refuses these returns too |
    | `obj.val === undefined` on an optional key, then `obj.val` at `undefined` | `field-refinement.ts#testOptionalFieldEqualsUndefined` | (b) | knowledge of an absent key needs a record clause whose bound excludes it |
    | `for...of` and spreads over a non-array iterable: a string, `Set`, `Map`, an iterator | `symbols.ts` (4), `for_in_for_of_tests.ts` (2), `for-in-for-of-invalid.ts#testForOfWithPrimitive`, `iterator-effects.ts`, `callgraph/for-of-iterator.ts` | (c) | `%Iterate%` is stated for arrays only ([loops over arrays](../PROGRAM-TYPING.md#loops-over-arrays)); the host collections' iterators could be stated, a client's cannot |
    | Generic call inference: nested instantiation, a spread into a generic | `per-field-tvar-isolation.ts`, `tvar-widening-ordinary-check.ts` (2) | (a) | producer inference |
    | SKJS unsound: aliased views of an empty literal, an inferred literal type that stays closed, `typeof c === "function"` on a class instance | `obj-literal-indexes.ts` (8), `callability.ts#testInstanceTypeofFunction` | (d) | [below](#suspected-skjs-unsoundnesses) |
    | Sound aliased views without fields | `obj-literal-indexes.ts#testAliasMutableOptionalThenOptional`, `#testAliasTwoReadonlyOptionals` | (b) | the same search as the unsound family's |
    | Guards: `Array.isArray` narrowing a union with a record, `typeof x === "function"` on `unknown` or a binder | `array-isarray-refinement.ts` (6), `array-object-union-operations.ts#testNarrowToArray`, `function-type.ts` (2) | (b) | needs the array-coherence heap invariant ([next steps](../DESIGN.md#next-steps)) |
    | `Promise<A>` below `Promise<B>`: `then` and `catch` are generic methods | `promise-object.ts#testThen`, `#testCatch`, `#testCovariantWiden` | (b) | relating two schemes needs a subtyping rule for quantified signatures ([next steps](../DESIGN.md#next-steps)) |
    | A module function where a longer signature, or an intersection with one, is expected | `function-intersection.ts` (4), `function-subtyping.ts#testMissingRestFails` | (c) | its slot is its annotated signature, checked by its own unit; offering more would make that slot a claim |
    | Classes: inheritance across a shadowed binder, field annotations and a `#private` field in a class body, a method reattached through a `this` parameter | `tparam_shadow.ts` (2), `field-type-annotations.ts#FieldsWithAnnotations`, `private-fields.ts#HasPrivateForInTest`, `this-parameter-implicit-class.ts#compatibleReattachment` | (b) | search |
    | SKJS's own literal typing, where TypeScript differs and the pipeline follows TypeScript: `[1, "a"]` as a tuple, an evolving `[]` | `array_literal_examples.ts` | (c) | TypeScript types these as `(number \| string)[]` and `any[]` |
    | An array's `length` as a record field; an 11-tuple's `length` as the literal 11 | `literal-representation-lifetime.ts`, `tuple-large-arity.ts#arity11Length` | (c) | an array keeps its length in its store, not at a field; a mutable tuple's length is not fixed by its type |
    | Computed types that follow TypeScript: `keyof typeof E` excluding reverse keys, `keyof (A \| B)` | `enums.ts#keyOfIncludesReverseKeys`, `type-operator-precedence.ts#testNestedKeyofBuggy` | (c) | TypeScript's computed type |
    | `<` with an operand that may be `undefined` | `array_literal_examples.ts#supertypePositionTest` | (c) | only operands compared in their primitive order |
    | A tuple as `Iterable<T>` | `tuple-iterable.ts` (3) | (b) | the search relates a tuple's store to the prototype's iterator element only for arrays ([next steps](../DESIGN.md#next-steps)) |

    Not yet read obligation by obligation: among others `unit.ts` (5),
    `obj-literal-indexes.ts#testProvidedOptionalNeverIndex`,
    `generic-inference-too-narrow.ts` (4), `nullish-coalescing.ts` (3),
    `spread-union-distribute.ts` (3), `instanceof-generic-skolem-args.ts`
    (3).

19. **Classes.** Member modifiers, optional and definitely assigned fields,
    parameter properties, constructor statements, receivers, a base declared
    earlier in the file (`super(...)`, `super.m(...)`, overrides checked, the
    derived prototype linked to the base's, an implicit constructor
    forwarding the base's parameters) and interface inheritance through
    aliases ([classes](../PROGRAM-TYPING.md#classes)). Left (25), each refused
    by its reason: a method with a `this` parameter (8,
    `this-parameter-detached.ts#H`; a method member is
    [host-relative](../DESIGN.md#method-members-are-host-relative)); extending
    a library constructor (4, `class-extends-generic-constructor.ts#StringArray`);
    a generic class method (3, `clauses-diff-subset.ts#Helper`); a member with
    a computed key (3, `private-fields.ts#WithPrivateSymbolMethod`); a
    constructor parameter with a default (3, `repro311.ts#MyClass`); a base
    from a library, an ambient declaration or a value (2,
    `class-extends-interface.ts#ClassExtendsMerged`); a class extending a
    generic class (1, `instanceof-generic-skolem-args.ts#SubBox`); an index
    signature in a class (1, `spread-callable.ts#indexedOwnCopy`).
20. **Generic classes.** A generic class's binders belong to the
    initialization unit that declares it, so its constructor and methods are
    certified at every instantiation
    ([generic bodies](../DESIGN.md#generic-bodies)). Generic methods and
    generic inheritance are refused (19).
21. **Generics.** A generic body is a graph request over parameter rows,
    certified at every assignment: records, tuples, arrays, field reads and
    writes, literals, `??`, `if`, `let` and `typeof` over a binder verify with
    no rule of their own ([generic bodies](../DESIGN.md#generic-bodies);
    `examples/generic-graph-bodies.ts`). Bounds of any ground type, explicit
    type arguments, `as const`, tuple bounds as contextual types and `T & D`
    at ground instances verify too. Left (10): a type parameter typing both a
    value and a rest parameter's argument list (3,
    `variadic-rest-corner-cases.ts#testEmptyRestInference`); a bound naming
    another binder, `U extends T`, which the graph reads as its own row (2,
    `hidden-dependent-bounds.ts#DependentBox`); generic function and
    constructor types as annotations (4,
    `object-literal-function-field-widening.ts#genericArrowField`); a type
    argument `object` not establishing its declared bound (1,
    `json-generated-service.ts#GraphResource`). Generic methods with their
    own binders are a [next step](../DESIGN.md#next-steps).
22. **Type forms.** A computed type (`typeof x`, `keyof T`, `T[K]`, template
    literal types, intersections of primitives, mapped keys) is the type
    TypeScript's checker computes, evaluated by the declaration reader
    ([computed types](../PROGRAM-TYPING.md#computed-types)); `object`, `{}`,
    method and construct signatures in type literals, numeric property names,
    `unique symbol` constants, annotation intersections as Lean's meet, and
    string, number and symbol index signatures
    ([index signatures](../PROGRAM-TYPING.md#index-signatures)) verify. Left
    (48), each refused by its reason: an intersection with no representable
    clause (9, `callability.ts#testArrayCallableIntersection`); an
    intersection with a type parameter, known only at an instance (8 at the
    gate, `generic-tvar-intersect-literal.ts#tag`, and 4 in a producer
    claim, `intersection-collapsing.ts#testTypeParam`); other forms over a
    type parameter: an indexed access (7,
    `observed-indexed-normalization.ts`), `keyof T` (1), a method of a type
    literal over one (2), a declaration with call or index signatures applied
    to one (1), a spread of one or of an intersection (2); `keyof` with a
    unique symbol part (6, `keyof.ts#koTup0`); `typeof` of a binding without
    an annotation (3), of a class with statics (1), and one that is not valid
    TypeScript (1); a call of an intersection of a function type and a
    record (1); an object type with construct signatures and other members
    (1); optional named fields beside a string index (1,
    `obj-literal-indexes.ts#testEmptyVsReadonlyOptionalNumberIndex`).
23. **Loops.** `for(;;)` is a `while` whose body's end and `continue` run the
    update; `for...in` iterates the trusted `%ForIn%`; `for...of` over an
    array steps `%Iterate%` ([loops over arrays](../PROGRAM-TYPING.md#loops-over-arrays)).
    Left (1): a `for...of` declaring other than one `const` binding
    (`for_in_for_of_tests.ts#testForLoopsWithDifferentDeclarations`).
24. **Exceptions.** A throw is an outcome of the calculus
    ([throws](../DESIGN.md#throws)); `throw`, `try`/`catch`/`finally` and
    `throw new Error(…)` are lowered. Left (1, refused): a `break` through a
    `finally` (`cfg/finally.ts#breakThroughFinally`), whose lowering runs the
    `finally` for returns and throws only.
25. **Calls.** `.call`, `.apply` and `.bind` on the file's functions, a
    leading `this: T` parameter as the receiver, and spreads among the
    actuals verify ([calls](../DESIGN.md#calls)). Left (11): array literal
    spreads outside the fragment (4, `generic-spread-params.ts#pushAll`);
    `.call` other than on a known local function with an explicit receiver
    (3, `this-parameter-bind-call-apply.ts#implicitRebindCompatibleOk`); a
    spread argument of no fixed length (1,
    `spread-in-function-calls.ts#testSpreadUndefined`) or into `new` (1,
    `#testSpreadInConstructor`); a method read off its object as a function
    value (1, `this-parameter-implicit-class.ts#compatibleDestructuring`,
    refused); `Object.assign` other than of a fresh arrow and an object
    literal (1, `typeof.ts#testCallableObject`).
26. **`await`.** `await` is a trusted step and an async result is a primitive
    ([async and iteration](../DESIGN.md#async-and-iteration)). Left (4): a
    thenable awaited where the closure's bound admits no thenable
    (`promise-object.ts#testAwaitThenable`, `#testAwaitThenableNested`,
    `nested_async_test.ts#createCounterService`).
27. **Object literals.** Numeric keys, spreads of literals and of values
    (an allocation from parts), object rests and construct-signature type
    literals verify ([object literals](../DESIGN.md#object-literals)). Left
    (8), each refused by its reason: a spread of a function (2), a class
    value (2), an array (1) or a string (1), whose own enumerable properties no
    record states (`spread-callable.ts`, `objects.ts#spreadFieldsAfterSpread`);
    a computed key (2, `symbols.ts#testSymObj`).
28. **Library `Function` methods, `Record`.** Read as in 1.
29. **Optional chaining.** One derived form, a conditional with the arms
    exchanged ([derived source forms](../PROGRAM-TYPING.md#derived-source-forms)).
30. **Sloppy code.** A sloppy function that reads no `this` is the strict
    one. Left (6, refused): a sloppy function reading `this`
    (`function-union.ts#f1`), sloppy receiver conversion not being modelled.
31. **Other forms.** `<T>e`, a top-level `;` and shadowing (the parser renames
    a hiding local by the declaration TypeScript binds each reference to)
    verify. Left (3): a generic closure body outside the rigid checker's
    forms (2, `parameter-binding-patterns.ts#testArrowGeneric`; generic
    closures still keep term code, [closures](../DESIGN.md#closures-are-graph-code)),
    and a contextual closure parameter TypeScript types `any` (1, refused,
    `instanceof-generic-skolem-args.ts#unionRoundTrip`).
32. **bigint.** Literals, `BigInt`, bigint literal types and arithmetic
    through the one operator rule, division and exponent throwing where
    JavaScript does. Left (1): a non-decimal numeric literal type
    (`number-literal-precision.ts#beyondRangePair`).
33. **Enums.** An enum is the module constant bound to the object
    TypeScript's emit makes, members and reverse mappings as readonly fields;
    `E`, `E.A` and `typeof E` as types; a `const enum`'s reads are its values
    ([enums](../PROGRAM-TYPING.md#enums)). Left (7, all dependencies in
    `enums-computed.ts`, refused): a computed member (5), an empty enum (1),
    an ambient enum (1).
34. **Module initialization and the SKJS environment.** A module whose only
    code is its initialization is checked through its initialization unit
    ([modules and code units](../DESIGN.md#modules-and-code-units)); each
    derived file runs in SKJS's test environment (Method, "Environment").
35. **Object growth.** Left (21, refused): a write adding a key to an object
    allocated without it (14, `local-objects.ts#testBasicGrowth`), a dynamic
    index write (5, `index-signatures.ts#writePlainIndexOk`), a write to a
    writable optional field (2,
    `object-type-readonly-fields.ts#assignNumberToOptional`). An object's keys
    are fixed at allocation; a key-adding write is a
    [next step](../DESIGN.md#next-steps).
36. **TypeScript errors and unresolved names.** Left (6, dependencies): a
    declaration TypeScript reports an error in, a property not assignable to
    the index type, which SKJS accepts (5, `index-signatures.ts`), and the
    relative import that does not resolve beside the derived files (1,
    `symbols.ts#importedSym`; see the caveats).
37. **Single refusals.** One unit each: a generic spread of a readonly array
    (`observed-array-rest.ts#observedRigidArrayElement`); a read of a field
    the contract does not name (`parameter-binding-patterns.ts#testArrowRest`,
    `simple-continue-validation.ts#validateContinue`); a quantified closure
    with no checked instantiation
    (`parameter-binding-patterns.ts#testArrowGenericConstraint`); a compound
    assignment inside a closed expression
    (`postfix-with-binary-ops.ts#testPostfixPlusBinary`); a quantified
    callable claim (`promise-object.ts#testAwaitNested`); a call writing more
    positions than its callee's parameters, which TypeScript rejects
    (`spread-in-function-calls.ts#testTooManyArguments`); a receiver the
    producer and TypeScript disagree on
    (`switch-clause-termination.ts#terminalLastClauseLeavesNoPath`); `as const`
    on an operand other than a literal or a name
    (`unsound-refinement.ts#checkedArrayAlias`); and the SKJS unsoundness
    `void.ts#returningConstrainedVoid`
    ([below](#confirmed-a-body-falling-off-its-end-at-a-binder-bounded-by-void-testsexpect-errorvoidtsreturningconstrainedvoid)).

## Suspected SKJS unsoundnesses

Divergences: SKJS-accepted units the pipeline parses and proposes, and Lean
then refuses (191 units in `search`). The source-form refusals Lean states
explicitly are fragment boundaries. The rest were read obligation by
obligation (group 18 above): all read so far are pipeline incompleteness
except four families below; the fifth is refused by the producer
(group 14).

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
*before* Lean (source/proposal) were not examined for unsoundness, except
where a group entry says so; widening the fragment will expose more
divergences, so each widening task should rerun this script and read new
`search` refusals.

## Proposed tasks

Each is sized for one agent. "Unlocks" is the first-blocker count, an upper
bound. Conflicts are shared files: tasks that conflict should be sequenced or
split by function.

| Task | Scope | Unlocks (units / files) | Likely files | Depends on | Conflicts with |
| --- | --- | --- | --- | --- | --- |
| A. Producer claim fix (done) | Literal type `0` as both zeros in the producer; readonly record intersections lowered as views | 17 / 6 reached, 5 / 4 verified | `semantic.ml`, `source.ml`, `Fragment.lean` | — | — |
| B. `Array<T>` and lib interfaces | `Array<T>`/`ReadonlyArray<T>` to array types; overloaded lib methods; `Function`, `Record<K,V>` | 78 / 19 | `declaration-graph.mts`, `declaration-types.mts`, `DeclarationGraph.lean` | — | C, K |
| C. Ambient declarations (done) | `declare function` (with overloads), `declare const/class` as typed module assumptions; `declare let`/`var` refused as module storage | 94 / 35 reached, 22 / 12 verified | `fragment-parse.mts`, `fragment.mts`, `declaration-graph.mts`, `Source/Fragment.lean`, `SourceExtraction.lean` | — | B, K |
| D. Numeric operators | `< <= > >=` (number, string), unary `-`/`+`/`~`, `**`, `**=` | 74 / 25 | `fragment-parse.mts`, `Fragment.lean`, `Calculus.lean`, `proposal.ml` | — | E, F (gate and expression lowering) |
| E. Small expression forms (done) | `void e` and the comma operator as one `comma` form; `+` with a string operand concatenating any primitive but a symbol by exact `ToString`; template literals as concatenations; the producer's `update`, `logicalAssign`, `nullishAssign` | 58 / 25 verified (703 -> 761 units, 672 -> 730 functions, 61 -> 72 whole files, none lost) | `fragment-parse.mts`, `annotate-source.mts`, `Fragment.lean`, `Calculus.lean`, `ProgramTyping.lean`, `SourceExtraction.lean`, `CertificateProducer.lean`, `source.ml`, `proposal.ml` | — | D, F |
| F. Statement forms (done) | `else if`/unbraced arms, nested blocks, `;`, bare `return`, block closures falling off the end, dead code after a jump, `switch` as labeled blocks (exact fall-through, no case narrowing), `for(;;)` as a `while` with an update, `for-in` over the trusted `%ForIn%`; `try`/`catch`/`finally`/`throw` moved to the calculus's throw outcome | 181 / 56 reached, 63 / 29 verified (+65 units, +60 functions, +11 files entirely; 703 → 768 on the marker corpus) | `fragment-parse.mts`, `fragment.mts`, `intrinsics.mts`, `annotate-source.mts`, `Fragment.lean`, `SourceExtraction.lean`, `SourceClaimJson.lean`, `source.ml`, `proposal.ml` | D (for `<` in loops) | D, E, H |
| G. Mutable bindings | Storage contract from a widened initializer, parameters as cells, `let x: T;` with definite assignment, module constants | 52 / 22 | `proposal.ml`, `environment.ml`, `ProgramTyping.lean` | — | I |
| H. Destructuring and parameters (done) | Object/array patterns (nested, holes, defaults, a tuple's rest) on `const`, in closure bodies and as parameters of functions and closures; function defaults; array assignment with a rest; readonly and alias rest parameters; refused with reasons: array rests of unknown length (slices), object rests, `let` patterns | 111 / 28 reached, 96 left the group; 82 units verified (911 → 993 units, 860 → 942 functions, 96 → 101 whole files, none lost, marker corpus) | `fragment-parse.mts`, `fragment.mts`, `type-term.mts`, `tsc-claims.mts`, `annotate-source.mts`, `Fragment.lean`, `SourceExtraction.lean`, `SourceClaimJson.lean`, `source.ml`, `proposal.ml`, `semantic.ml` | — | F |
| I. Literal equality and tag narrowing (done) | Singleton tags of every primitive kind; strict equality as the `arith` operator (primitives, objects with a field); two unions of singletons dispatched as their tags; discriminated unions by a field slice on the branch edge; field contents after a guard; `switch` case narrowing (break joins, field discriminants re-read, exhaustive switches unreachable at their end); `== null`; impossible edges | 1578 → 1699 units (+121, none lost), 1070 → 1176 functions, 157 → 171 whole files (marker corpus, on top of tasks H, N, Q, the overlay and throws) | `Calculus.lean`, `ProgramTyping.lean`, `BranchRefinement.lean`, `ControlFlow.lean`, `HeapExpressionRules.lean`, `CertificateProducer.lean`, `SourceExtraction.lean`, `Fragment.lean`, `fragment-parse.mts`, `proposal.ml`, `environment.ml`, `claims.ml`, `source.ml` | F for `switch` | G, J |
| J. Guards (done) | `typeof` as a value and `typeof x === "object"` (tag `typeofObject`); `key in o` as the own-key tag `hasKey` (literal keys, unions of string literals), `isArray` its store-key case; refused with reasons: keys the realm's prototypes hold, array indices, `string` keys, primitive and class operands, source keys naming the model's reserved keys (a soundness hole in `isArray` closed); `tagTestPlan` branches on an unsettled arm; decided and documented, not lowered: `instanceof` of a constructor (no class identity in the model), static `[Symbol.hasInstance]`, user-defined guards; presence narrowing left | 1,791 → 1,842 units (+51, none lost), 1,261 → 1,310 functions, 180 → 182 whole files (marker corpus) | `Calculus.lean`, `ProgramTyping.lean`, `Fragment.lean`, `SourceExtraction.lean`, `SourceClaimJson.lean`, `calculus.mts`, `fragment.mts`, `fragment-parse.mts`, `tsc-claims.mts`, `source.ml`, `proposal.ml` | I, K (`Array`) | I, M (class allocation for `instanceof`) |
| K. Library globals (done, first part) | Global values read at the call signatures a module calls (`BigInt(v)`, `Symbol()`, `String(v)`) as well as members; a standard library global only through a reviewed overlay (`library-globals.mts`) that states a parameter at what the host accepts without throwing | all 102 `BigInt` units and the `Symbol()`/`String()` calls pass the reader; 6 units / 2 files newly verified (703 → 709 units, 61 → 62 whole files); `Array.isArray`, `new X(…)`, well-known symbols, `Promise`/`JSON`/`Object` statics left | `declaration-graph.mts`, `library-globals.mts` | B, C | B, C |
| L. Primitive and union reads (done) | Truthiness as a tag test, value-level `&&`/`||`, `!`; string `length` and code units; primitive members through their wrapper prototypes' contracts (the overlay generalized); not done: method calls on primitive unions, dynamic string index writes (objects cannot grow) | 68 / 30 reached, 61 / 7 (files fully) verified | `Calculus.lean`, `ProgramTyping.lean`, `ProgramCertificates.lean`, `CertificateProducer.lean`, `SourceExtraction.lean`, `array-prototype.mts`, `declaration-graph.mts`, `fragment-parse.mts`, `proposal.ml` | B (string lib) | I |
| M. Class members | Modifiers, optional/definite fields, parameter properties, constructor statements, receivers (inheritance: M2) | 104 / 31 | `fragment-parse.mts` (classes), `proposal.ml`, class model in Lean | — | N |
| N. Generics (done, first part) | Bounds of any ground type, unions mentioning a binder, rigid bodies ending without a return or with expression statements, unannotated nested closure results, explicit type arguments on plain calls and `new`, `as const`, tuple bounds as contextual types, `T & D` at ground instances; left: records, tuples and field reads over a binder, and generic classes, which need them | 71 / 7 (files fully) verified (911 → 982 units, 860 → 930 functions, none lost) | `fragment-parse.mts`, `proposal.ml`, `DirectObligation.lean`, `RigidJudgments.lean`, `GenericSource.lean`, `SourceJudgments.lean`, `SourceClaimJson.lean`, `DeclarationGraph.lean` | M for generic classes | M |
| O. Type forms (done) | Computed types (`typeof`, `keyof`, `T[K]`, template literal types, intersections of primitives, mapped keys) evaluated by the declaration reader through TypeScript's checker; `object`, `{}`; method and construct signatures in type literals; numeric property names and number-keyed reads of non-arrays; `unique symbol` constants; annotation intersections as Lean's meet; `string \| number` and equal number indexes as the string index; refused with reasons: number and symbol index signatures, forms over a type parameter, `keyof` with unique symbol keys | 106 units / 13 files (fully) verified (1,791 → 1,897 units, 1,261 → 1,350 functions, 180 → 193 whole files, none lost, marker corpus) | `computed-types.mts`, `type-term.mts`, `declaration-graph.mts`, `fragment-parse.mts`, `DeclarationGraph.lean`, `SourceExtraction.lean`, `source.ml`, `claims.ml`, `semantic.ml` | — | N |
| O2. Index keys (done) | An index over a key class (`IndexKeys`: every string key, the canonical numeric keys "0", "1.5", "NaN" that some number's `ToString` spells, every symbol key), one mechanism for `[k: string]`, `[k: number]` and `[k: symbol]`, their unions and mapped types over them; the calculus's computed key converted by `ToPropertyKey` (a number reads the key its `ToString` spells, a symbol its own key); reads by a named key an index surely admits and by a `string`/`number`/`symbol` key; covering over as many keys, a writable target's contract within every source index and optional field over its keys; fresh literals excuse keys no number spells. Refused with reasons: writes through an index (`x[99] = v`, `x[n] = v`: the calculus adds no key), intersections of declared interfaces (no representable clause at lowering), a spread, `{ a?: number; [k: string]: never }` built with `a` (the index constrains `a` too) | 39 units / 2 files (fully) verified (1,897 → 1,936 units, 1,350 → 1,388 functions, 193 → 195 whole files, none lost; `--skjs`) | `Calculus.lean`, `Types.lean`, `PositiveNormalization.lean`, `PositiveRules.lean`, `ProgramTyping.lean`, `ProgramCertificates.lean`, `CertificateProducer.lean`, `DeclarationGraph.lean`, `SourceExtraction.lean`, `type-term.mts`, `semantic.ml`, `source.ml`, `proposal.ml`, `claims.ml` | O | — |
| P. Search narrowing and async | Flow narrowing after assignment and refinement snapshots, `Promise`/async results and `await`, contextual literals into unions, function values into intersections | ~80 / 30 | `CertificateProducer.lean`, `ProgramTyping.lean`, `proposal.ml` | I | I, J |
| Q. Module initialization and run setup (done) | A module with no function checked through its initialization unit; verdicts attributed only to units whose own code was checked; SKJS's test environment (stub imports through a per-unit `--project`, `__SKJS_show`, `process`, `StringRecord`, `Closed<T>` as `T`) | 450 / 98 verified (911 → 1,361 units, 860 → 880 functions, 96 → 136 whole files, none lost) | `SourceClaimJson.lean`, `check.mts`, `skjs-coverage.mts`, `skjs-environment/` | — | — |
| K2. Library globals, second part (done) | `JSON.parse`/`stringify`, `Promise.reject`, `new Promise`, `Set`/`Map`/`Date` contracts and constructors, `Date.now`, `instanceof Array`, generic `Object.values`/`entries` at dictionaries, throwing string members and string-pattern `split`/`replace` | 5 units / 1 file newly verified (1,420 → 1,425 units, 917 → 922 functions, 141 → 142 whole files, none lost); the corpus reaches these globals in 16 units | `library-globals.mts`, `array-prototype.mts`, `intrinsics.mts`, `declaration-graph.mts`, `fragment-parse.mts`, `source.ml`, `proposal.ml`, `DeclarationGraph.lean` | K, S | K |
| S. Throws (done) | A throw is an outcome: `throw`, `try`/`catch`/`finally` (handler edges, the `finally` compiled on each way out, returns included), `typeof` narrowing `unknown`; bigint division and exponent, `BigInt` of any number or string, and primitive radix/digit arguments read as declared | 59 units newly verified over the committed run (1,361 → 1,420, 880 → 917 functions, 136 → 141 whole files, none lost), of which about 38 in exception or bigint units and the rest from overlay work the committed run predated | `Calculus.lean`, `Safety.lean`, `ControlFlow.lean`, `ProgramTyping.lean`, `SourceExtraction.lean`, `fragment-parse.mts`, `library-globals.mts`, `array-prototype.mts`, `proposal.ml` | — | — |
| M2. Allocation from parts (done) | `Tm.merge`: object spreads of values and object rest patterns copy own enumerable string keys; class methods on a `[[proto]]` prototype object; `in` follows the prototype chain; `Error`'s `message` on a prototype; `class D extends B` (base part copied, prototype a copy of the base's with the overrides, `super.m()`, implicit constructors over a base taking nothing, overrides checked, `this` before `super` refused) | `--only` probes over the committed run at ad8564d8: spread files +11 (38 of 66), `class_inheritance_test.ts` +2, generic class files +1, none lost; on the run before tasks J and O, about 25 units by name, none lost | `Calculus.lean`, `ObjectMerge.lean`, `ProgramTyping.lean`, `ProgramCertificates.lean`, `CertificateProducer.lean`, `PositiveRules.lean`, `SourceExtraction.lean`, `Fragment.lean`, `fragment-parse.mts`, `library-globals.mts`, `source.ml`, `proposal.ml`, `claims.ml` | J (`in`) | J, M |
| M3. Prototype chains and `instanceof` (done) | A derived class's prototype linked to its base's (`MethodMembers.along`, `CoversByProto` over `ProtoHolds`); `x instanceof C` for a top-level class of the file as `hasKey` of the key only `C`'s prototype owns; the implicit derived constructor forwarding its base's parameters; refused with reasons: narrowing `unknown` to `C`, a right operand that is not a class of the file | 6 units / 1 file newly verified (2,181 → 2,187 units, 1,589 → 1,594 functions, 227 → 228 whole files, none lost; `--skjs`) | `MethodMembers.lean`, `PositiveRules.lean`, `PositiveCertificates.lean`, `ProgramTyping.lean`, `Parametricity.lean`, `Fragment.lean`, `SourceTypes.lean`, `fragment-parse.mts`, `declaration-graph.mts`, `annotate-source.mts`, `source.ml`, `proposal.ml` | M2 | J |
| R. Remaining source forms (done) | Enums (runtime, `const`, types, reverse mappings, number keys on records); object literals (numeric keys, literal spreads, construct-signature type literals; value spreads and accessors refused with reasons); optional chaining as one derived form; `.call`/`.apply`/`.bind` on module functions and `this` parameters as receivers; `%` exact on numbers and bigints | 80 / 19 verified, measured on 414fc86a before task S (1,361 → 1,441 units, 880 → 956 functions, 136 → 142 whole files, none lost) | `fragment-parse.mts`, `type-term.mts`, `declaration-graph.mts`, `annotate-source.mts`, `Fragment.lean`, `SourceExtraction.lean`, `Calculus.lean`, `ProgramTyping.lean`, `source.ml`, `proposal.ml` | D (bigint) | I (enum narrowing) |
| U. Source-gate groups (done) | One shadowing mechanism: the parser renames a hiding local by the declaration TypeScript binds each reference to (closure bodies, parameters, cells, `for...of`, `catch` included; the TDZ refused), replacing Lean's `shadow`; a `let` nothing assigns as a `const` (narrowing, `let` patterns); sloppy methods without a `this` read; rest parameters through generic alias equations; interface inheritance through an alias and from bases sharing an index; every other unit of classes, destructuring, sloppy code, enums, object literal members and other forms refused naming its reason | 10 units verified over b9196b01 (2,281 → 2,291, `--skjs --width 3`, none lost), 1,679 → 1,689 functions, 249 → 254 whole files | `fragment-parse.mts`, `type-term.mts`, `declaration-graph.mts`, `skjs-coverage.mts`, `proposal.ml`, `source.ml`, `environment.ml`, `Fragment.lean`, `GenericSource.lean`, `SourceExtraction.lean` | — | — |
| T. Closure bodies as graph code (done) | A closure's body is a graph as a function body is (`CallCode.graph`, `funGraph`): mutable locals, loops, `switch`, labeled blocks, `try`/`catch`/`finally` and `x++` inside closures; captures are the named bindings the body reads, cells by identity; an expression arrow is the graph of `return e`; node plans the extractor knows are rendered, not searched; `if (x.f !== c) return x.f;` returns the tested read in any body. Still term code, with reasons: generic closures (their certificate is universal), rest parameters (graph code is fixed-arity), parameter defaults and class constructors | 12 units verified (2,207 → 2,219 on the marker corpus, `--width 3`, none lost), two of them past a duplicate-claim failure in closure statements; `sum-*` cases 39.4 s → 37.0 s CPU, `sum-sound-binding` 7.8 s → 5.9 s | `Calculus.lean`, `Bindings.lean`, `CallArguments.lean`, `ObjectCoherence.lean`, `ProgramTyping.lean`, `ProgramCertificates.lean`, `HeapExpressionRules.lean`, `ControlFlow.lean`, `GraphCode.lean`, `CertificateProducer.lean`, `RequestJson.lean`, `SourceExtraction.lean`, `Fragment.lean`, `fragment-parse.mts`, `annotate-source.mts`, `calculus.mts`, `source.ml`, `proposal.ml` | — | N (generic closures) |

Suggested order: A, B, D in parallel (disjoint files except D's gate
entries); then C, E, G; then F, H; then I, K; then J, L, P; M, N, O last (the
largest). Q any time. After each task, rerun the script and read the diff of
`skjs-coverage.json`.
