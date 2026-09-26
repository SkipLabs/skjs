# SKJS coverage by the OCaml pipeline

How much of what SKJS accepts in its own test suite the pipeline
(`check.mts`: parser → OCaml producer → Lean search and check) verifies, what
stops the rest, and where the two disagree because SKJS is wrong.

**2,065 of 2,676 SKJS-accepted units verify (77.2%); 1,485 of 2,026 accepted
functions (73.3%).** 212 of the 377 files with an accepted unit verify entirely.
Four families of SKJS-accepted functions that the pipeline reaches and refuses
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
| `tests/expect-error` | `@ts-expect-error` / `@skjs-expect-error` name the next non-annotation line (`tests/Helpers.sk` `findExpectErrors`); `@skjs-expect-warning` is not an error | 399 (374 with units) | 3,885 | 2,458 | 1859 | 1,863 | 1330 |
| `tests/callgraph` | no error allowed | 25 | 59 | 59 | 56 | 51 | 48 |
| `tests/constprop` | no error allowed | 14 | 66 | 66 | 64 | 49 | 48 |
| `tests/deadcode` | no error allowed | 7 | 27 | 27 | 24 | 16 | 14 |
| `tests/cfg` | no error allowed | 7 | 22 | 22 | 21 | 21 | 20 |
| `tests/projects` | expect-error markers, under the project's tsconfig | 24 of 68 | 44 | 34 | 33 | 23 | 22 |
| `tests/ts-conformance/cases` | lines listed in `reference/*.errors.txt` | 4 | 11 | 10 | 8 | 3 | 3 |
| **total** | | **480** | **4,114** | **2,676** | **2,065** | **2,026** | **1,485** |

Excluded (79 files, listed in the JSON with reasons): `ts-conformance/not-supported`
(31) and `callgraph-unsupported` (4) assert only that SKJS reports errors;
project files that import each other (26), whose tsconfig disables strictness,
a strict sub-option or sets a non-default truthiness (11), or extends another
config (5); and 2 files the project's own tsconfig does not check.
`examples/src` is also SKJS-validated but outside this corpus.

**Units.** The pipeline verifies whole files and stops at the first blocker,
and SKJS test files mix accepted and rejected functions, so each file is split.
Every top-level value-level statement (function with a body, class, variable
statement, top-level code) is a unit. Its derived file holds it plus, in source
order, every top-level statement it reaches by name, transitively (aliases,
interfaces, ambient declarations, other functions, overload signatures). A
unit is marker-accepted when no statement of that closure has an error line
(1,366 units are rejected themselves, 70 through a dependency).

**SKJS confirmation.** SKJS (`check --import-stubs import-stubs`, default
truthiness, as the harness runs it) is run once over all 2,678 derived files of
marker-accepted units. It rejects 2: two `*-prettier-ignore.ts` files whose
expected *parse* errors the markers attribute to the wrong statement. They are
not counted. The remaining 2,676 are the accepted corpus.

**Environment.** SKJS checks a test in the environment its stubs give
(`--import-stubs import-stubs`); the pipeline gives each derived file the
same one, a project of its own extending
[`skjs-environment/tsconfig.json`](skjs-environment/tsconfig.json): a bare
import specifier resolves in `import-stubs`, and
[`skjs-environment.d.ts`](skjs-environment/skjs-environment.d.ts) restates the
builtins stub's globals TypeScript's library lacks (`__SKJS_show`, `process`,
`StringRecord<V>`, and `Closed<T>` read as `T`). These declarations are
assumptions of the result, as an import's are
([DESIGN.md](../DESIGN.md#modules-and-code-units), "The SKJS test
environment").

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
| verified | 2,065 |
| source (gate) | 271 |
| proposal (producer) | 60 |
| search (Lean) | 279 |

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

Units whose first blocker is in the group (`self`: in the unit's own
statement; `dep`: in a dependency). Cost: S (one layer, local rule), M (two
layers or a new rule family), L (new calculus concept or several layers).
Layers: P = parser gate / Fragment (`verification/tools/fragment-parse.mts`,
`fragment.mts`), D = declaration reader (`tools/declaration-graph.mts`,
`declaration-types.mts`, Lean `Source/DeclarationGraph.lean`), O = OCaml
producer (`proposal.ml`, `environment.ml`, `inference.ml`, `source.ml`),
L = Lean lowering, rules or search (`Source/SourceExtraction.lean`,
`Source/Fragment.lean`, `Semantics/Calculus.lean`, `Programs/ProgramTyping.lean`,
`Programs/CertificateProducer.lean`, `Types/*`).

Ordered by value for cost (units per effort, files as a tiebreak):

| # | Group | Units | self | dep | Files | Cost | Layers |
| ---: | --- | ---: | ---: | ---: | ---: | --- | --- |
| 1 | ~~`Array<T>` / `ReadonlyArray<T>` read from `lib.es5.d.ts`~~ done (task B) | 0 | | | | | |
| 2 | Relational operators `< <= > >=`, `**` | 53 | 37 | 16 | 21 | S | P L |
| 3 | Producer claim differs from annotation (literal-union parameters, cells) — done | 0 (was 17) | | | | S | O L |
| 4 | Ambient declarations (`declare function/const/class`) — done (task C) | 0 (was 94) | | | | M | P D |
| 5 | ~~Control-flow forms (`else if`, non-block branches, bare `return`, block closures that fall off the end, dead code)~~ done (task F) | 0 (was 100) | | | | | |
| 6 | ~~`switch`~~ done (task F; case narrowing task I) | 0 (was 46) | | | | | |
| 7 | Unary `-`/`+`/`~` | 39 | 21 | 18 | 7 | S | P L |
| 8 | `void e` — done (task E) | 0 (was 27) | | | | S | P L |
| 9 | Template literal expressions and string `+` — done (task E); template literal *types* done (task O): finite ones evaluate, string patterns refused | 0 (was 17) | | | | M | P L |
| 10 | Mutable bindings: unannotated `let`, `let x: T;`, parameter assignment, unannotated module constants read by functions | 52 | 42 | 0 | 22 | M | O L |
| 11 | Compound / update assignment (`x++`, `+=`, `||=`, `??=`) — done (task E); array destructuring assignment done (task H) | 5 | 5 | 0 | 4 | S | O L |
| 12 | ~~Destructuring, rest/default parameters~~ done (task H); left: slices, object rests, `let` patterns, generic alias rests | 15 (was 111) | 10 | 5 | 9 | M | P O L |
| 13 | Library globals as values — calls and the reviewed overlay done (tasks K, K2): `Array.isArray` and `instanceof Array`, `new Error`/`Array`/`Set`/`Map`/`Date`/`Promise`, `Promise`/`JSON`/`Object` statics, `Set`/`Map`/`Date` members; left: loops and spreads over a `Set` or `Map`, narrowing `unknown` to an array | 0 as first blocker (was 86) | | | | M | D L |
| 14 | ~~Reads on primitives and unions, value-level `&&`/`||`~~ done (task L); left: dynamic string index writes, numeric keys on string indexes | 4 (was 48 + 20) | | | | M | O L |
| 15 | ~~Equality against string/boolean literal singletons~~ done (task I); left: two objects without a field (no identity in the model) | 6 (was 46) | 6 | 0 | 2 | M | L |
| 16 | ~~Discriminated-union narrowing~~ done (task I); left: a `let` holding a union object | 3 (was 28) | 3 | 0 | 1 | M | O L |
| 17 | `in` / `instanceof` / `typeof` — `typeof` as a value and `"object"`, `in` with literal and literal-union keys done (task J); left: `instanceof` (no class identity in the model), `typeof` in types (task O), numeric and `string` `in` keys | 65 (was 127, marker corpus; 31 of them `typeof` in types) | 58 | 7 | 20 | L | P O L |
| 18 | Search: no derivation found — triaged (task S): 45 of 169 verify, 11 refused by name, the rest by cause below | 113 (was 169) | | | | L | L O |
| 19 | Classes: member modifiers, optional/definite fields, parameter properties, inheritance, constructor statements, receivers | 104 | 65 | 39 | 31 | L | P O L |
| 20 | Generic classes (records over a binder, below) | 47 | | | 21 | L | P O L |
| 21 | Generics: ~~constraint forms, explicit type arguments on calls, unions with rigid types, `as const`, tuple bounds, `T & D`~~ done (task N); left: records, tuples and field reads over a binder | 58 | | | 21 | L | P O L |
| 22 | Type forms: ~~literal types, `keyof`, indexed access, `typeof`, template literal types, mapped keys, `object`, `{}`, method and construct signatures, numeric field names, `unique symbol`, intersections~~ done (task O); ~~number and symbol index signatures~~ done (index keys); left: forms over a type parameter, TypeScript errors in declarations | 87 (was 187) | 45 | 41 | 27 | L | P D L |
| 23 | Loops: ~~`for(;;)`, `for-in`~~ done (task F); `for-of` with `let` | 1 (was 24) | 1 | 0 | 1 | S | P L |
| 24 | Exceptions: ~~`try`/`catch`/`finally`, `throw`~~ done (throw outcome) | 0 (was 11) | 0 | 0 | 0 | M | P L |
| 25 | Calls: ~~`.call`/`.apply`/`.bind` on module functions, `this` parameters~~ done (task R); left: overloads, union callees, spreads not last or into `new`, `.call` on a method read, `Object.assign` | 15 | 7 | 1 | 8 | M | P O |
| 26 | `await` of non-promises and unions | 12 | 12 | 0 | 2 | M | L |
| 27 | Object literals: ~~numeric keys, spreads of literals, construct-signature type literals~~ done (task R); ~~spreads of values, object rests~~ done (task M2); left: a spread into an index signature, string, function and class-value operands, computed keys, accessors | 32 | 31 | 1 | 12 | L | P O L |
| 28 | ~~Lib `Function` methods, `Record`~~ done (task B) | 0 | | | | | |
| 29 | ~~Optional chaining~~ done (task R); 1 left at search (incompleteness) | 0 (was 8) | | | | | |
| 30 | Sloppy (non-strict) code reading `this` | 8 | 6 | 2 | 5 | S | P |
| 31 | Other forms (type assertions `<T>e`, empty statement, shadowing, body forms) | 12 | 9 | 0 | 9 | S | P L |
| 32 | bigint (literals, `BigInt`, bigint literal types) | 232 | 100 | 132 | 12 | L | P L |
| 33 | ~~Enums~~ done (task R); refused: computed members, an ambient and an empty enum; left: `keyof typeof E` done (task O, but a reverse key, which TypeScript excludes), a union key, equality narrowing | 7 (was 56) | 0 | 7 | 1 | | |
| — | ~~Policy: no function to verify~~ done (task Q): a module with no function is checked through its initialization | 0 (was 453) | | | | | |
| — | ~~Environment: SKJS stub imports, `__SKJS_show`, `process`, `Closed<T>`, `StringRecord`~~ done (task Q) | 1 (was 38 + 18 related + 5) | | | | | |

The unit counts of bigint and enums come from a few files full of top-level
constants; by files they are the least valuable groups.

### Group details

Each entry: the refusals it covers (normalized: positions and quoted names
dropped), examples, what the extension needs.

1. **`Array<T>` from lib.** *Done (task B): `Array<T>`/`ReadonlyArray<T>` are
   read as `T[]`/`readonly T[]`, `Record<K, V>` as the library's mapped type at
   its arguments, `Function` as callable-or-class (DESIGN.md, "Library
   types"); +23 units, +22 functions, no unit lost. The 59 + 19 units now stop
   at their next blocker (else-if, rest parameters over `readonly`/alias
   arrays, generics, `typeof`, number/symbol mapped keys, `class … extends
   Array`); the new search refusals were read and are incompleteness, not
   SKJS unsoundness.* Before: `source: duplicate field name in a record in
   typescript/lib/lib.es5.d.ts#Array` (48), `#ReadonlyArray` (11). Written
   `Array<number>` rather than `number[]`, the reference is read as the lib
   interface, whose overloaded methods collide. Examples:
   `array-object-union-operations.ts#testCommonProperty`,
   `array_literal_examples.ts#promoteNonUniformTuple`,
   `class-extends-generic-constructor.ts#StringArray`. Needs: the declaration
   reader resolves `Array<T>`/`ReadonlyArray<T>` to the fragment's array types
   (or merges overloads). No dependencies; unblocks part of 13.
2. **Relational operators.** `source: binary operator outside the fragment (<)`
   (36), `(>)` (9), `(<=)` (5), `(**)`, `(**=)`. Examples:
   `constprop/loops.ts#counted`, `complex-expressions.ts#testTernaryWithBinaryOps`.
   Needs: number (and string) comparison typed to `boolean`; `**` as number
   arithmetic. No narrowing involved.
3. **Claim differs from annotation.** Done: all 17 units pass the claim
   check, 5 verify (`equality.ts#strictInequalityDisjoint`,
   `#alwaysTrueNumber`, `local-vs-local-refinement.ts#testVarVsLiteral`,
   `unit.ts#check8`, `type-query-memo-stability.ts#queryCompoundIntersection`).
   Two causes. The literal type `0` denotes both runtime zeros in Lean's
   annotation lowering, and the producer claimed only `+0`; it now reads an
   annotation's `0` as both (every literal-union unit here had a `0`). And
   Lean's source lowering of a record intersection refused readonly fields
   (`cell read and write types do not describe the same invariant`); it now
   lowers them by the declaration meet, as views
   ([DESIGN.md](../DESIGN.md#compositional-unions-at-the-source-boundary)).
   The other 12 now stop at their next blocker: 9 at equality between two
   literal unions (15), 2 at truthiness of a number
   (`conditions.ts#acceptLiteralUnion`, `#acceptOctalZero`), 1 at narrowing a
   field by `x === o.v` (`local-vs-local-refinement.ts#testVarVsLocalFieldNarrowsField`, 18).
4. **Ambient declarations — done (task C).** Were `source: only the export
   and async modifiers are admitted on a source function` (53: `declare
   function`) and `an ambient declaration other than 'declare const k: unique
   symbol' is outside the fragment` (41), always as a dependency. A `declare
   function`, `declare const` or `declare class` now joins the module's
   values like an import, read from its own declaration by the declaration
   reader (specifier `ambient`); overloads, ambient or imported, are the
   conjunction of their signatures; `declare let`/`var` is refused as module
   storage ([DESIGN.md](../DESIGN.md#modules-and-code-units), "Ambient
   declarations"). Of the 94 units, 22 in 12 files verify; the other 72 stop
   at their next blocker: 9 at a generic call whose binder the producer
   instantiates at `number[]` where the bound is a tuple
   (`tuple-constraint-literal.ts`, `exact<K extends [0, 1]>(x: K)` called with
   `[0, 1]`: TypeScript infers `K = [0, 1]`), 8 at explicit type arguments on
   a function call, 5 at other failed searches (producer inference of a
   binder from a later use, `tvar-widening-ordinary-check.ts#testNestedCandidate`;
   string `+`), and the rest at gate forms of other groups (object types with
   construct signatures or methods, `typeof` types, rest-parameter contracts,
   `.call`/`.apply`/`.bind`, `instanceof`). One new search refusal is an SKJS
   unsoundness (`testEscapedInferredLiteralStaysClosed`,
   [below](#confirmed-an-inferred-literal-type-through-a-generic-declaration-is-closed-testsexpect-errorobj-literal-indexeststestescapedinferredliteralstaysclosed));
   the others are sound instantiations the producer does not propose, or
   forms Lean does not yet derive. Four `declare class`
   units that the gate refused as generic classes also moved on (2 to
   search, 2 to the producer).
5. **Control-flow forms — done (task F).** Were `closure block must return
   on both terminal arms` (31; void block closures and void methods), ``else
   if` and non-block branches`` (29), `a bare 'return'` (7), statements after
   return (4). An unbraced arm is its block, `else if` a nested `if`, `return;`
   is `return undefined`, a block closure falling off its end returns
   `undefined`, and statements after one that always jumps are dropped unless
   a name they declare is hoisted or read live
   ([DESIGN.md](../DESIGN.md#statement-forms)). 30 of the 100 units verify;
   the others now stop at discriminated-union and literal narrowing (15, 16),
   `let` inside closure bodies, and flow narrowing in search (18).
6. **`switch` — done (task F).** Were `statement outside the fragment
   (SwitchStatement)` (44). Lowered to labeled blocks, one per clause, with a
   dispatch of `===` tests: fall-through is exact, `break` leaves the switch.
   No case narrowing: 22 of the 46 units verify; the other 24 stop at a test
   against a string or Boolean label (15) or need the scrutinee narrowed by
   its case (`switch.ts#caseNarrowsTheScrutinee`, exhaustiveness). *Case
   narrowing done (task I): every accepted unit of the `switch*.ts` files
   verifies but the "no function" policy (`switch-scope-merge.ts#switchSeed`
   and its dependant) and one missing environment declaration
   (`switch-clause-termination.ts#terminalLastClauseLeavesNoPath`).*
7. **Unary operators.** `unary operator outside the fragment` (39; 18 of them
   negative bigint constants). `precedence-types.ts#testUnaryBinaryTypePositive`.
8. **`void e`.** *Done (task E): `void e` is the comma form `e, undefined`,
   one new source form (`comma`, also the comma operator) lowered by binding
   the left operand in an unread slot, no new calculus term or rule
   ([DESIGN.md](../DESIGN.md#string-concatenation-templates-and-void)).* Was
   `expression outside the fragment (VoidExpression)` (27). 13 verify; the
   other 14 stop at their next blocker: field narrowing after an effect
   (`call-effect-boundaries.ts`, the same without `void`), tuples as
   `Iterable`, `typeof` (2), destructuring, rest and generic arrows, and 2
   constant-only units ("no function").
9. **Template literals and string `+`.** *Done (task E) for expressions: `+`
   with a string operand is the operator rule's concatenation (`binop`
   concatenates, `opResult` classifies a string), the other operand any
   primitive but a symbol, converted by `ToString` exactly (`primString`;
   `numberToString` is `Number::toString`, checked against node for 300
   pseudo-random doubles); an object or symbol operand is refused. A template
   is the parser's left-nested concatenation of its parts. 18 template units
   and the 4 string-concatenation search failures of 18 verify.* Were
   `TemplateExpression` (42), `FirstTemplateToken` (9), and search failures
   on `"Hello, " + name` (`string.ts#const_plus_const`, `cfg/linear.ts#greet`).
   Of the rest, 26 stop at a member read on a primitive (`n.toFixed(2)`,
   `s.length`), 16 are constant-only units ("no function"), and 17 are
   template literal *types* (22).
10. **Mutable bindings.** `proposal: mutable binding requires an explicit fixed
    storage contract` (34: unannotated `let x = 0`), `source: a 'let' needs an
    initializer` (13), `module constant _ is read by a function, so it needs an
    annotation` (3), `proposal: assignment to immutable binding` (2:
    reassigning a parameter). Examples: `constprop/locals.ts#main`,
    `gap-definite-assignment-union-undefined.ts`. Needs: the producer proposes
    the widened initializer type as the storage contract (as TypeScript
    does); parameters as mutable cells; definite assignment for `let x: T;`.
11. **Compound/update assignments.** *Done (task E): the producer proposes
    `update`, `logicalAssign` and `nullishAssign`, which Lean already lowered
    (target parts once, read at the storage contract, the operation, the
    write back); `x += s` concatenates, and an increment is refused on a
    non-numeric target (it converts to a number). 23 of 29 verify.* Were
    `proposal: expression update` (16), `logicalAssign` (3), `nullishAssign`
    (1). Left: `arrayAssign` (4, `[a, b] = [b, a]`: destructuring, 12; done, task H),
    `source: only field and local assignments are supported` (1, a pattern
    default), and 2 moved on (`&&`, a loop edge).
12. **Destructuring and parameters.** *Done (task H): one recursive
    `Pattern` (Fragment `destructure` statement, `destructBody` in a closure
    body) for object and array patterns, nesting, holes, a tuple's rest, and
    defaults (a tag dispatch on `undefined`, a declared alias told apart
    clause by clause); array patterns read positions of any array under the
    `%Iterate%` trust, replacing the fresh-literal-only rule; parameter
    patterns and defaults of functions bind a hidden name and start the body
    with the pattern; closure parameter patterns likewise; array assignment
    with a rest; rest parameters `readonly T[]`, readonly tuples and aliases
    of either (DESIGN.md, "Patterns"). 911 → 993 units (+82), 860 → 942
    functions, 96 → 101 whole files, none lost (marker corpus). The 15 left
    in the group: a rest over an array of unknown length is a slice (4:
    `restFromArray`, `restTargetOfArrayAccepted`, and unions of tuples of
    different lengths `declaredRest`, `emptyRemainder`; no slice term),
    object rests (3: the copy's keys are the source's, which a record does
    not bound), `let` patterns (2), rest parameters typed by a generic alias
    application or an intersection over a binder (task N), and `...x: number`
    (not an array). Units that moved on stop at field narrowing after a guard
    (`earlierPatternRead`, `checkedNestedPattern`,
    `unsound-refinement.ts#checkedDeclarationDefault`), a local shadowing a
    module constant, a pattern reading a method (`compatibleDestructuring`,
    refused as `c.m` is), and a fixed arrow into a variadic signature
    (`observedOptionalSourceForArrayRest`); none is an SKJS unsoundness.*
    Were: `proposal: statement pattern` (29),
    `statement arrayPattern` (10), `rest elements` (12), `default parameters`
    (10), `destructuring parameter` (10), `expected an ordinary closure
    parameter` (8), `array pattern holes` (6), `a rest parameter needs a tuple
    of required positions or a mutable array` (8), nested patterns (2), `let`
    pattern (1). `array-destructuring-rest.ts#restFromTuple`,
    `destructuring.ts#usefulDefault`. Desugar to reads (the Fragment already
    has field/index reads); defaults need the `undefined` test.
13. **Library globals.** *Task K (first part): a global value may be called,
    `BigInt(v)`, at the call signatures TypeScript resolves the calls to, and
    an interface of the global's name (`interface BigInt` beside `declare var
    BigInt`) is its type meaning, not a second value. A standard library
    global is read only through a reviewed overlay
    ([DESIGN.md](../DESIGN.md#library-globals), `tools/library-globals.mts`):
    `BigInt` at a bigint, a Boolean, or an integer or string literal it
    converts; `Symbol`, `Symbol.for`/`keyFor`; `String` of a primitive;
    `console.log`. 703 → 709 units verify (`simple_bigint_test.ts` 2,
    `symbols.ts` 4), no unit lost; the 102 `BigInt` units stop next at
    reads on primitives (`x.toString()`, 39, task L), template literals (7)
    or the init-only policy (52). Left, by first blocker:* `Array.isArray`
    (23: `isArray(arg: any): arg is any[]` is a guard at `any`, and an array
    test reads the heap, which a value shape test cannot; needs a new test and
    narrowing rule, group 17), constructs `new Error` (23, behind `throw`;
    an `Error`'s `name` is inherited, not own, so the declared interface
    is not its own-field record), `new Array`/`Set`/`Map`/`Date`/`Promise`
    and `instanceof Array` (`Array is read only through its members`, 15),
    well-known symbols as values (`Symbol.iterator`, 8; `unique symbol` is
    read as a key, not yet as a value), `const s: unique symbol = Symbol()`
    (11, TypeOperator; done, task O), a global both called and read through a method (1),
    and unlisted statics: `Promise.resolve`/`reject`/`all` (generic;
    `resolve` adopts thenables), `JSON.stringify` (returns `undefined`,
    throws on bigints), `Object.keys`.

    *Task K2 (second part, done): `Promise.reject` and `new Promise(e)` as
    the intrinsics `%PromiseReject%` and `%NewPromise%` (`resolve` bounded
    at the primitives, as `%AsyncReturn%` is); `JSON.parse` stated at
    `unknown` (no reviver) and `JSON.stringify` at `JsonValue`, primitives
    and dictionaries of them, which own nothing the host calls (arrays and
    open records may own a callable `toJSON`); `Set<T>`, `Map<K, V>` and
    `Date` read through an interface overlay (`interfaceOverlay`, listed
    members as host-relative methods, `this` results as the receiver) with
    stated constructors of arrays; `Date.now`; `x instanceof Array` as the
    `isArray` test; the generic `Object.values`/`entries` at a dictionary;
    `repeat`, `normalize(form?)`, `split`/`replace`/`replaceAll` of string
    patterns and `toLocaleString(locales)`. 1,420 → 1,425 units, 917 → 922
    functions, 141 → 142 whole files, none lost: `promise-value.ts` 2,
    `date-constructor-string.ts#test`, `typedArrayIdentity`,
    `testTernaryWithInstanceOf`. The units they reached and still refuse
    are incompleteness: loops and spreads over a `Set` or `Map`
    (`symbols.ts`, 4; `%Iterate%` is stated for arrays), `m.keys()`
    (`MapIterator` not read), `instanceof Array` narrowing `unknown` (4; the
    documented `isArray` limit), `Object.values` of `Closed<T>` (read as
    `T`, an open record), and `new Date("2020-01", 1)`, which TypeScript
    rejects. None is an SKJS unsoundness.*

14. **Reads on primitives and unions; value-level `&&`/`||`.** *Done (task
    L): truthiness is a tag test (`ToBoolean`), so a condition that is not a
    Boolean, `!x` and `&&`/`||` returning an operand are the existing tag
    machinery (DESIGN.md, "Truthiness"); a string's `length` and code units
    are calculus reads (`lenStr`, `elemStr`: `s[i]` is `string | undefined`
    for any number), and every other member of a primitive is read through a
    wrapper of its realm prototype, whose contract (`StringProto`,
    `NumberProto`, `BigIntProto`, `BooleanProto`) the array overlay reads
    from TypeScript's library, narrowing `toString(radix)` to 2..36 and
    `toFixed` digits to 0..100 (DESIGN.md, "Primitive members"). 703 → 764
    units verified (+61), 672 → 728 functions, 61 → 68 files fully verified,
    none lost (marker corpus, before the `--skjs` rerun).* Of the 115 units
    stopped at a bigint or other primitive member read, 88 are top-level
    constants that now stop at the "no function to verify" policy (Q); the
    others stop at string `+` (E), `Promise` members (P), field narrowing
    after a guard (18), discriminated unions (16) or literal equality (15).
    Left here: a method call on a union of primitives
    (`this-parameter-union-receiver.ts#primitiveUnion`: each shape's member
    takes its own receiver; the call would need to dispatch by shape), `x[42]`
    on a string index signature (a numeric key's property name), and dynamic
    string index writes (3: `x[k] = v` may add a key, and the calculus's
    objects have their keys fixed at allocation). None of the new search
    refusals is an SKJS unsoundness.
15. **Equality.** *Done (task I): a singleton operand of every primitive kind
    selects a tag test (Boolean `boolEq` and bigint `bigintEq` added beside
    null, undefined, number and string), which narrows the other operand on
    both edges; any other `===` is the strict-equality operator (`Arith.eq`,
    the `arith` rule), exact where one operand is a primitive or an object
    with a field (an object value is its field locations, fresh at
    allocation); two unions of singletons, and a field against one, dispatch
    as their tag tests and narrow where equal; `x == null` is the nullish
    test and other `==` is refused at the gate (it converts); an observation
    the tested type rules out makes its edge never taken
    ([DESIGN.md](../DESIGN.md#strict-equality-and-tag-narrowing)). Was
    `equality requires a null, undefined or numeric singleton operand` (46).*
    Left (6): two operands that may both be objects without a field
    (`equality.ts#weakObjects`, `#funDisjoint`, `#funCounterExample`,
    `#promiseDisjoint`, `#promiseCounterExample`, `void.ts#x7` comparing two
    `void` results):
    closures and all-optional records have no field location, so two of them
    would be one value in the model though JavaScript tells them apart; refused
    with that reason. Narrowing by object identity (`x.child === narrow` in
    `unsound-refinement.ts#stableMemberScalar`), by a call operand
    (`local-vs-local-refinement.ts#testVarVsCall`) or a field against a field
    (`#testFieldVsFieldNarrowsBoth`, `field-refinement.ts#testFieldNarrowedToIntersection`)
    stays an incompleteness in search.
16. **Discriminated-union narrowing.** *Done (task I): a test of a field of an
    immutable binding's object against a singleton keeps the arms whose field
    admits the outcome, checked by a field slice on the branch edge (a heap
    meeting the world holds the field's contract at its location, so the arm
    is fixed at allocation and survives later writes); what the field holds is
    a current-content fact until a step may write it; `switch (s.kind)`
    re-reads the field at each case. Was `proposal: missing field _` (28).*
    Left (3, `algebraic-data-types-comprehensive.ts#processMessage`,
    `#testNestedADTs`, `#testOptionADT`): the object is held by a `let`, a cell,
    whose current contents Lean knows only as primitive atoms, so a guard
    cannot narrow the object it holds. (`local-objects.ts#testReassignGrownField`
    and `unsound-refinement.ts#grownAliasField` match the same "missing field"
    reason but are object growth, not narrowing;
    `array-isarray-refinement.ts#testArrayMethodsAfterRefinement` and
    `#testEarlyReturnWithLength` are a read of `length` after `Array.isArray`
    on a union, the overlay's narrowing.)
17. **`in`/`instanceof`/`typeof`.** Task J took `typeof` as a value (a
    chain of tag tests, claimed `string`) and `typeof x === "object"` (the tag
    `typeofObject`: null or an object without call code), and `key in o` as
    the tag `hasKey`, an own-key test, with a literal key or a union of string
    literals, refused with reasons where JavaScript's answer differs: a key a
    realm prototype holds, an array index, a `string` key, a primitive or class
    operand ([DESIGN](../DESIGN.md#guards)). Left, by reason: `instanceof` other
    than `instanceof Array` (25: the model gives an object no identity of the
    constructor that made it; 12 of them also generic classes), a class with a
    static `[Symbol.hasInstance]` (4: a computed static member), `typeof` in
    types (31, done, task O), numeric `in` keys (3), `string` keys (2). Outside the
    group, presence narrowing after `in` on an optional field or a dictionary
    (4, search) and `x[s]` after `s in x` with a union key (3, producer).
18. **Search found no derivation.** *Task S: triaged obligation by
    obligation, 169 units in 67 files at the start (the marker corpus at the
    task-O commit; 158 in the unit itself, 11 through a dependency). The
    message now names the failed obligation and why: the verifier's sentence
    names its role (`… evidence search failed: no derivation of its
    return-contract claim`, `… the edge from node N does not establish the
    claims at this point`), and `check.mts` adds the reader's source-term
    summary as an `obligation:` line (`The available claim for y is "a" | "b".
    This return requires "a".`; for a term that is not a slot, its form and
    the claims of the slots it reads), which the coverage rows carry. The
    reader had been refusing every node and edge record since nodes gained a
    handler field, so no search failure was explained before
    ([OBLIGATION-DIAGNOSTICS.md](../OBLIGATION-DIAGNOSTICS.md)). Of the 169: 45
    verify, 11 are refused by the producer with a named reason, and 113 stay,
    by cause below.*

    Fixed (45 units; kind (a) producer proposal unless marked):

    | Cause | Units | Fix |
    | --- | ---: | --- |
    | A fresh object or tuple literal at a union of records or tuples was widened, so no arm admitted it (`algebraic-data-types-comprehensive.ts` 3, `function-union.ts` 2, `spread-union-distribute.ts` 2, `typeof.ts` 2, `stypes-diff.ts`, `delayed-literal-union-contract.ts`) | 11 | built at the arm its keys, length and literal members select ([DESIGN.md](../DESIGN.md#fresh-literals-have-exact-keys)) |
    | Generic call inference: a binder in `A \| null` (2), a fresh literal at `T extends Json` (3), primitives and arrays of primitives below a declared bound (3: `tvar-widening-in-constraint-check.ts`, `constrainedArrayLiteralDirect` and its caller), a tuple at `readonly T[]` for `for...of` (1) | 9 | `Inference.infer` and the literal's construction at a dictionary bound |
    | A closure literal claimed at its widened result where the context asks for a literal or an async body's promise (`object-literal-function-field-widening.ts`) | 6 | contextual return type where the body fits it |
    | An unannotated constant's fresh array committed by its first use, as SKJS does (`array_literal_examples.ts` 3 and 3 callers) | 6 | built at the array type its first use expects |
    | A closure used where a signature binding more parameters is expected, outside a call (`function-subtyping.ts` 3) | 3 | offered that signature wherever it flows |
    | A loop head claiming every assigned cell at its contract (`loop-jump-edge.ts`, `jump-edge-definite-assignment.ts`, `for-in-for-of-invalid.ts#loopScopeRestoresOuter`) | 3 | the head found by running the body until stable; the update from the body's end and its `continue`s; the exit from the head and its `break`s |
    | (b) A jump's slot map found a binding by name, so a parameter hiding a module constant gave the constant its narrowed slot (`deadcode/try_catch.ts` 3) | 3 | Lean's `leave` finds bindings by descriptor |
    | `+1` typed `number` (`unary-as-const.ts`, `contextual-literal-args.ts`) | 2 | the parser reads a signed decimal literal as the literal, as it did `-1` |
    | Equality with an enum member or an ambient constant's field did not narrow (`enums.ts#narrowByEquality`, `local-vs-local-refinement.ts#testVarVsGlobalField`) | 2 | the producer reads module values' fields |

    Refused by name (11, kind (c)): a write adding a key to a record allocated
    without it (9: `local-objects.ts` 7, SKJS's growth of a local `{}`, which
    TypeScript refuses too; `test.ts#myObject`; `symbols.ts#testBracketAssignString`)
    and a write to a writable optional field (2:
    `object-type-readonly-fields.ts#assignNumberToOptional`,
    `parameter-property-undefined.ts#writeUndefinedToTranslatedField`): an
    object's keys are fixed at its allocation, and a write that adds one needs
    a key-adding write in the calculus
    ([DESIGN.md](../DESIGN.md#object-literals), "A write never adds a key").

    Left (113), by cause:

    | Cause | Units | Kind | Owner or reason |
    | --- | ---: | --- | --- |
    | Index signatures: `v[k]!` of a `for...in` key (`forin-exclamation.ts` 8), writes and numeric keys on a string index (`index-signatures.ts` 3, `local-objects.ts#testWithIndexSignature`), `Closed<T>` (read as `T`, an open record) into a dictionary or `Json` (`closed-type.ts` 5, `json-named-object-type.ts` 2) | 19 | (b)/(c) | key-restricted index signatures (parallel task) |
    | Flow narrowing: a guard on an optional field (5: the key may be absent, and a heap fact names a field location), a test against several singletons, a call or another field (4), object identity (2: `x.child !== narrow`), fields of a union of records or a view of one (4, `unsound-refinement.ts`), a computed key assigning its own receiver (3), cells written in a `try` or across a condition that calls (3: the producer forgets every cell at a call, having no capture analysis), an assignment inside a conditional expression, `x === null && true`, and knowledge across nested loops with `continue` (1 each) | 24 | (b) | Lean's heap knowledge and the producer's cell tracking; none is an SKJS unsoundness (each read) |
    | `for...of` and spreads over a non-array iterable: a string, `Set`, `Map`, an iterator (`symbols.ts` 4, `for_in_for_of_tests.ts` 2, `for-in-for-of-invalid.ts`, `iterator-effects.ts`, `callgraph/for-of-iterator.ts`) | 9 | (c) | `%Iterate%` is stated for arrays only ([DESIGN.md](../DESIGN.md#loops-over-arrays)); a string's and the host collections' iterators could be stated, a client's cannot (its `return`) |
    | Generic call inference: a tuple literal at a bound with a tuple arm (2), `K extends 0 \| 1` through `Array<[K, number]>`, explicit type arguments with a `const`-bound array (which TypeScript refuses), nested instantiation (`per-field-tvar-isolation.ts`, `tvar-widening-ordinary-check.ts`), a spread into a generic, and `new Container()` instantiated from later pushes (2; TypeScript infers `unknown` and refuses) | 9 | (a) | producer inference |
    | SKJS unsound (confirmed, [below](#suspected-skjs-unsoundnesses)): aliased views of an empty literal (`obj-literal-indexes.ts` 6), an inferred literal type that stays closed, `typeof c === "function"` on a class instance | 8 | (d) | reported |
    | Guards: `Array.isArray` narrowing a union with a record (6), `typeof x === "function"` on `unknown`, `instanceof Array` at a readonly array | 8 | (b) | typeof/in/instanceof guards (parallel task) |
    | `Promise<A>` below `Promise<B>` (`promise-object.ts` 6): `then` and `catch` are generic methods, and relating two instances needs subtyping of quantified signatures | 6 | (b) | the search relates schemes only by identity |
    | A module function used where a longer signature (or an intersection with one) is expected (`function-intersection.ts` 4, `function-subtyping.ts#testMissingRestFails`) | 5 | (c) | its slot is its annotated signature, checked by its own unit; offering it more would make that slot a claim ([DESIGN.md](../DESIGN.md#method-members-are-host-relative)) |
    | Classes: inheritance across a shadowed binder (`tparam_shadow.ts` 2), field annotations and a `#private` field in a class body, a method reattached through a `this` parameter | 5 | (b) | spreads and class inheritance (parallel task) |
    | SKJS's own literal typing, where TypeScript differs and the pipeline follows TypeScript: `[1, "a"]` as a tuple (2), an evolving `[]` (2) | 4 | (c) | TypeScript types these as `(number \| string)[]` and `any[]` |
    | An array's `length` as a record field (`{ readonly length: number }` view, a union with a record, an intersection with one) and an 11-tuple's `length` as the literal 11 | 4 | (b) | `length` is the calculus's `lenArr`, not a field; a mutable tuple's length is not fixed by its type |
    | Computed types that follow TypeScript: `keyof typeof E` excluding reverse keys, `keyof ({ x: number } \| string)` (`never`), the meet of two tuple types | 3 | (c) | TypeScript's computed type |
    | `aliased views without fields` (`obj-literal-indexes.ts#testAliasMutableOptionalThenOptional`, `#testAliasTwoReadonlyOptionals`): sound, refused | 2 | (b) | as the unsound family's search |
    | `<` with an operand that may be `undefined` (`supertypePositionTest` and its caller) | 2 | (c) | the rule admits only operands compared in their primitive order ([DESIGN.md](../DESIGN.md#numeric-operators-and-bigints)) |
    | A tuple as `Iterable<T>` (`tuple-iterable.ts` 2) | 2 | (b) | the search relates a tuple's store to `Array.prototype[Symbol.iterator]`'s element only for arrays |
    | An optional parameter at a rest signature, a `this: undefined` function as a plain callback, a nested array literal at a generic class's constructor | 3 | (b) | search |

19. **Classes.** `a class member modifier outside the fragment` (54:
    `private`/`protected`/`static`/`readonly`/`#x`), optional or
    definitely-assigned fields (17), parameter properties (9), inheritance
    (7 + 2 in the producer), constructor statements other than `this.f = e`
    (5), method receivers (4), optional/generator/generic methods (3).
    *Inheritance done (task M2; DESIGN.md, "Class members"):* a base
    declared earlier in the file, `super(...)` after statements not reading
    `this`, `super.m(...)`, overrides checked against the base's member types,
    an implicit constructor over a base taking nothing. Left: an implicit
    constructor forwarding a base's parameters, `instanceof` a derived class
    (the model's derived prototype is a copy, not a link), `extends` of a
    library, ambient or later class.
20. **Generic classes.** `a generic class is outside the fragment` (47).
    An instance of `class Box<T> { v: T }` is a record over its binder, which
    no universal certificate reaches yet (21, left).
21. **Generics.** *Done (task N): a bound may be any ground type (the parser
    admits every constraint; `DeclarationGraph.prepare` lowers a ground bound
    to graph rows; a local closure's substituted bound is checked by the
    graph's certified subtyping, as a module value's); direct types have
    unions mentioning a binder, `string | T` (`Ty.union`, one canonical
    spelling `Ty.mkUnion`; `RigidJudgments.Sub` gains union reflexivity, a
    union below what each member is below, a non-ground type below a union
    through one member, a ground list label by label; `Sub.sound` and
    `leUnder_iff_Sub` extended); a rigid body may end without a return
    (`undefined`), contain expression statements, and nest a closure the
    source leaves without a result annotation (its claimed arrow's result,
    checked against the body); explicit type arguments on plain calls and
    `new` are checked against the claimed instance (`Scheme.explicitInstance`,
    module values and local quantified closures alike); `e as const`
    (readonly tuples and fields of literal types, a cast kind with no
    annotation); an array literal at a binder bounded by a tuple is built at
    the tuple (`exact<K extends [0, 1]>([0, 1])`, `K := [0, 1]`); an
    intersection ground once a call fixes the binders, `T & DepSafe` at
    `T := Todo`, is the graph's meet (`sum-serializable-freeze` verifies).
    911 → 982 units verified on the marker corpus (+71, none lost),
    860 → 930 functions, 96 → 103 files fully verified; the generics group
    161 → 58.* Left, by first blocker: `rigid type nested in a graph type`
    (40: records, tuples and object literals over a binder, `Box<T>`,
    `List<T>`, `[T1, T2]`), `field read on rigid parameter` (6: `x.length`
    through the bound `T extends { length: number }`), `generic claim
    checking requires a checked variable-copy body` (9: `if`, `let`, `typeof`
    in a generic body), number and string literals, `??` and `===` in a
    generic body (about 15, counted under other groups), generic function
    types as annotations (3). Records over a binder are out for one reason:
    the universal certificate (`GenericCertificate`, for every admissible
    assignment) exists only for the direct checker, whose types have no
    record; graph evidence certifies a body at the graph's own assignment of
    its parameter rows (`meaning G = mixedValues G G.env`), and the evidence
    checker is not proved independent of that assignment, so it cannot supply
    the universal statement callers rely on. The two ways forward are
    records in the direct checker (a proof constructor per heap operation) or
    that independence theorem for `CertificateProducer.accept`. One new search
    refusal is an SKJS unsoundness
    ([below](#confirmed-a-body-falling-off-its-end-at-a-binder-bounded-by-void-testsexpect-errorvoidtsreturningconstrainedvoid));
    the others read were sound instantiations the producer does not propose
    (a fresh literal at `T extends Json`, spreads into a generic) or forms
    of other groups.
22. **Type forms.** *Done (task O): a computed type, `typeof x`, `keyof T`,
    `T[K]`, a template literal type, an intersection of primitives and a
    mapped type's keys, is the type TypeScript's checker computes, evaluated
    by the declaration reader where it is written (`computed-types.mts`,
    DESIGN.md "Computed types") to a union of literals and primitives, or to
    the declared annotation or value type it names under the checker's type
    identity; `object` is every object and `{}` every value but `null` and
    `undefined`; method signatures in type literals are host-relative members
    (the producer's `host` fields); a type literal of construct signatures is
    a class value; a numeric property name is its `ToString` key, in types,
    mapped types, object literals and number-keyed reads of non-arrays; a
    `unique symbol` constant holds a symbol and names a key, by what made it
    (`Symbol()` its own, `Symbol.for("k")` the registry's "k");
    annotation intersections are Lean's meet; an index over `string | number`,
    or a number index of the string index's contract, is the string index;
    `Record<K, V>` and mapped types take the keys TypeScript computes (an
    alias of literals); `keyof typeof E` of an enum. Construct-signature type
    literals and numeric keys build on task R's readings. 1,791 → 1,897 units
    verified on the marker corpus (+106, none lost), 1,261 → 1,350 functions,
    180 → 193 files fully verified.* `enums.ts#keyOfIncludesReverseKeys`
    returns `0` at `keyof typeof E`, which SKJS admits (the enum object owns
    the reverse key "0") and TypeScript does not (`"A" | "B"`): the pipeline
    follows TypeScript, which is sound, so this is incompleteness, not an SKJS
    unsoundness. *Number and symbol index signatures (25 + 3 mapped over
    `number`, 12 + 4 over `symbol`) were done afterwards by the index-keys
    task (below).* Left, each refused with its reason: TypeScript errors in declarations and duplicate
    declarations (13 + 6: `Duplicate identifier`, implicit `any` members,
    properties not assignable to an index, which SKJS accepts and TypeScript
    rejects); forms over a type parameter (`T[number]`, `keyof T`,
    intersections with a binder, 8 + 7 + 1: computed only at an instance) and
    the producer's `a type parameter's intersection in a claim` (4);
    intersections Lean has no representable meet for (6); `keyof` with a
    unique symbol key (6: `keyof [number]`, `keyof string`,
    `keyof Promise<T>`); `typeof` of a binding without an annotation (2),
    of a class with statics (1) and of `true` (1, not valid TypeScript); a
    method with a `this` parameter or over a binder in an annotation (4). None
    of the new search refusals is an SKJS unsoundness; SKJS reads
    `keyof (A | B)` as the union of the members' keys where TypeScript takes
    their intersection (`type-operator-precedence.ts#testNestedKeyofBuggy`),
    and refuses indexing with it, so no witness was found.
23. **Loops — done (task F), but `for (let … of …)`.** Were `for-in` (13),
    `for(;;)` (8). `for` is a `while` whose body's end and `continue` run the
    update, in a block scoping its `let`; `for-in` iterates the trusted
    `%ForIn%` (keys, each a string). 11 of the 24 units verify; `forin-exclamation.ts` (7) stops at reads
    through a string key (14), `for` updates at a `continue` after a write
    (`jump-edge-definite-assignment.ts#assignedBeforeTheJump`) at the
    producer's head knowledge; `for (let … of …)` stays refused.
24. **Exceptions** (done). A throw is an outcome of the calculus
    ([DESIGN.md](../DESIGN.md#throws)); `throw`, `try`/`catch`/`finally` and
    `throw new Error(…)` are lowered. What still stops such units is
    elsewhere: a handler that needs the precise state at a raise point
    (`catch-entry-writes.ts#absorbedInnerTryDoesNotEscape`,
    `#separateTryDoesNotLeak`, `jump-through-finally.ts#jumpBeforeTheTryIsUntouched`:
    the handler and the finalizer know each cell by its contract), and a
    `break`/`continue` through a `finally` (refused).
25–31. See the table; each is a handful of gate or producer forms. Task R
    (DESIGN.md, "Optional chaining", "Object literals", "Receivers and
    methods"): of 25, `.call`, `.apply` and `.bind` on the file's function
    declarations, a leading `this: T` parameter as the receiver, and `.apply`
    with an array literal as the `.call` with its elements verify (8 units);
    the rest are overloads and union callees (6), spreads not last or into
    `new` or of a `let` (5, incompleteness), `.call` on a method read from a
    parameter (1: its `call` property is not known to be the intrinsic), and
    `Object.assign` (1, the library overlay's). Of 27, construct-signature
    type literals (`{ new (): T }`, 6 units, 4 of them first blocked here),
    numeric keys in literals and types (8, 6 of them in
    `number-literal-normalization.ts`) and a spread of an object literal (1)
    verify. Task M2 (DESIGN.md, "Object literals"): a spread of a value is
    an allocation from parts copying its operand's own enumerable string-keyed
    properties; a class instance's methods are its prototype's and an
    `Error`'s `message` is on a prototype, so neither is copied; object rest
    patterns are the same copy less the named keys. Left: a spread whose
    result states an index signature (4, a dictionary result clause), a
    string, function or class-value operand, an array's object rest, a
    literal writing a key its type lacks. Two computed keys stay outside. Of 29, 7 verify; `composedReceiverSnapshot`
    stops at the fresh-literal snapshot its plain `snapshot.read()` also
    stops at (incompleteness). `%` (6 units, unclassified before): 3 verified
    before the throw outcome; the other 3, bigint remainders by a `bigint`
    divisor, throw at a zero divisor, an outcome, as `/` does since task S.
32. **bigint.** `BigIntLiteral` (129), the `BigInt` global (102, read since task K), `non-decimal
    numeric literal type` (1). A new primitive in the calculus.
33. **Enums.** *Done (task R): an enum is the module constant bound to the
    object TypeScript's emit makes, members and reverse mappings as readonly
    fields at their literals; `E`, `E.A` and `typeof E` as types; a `const
    enum`'s reads as its values; a number key on a record reads the field its
    `ToString` spells (DESIGN.md, "Enums"). 45 of the 56 units verify.*
    Refused with their reasons: a computed member (5: its reverse mapping is
    keyed by its runtime value), an ambient `declare enum` (1), an empty enum
    (1: an object with no property). Left for other groups: `keyof typeof E`
    (2, type forms), `E[i]` with `i` a union of keys (1), equality narrowing
    `x === E.A` (1, task I). None is an SKJS unsoundness.

34. **Module initialization and the SKJS environment (task Q).** *Done.* A
    module whose only code is its initialization, constants, classes and
    top-level statements, was refused, "no source functions to verify" (453
    units, 88 files, most of them bigint and literal constants and classes).
    It is now a program like any other: Lean checks its initialization unit,
    the one unit it has, and refuses a module with neither function nor
    initialization (DESIGN.md, "A module with no function"). 430 of the 453
    verify; the other 23 stop at their real blockers: equality against a
    bigint or string operand (15, group 15), bigint division (2: it throws
    on a zero divisor) and `BigInt` of a computed string (3: it throws on a
    non-numeric one, and the overlay admits only literals), `+42` claimed at `42` (1, the unary `+`
    result is `number`), and two classes with an optional field never
    assigned (`class C { px?: number }`: the producer claims the instance with
    the field present; incompleteness). Each derived file also runs in SKJS's
    test environment now (Method, "Environment"): the stub imports resolve
    (`Json`, `Mapper`, `InputDefinition`, `functionFromStubs`), and
    `__SKJS_show`, `process`, `StringRecord<V>` and `Closed<T>` are declared;
    of the 45 units these stopped, 20 verify, the unbound-name errors are
    gone, and the rest stop at their next blocker: `EagerCollection`'s rest
    parameter over a generic (6), generic classes (3), `in` (3), one each of
    explicit call type arguments, a rigid type in a graph type, an object
    spread, a field read on a non-object, the relative import above, and
    search failures that are
    incompleteness: `Closed<T>` read as `T` into `Json` or an index signature
    (6, SKJS relies on the absent keys), a fresh literal instantiating
    `T extends Json` (1), `new InputDefinition<string, number>([])` (1). None
    of the new search refusals is an SKJS unsoundness.

**Dependencies.** 1 → 13 → 24 (`throw new Error`); 4 → 13; 2 → 23; 15 → 16, 6's case narrowing, 17; 19 + 21 → 20;
7 → 32 (negative bigint).

## Suspected SKJS unsoundnesses

Divergences: SKJS-accepted units the pipeline parses and proposes, and Lean
then refuses (337 units in `search` before task Q, when 130 of them were the
since-lifted "no function" policy; 356 after it, see 34). 29
"unions with rigid types", 28 "equality with string literals" and the other
source-form refusals Lean states explicitly; those are fragment boundaries. The
rest were read obligation by obligation (group 18 above): all are pipeline
incompleteness except two families. Reading ambient declarations (task C)
reached a third, and generic bodies ending without a return (task N) a fourth.

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
same shape, blocked earlier at the gate.

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

Reached once ambient declarations were read (task C). SKJS reads the result
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

Reached once generic bodies could end without a return (task N). SKJS accepts
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

### Undetermined

None of the other search refusals looked like SKJS errors on reading their
source and obligation; the candidates checked and found sound are
`array_literal_examples.ts#arrayCommittedTypeTest` (SKJS rejects the aliasing
variant), `tparam_shadow.ts` (read-only fields, so covariance is sound),
`function-intersection.ts`/`function-subtyping.ts` (fewer parameters),
`unsound-refinement.ts` snapshots, `void.ts#unsafeInTypescript`. Units refused
*before* Lean (source/proposal) were not examined for unsoundness; widening the
fragment will expose more divergences, so each widening task should rerun this
script and read new `search` refusals. Task R's (an empty enum's allocation,
now refused at the gate; enum equality narrowing; a number key on a string
index; the bigint `%` by a `bigint` divisor before the throw outcome; generic
inference through `Maybe<A>`; a fresh-literal snapshot read through `?.`)
are incompleteness. Task M2's remaining refusals of spreads and derived
classes (listed under 19 and 27) are incompleteness; no new `search`
refusal of an SKJS-accepted unit it reaches is a wrong SKJS verdict.

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
| R. Remaining source forms (done) | Enums (runtime, `const`, types, reverse mappings, number keys on records); object literals (numeric keys, literal spreads, construct-signature type literals; value spreads and accessors refused with reasons); optional chaining as one derived form; `.call`/`.apply`/`.bind` on module functions and `this` parameters as receivers; `%` exact on numbers and bigints | 80 / 19 verified, measured on 414fc86a before task S (1,361 → 1,441 units, 880 → 956 functions, 136 → 142 whole files, none lost) | `fragment-parse.mts`, `type-term.mts`, `declaration-graph.mts`, `annotate-source.mts`, `Fragment.lean`, `SourceExtraction.lean`, `Calculus.lean`, `ProgramTyping.lean`, `source.ml`, `proposal.ml` | D (bigint) | I (enum narrowing) |

Suggested order: A, B, D in parallel (disjoint files except D's gate
entries); then C, E, G; then F, H; then I, K; then J, L, P; M, N, O last (the
largest). Q any time. After each task, rerun the script and read the diff of
`skjs-coverage.json`.
