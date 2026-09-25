# SKJS coverage by the OCaml pipeline

How much of what SKJS accepts in its own test suite the pipeline
(`check.mts`: parser → OCaml producer → Lean search and check) verifies, what
stops the rest, and where the two disagree because SKJS is wrong.

**703 of 2,676 SKJS-accepted units verify (26.3%); 672 of 2,026 accepted
functions (33.2%).** 61 of the 377 files with an accepted unit verify entirely.
Three families of SKJS-accepted functions that the pipeline reaches and refuses
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
| `tests/expect-error` | `@ts-expect-error` / `@skjs-expect-error` name the next non-annotation line (`tests/Helpers.sk` `findExpectErrors`); `@skjs-expect-warning` is not an error | 399 (374 with units) | 3,885 | 2,458 | 578 | 1,863 | 565 |
| `tests/callgraph` | no error allowed | 25 | 59 | 59 | 44 | 51 | 40 |
| `tests/constprop` | no error allowed | 14 | 66 | 66 | 45 | 49 | 36 |
| `tests/deadcode` | no error allowed | 7 | 27 | 27 | 13 | 16 | 8 |
| `tests/cfg` | no error allowed | 7 | 22 | 22 | 11 | 21 | 11 |
| `tests/projects` | expect-error markers, under the project's tsconfig | 24 of 68 | 44 | 34 | 10 | 23 | 10 |
| `tests/ts-conformance/cases` | lines listed in `reference/*.errors.txt` | 4 | 11 | 10 | 2 | 3 | 2 |
| **total** | | **480** | **4,114** | **2,676** | **703** | **2,026** | **672** |

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

**Pipeline.** Each derived file goes through `checkApart` (exactly
`node check.mts <file>`), 10 at a time, with `check.mts`'s 30 s step timeout.
A unit whose run ends in an infrastructure error (a step timeout, the
TypeScript service's "context canceled" under load — seen once) is run again
alone; no timeout remained. Outcome rows: `verified`, or the first blocker with its phase
(`source` = parser gate, `proposal` = producer `unsupported:`, `search` =
Lean found no derivation or refused a source form, `error`), its normalized
reason, its feature group, and where it lies: in the unit's own statement
(`self`), in a statement its closure brought (`dependency`), or `unknown`.

| Phase of first blocker | Units |
| --- | ---: |
| verified | 703 |
| source (gate) | 1,165 |
| proposal (producer) | 322 |
| search (Lean) | 483 (229 of them: "no source functions to verify") |
| error (producer: unbound `__SKJS_show`, `process`) | 3 |

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
- Class and constant units whose closure holds no function are refused with
  "no source functions to verify" (130 units, 71 files). This is a pipeline
  policy (module initialization is verified only alongside a function), not a
  language gap; decide whether init-only files should verify.
- Imports from the SKJS runtime stubs (`Json`, `EagerCollection`, `Context`,
  `Mapper`, …) are unresolved because the run passes no `--project`; SKJS's
  `Closed<T>` stub type is the "unknown type alias". 38 units; an environment
  gap, not a language gap.
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
| 5 | Control-flow forms (`else if`, non-block branches, bare `return`, block closures that fall off the end, dead code) | 72 | 62 | 9 | 21 | M | P L |
| 6 | `switch` | 44 | 42 | 2 | 14 | M | P L |
| 7 | Unary `-`/`+`/`~` | 39 | 21 | 18 | 7 | S | P L |
| 8 | `void e` | 27 | 24 | 3 | 7 | S | P L |
| 9 | Template literal expressions (and `"a" + s`, in search) | 68 (42 expr, 9 no-substitution, 17 types) | 42 | 26 | 14 | M | P L |
| 10 | Mutable bindings: unannotated `let`, `let x: T;`, parameter assignment, unannotated module constants read by functions | 52 | 42 | 0 | 22 | M | O L |
| 11 | Compound / update assignment (`x++`, `+=`, `||=`, `??=`, `a[i] op=`) | 24 | 24 | 0 | 15 | S | O L |
| 12 | Destructuring, rest/default parameters | 96 | 90 | 5 | 22 | M | P O L |
| 13 | Library globals as values (`Array.isArray`, `new Array`, `Symbol()`, `new Error`, `Promise`, `Set`, `Map`, `Date`, `JSON`) | 108 | 94 | 14 | 29 | M | D L |
| 14 | Reads on unions/primitives (field/index read on non-object, string keys) and value-level `&&`/`||` | 48 + 20 | 63 | 0 | 30 | M | O L |
| 15 | Equality against string/boolean literal singletons (Lean refuses the source form) | 37 | 37 | 0 | 5 | M | L |
| 16 | Discriminated-union narrowing (producer: "missing field" after a tag test) | 14 | 13 | 0 | 4 | M | O L |
| 17 | `in` / `instanceof` / `typeof` (expression and type query) | 88 | 81 | 5 | 16 | L | P O L |
| 18 | Search: no derivation found (mostly flow narrowing; see below) | 104 | 101 | 3 | 44 | L | L O |
| 19 | Classes: member modifiers, optional/definite fields, parameter properties, inheritance, constructor statements, receivers | 104 | 65 | 39 | 31 | L | P O L |
| 20 | Generic classes | 45 | 31 | 14 | 21 | L | P O L |
| 21 | Generics: constraints, explicit type arguments on calls, unions with rigid types, rigid types in graph types, `as const` (6 of 9 "unknown type parameter") | 130 | 109 | 21 | 35 | L | P O L |
| 22 | Type forms: index-signature forms, numeric field names, literal types, `keyof`, indexed access, mapped, `object`, `{}`, method signatures, intersections | 168 | 99 | 69 | 41 | L | P D L |
| 23 | Loops: `for(;;)`, `for-in`, `for-of` with `let` | 22 | 22 | 0 | 12 | M | P L |
| 24 | Exceptions: `try`/`catch`/`finally`, `throw` | 11 | 10 | 1 | 6 | M | P L |
| 25 | Calls: overloads, `.call`, spread arguments, `Object.assign`, arrow callee | 12 | 5 | 0 | 7 | M | P O |
| 26 | `await` of non-promises and unions | 12 | 12 | 0 | 2 | M | L |
| 27 | Object-literal methods, accessors, spreads | 33 | 31 | 2 | 13 | M | P O L |
| 28 | ~~Lib `Function` methods, `Record`~~ done (task B) | 0 | | | | | |
| 29 | Optional chaining | 8 | 8 | 0 | 3 | M | P L |
| 30 | Sloppy (non-strict) code reading `this` | 8 | 6 | 2 | 5 | S | P |
| 31 | Other forms (type assertions `<T>e`, empty statement, shadowing, body forms) | 12 | 9 | 0 | 9 | S | P L |
| 32 | bigint (literals, `BigInt`, bigint literal types) | 232 | 100 | 132 | 12 | L | P L |
| 33 | Enums | 56 | 0 | 56 | 4 | L | P D L |
| — | Policy: no function to verify (class/constant-only units) | 130 | 127 | 0 | 71 | S | L |
| — | Environment: SKJS stub imports and `Closed<T>` | 38 (+18 related) | | | 21 | S | run setup |

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
5. **Control-flow forms.** `closure block must return on both terminal arms`
   (31; mostly void block closures `() => { x = 1; }` and void methods),
   ``else if` and non-block branches are outside the fragment`` (29), `a bare
   'return'` (7), statements after return (4), closure returning from a branch
   needs a result annotation (1). Examples:
   `captured-local-write.ts#capturedWriteCorrectType`,
   `algebraic-data-types-comprehensive.ts#processColor`,
   `array_literal_examples.ts#takesArrayOrNull`. Needs: desugaring in the gate
   or lowering (else-if to nested blocks, fall-through to `return undefined`
   for void), plus the dead-code rule.
6. **`switch`.** `statement outside the fragment (SwitchStatement)` (44).
   `switch-boolean-exhaustive.ts`, `loop-jump-edge.ts#breakInSwitchBindsToTheSwitch`.
   Lowering to if-chains with `break` edges (the control-flow checker already
   validates `break`). Case narrowing on string tags depends on 15/16.
7. **Unary operators.** `unary operator outside the fragment` (39; 18 of them
   negative bigint constants). `precedence-types.ts#testUnaryBinaryTypePositive`.
8. **`void e`.** `expression outside the fragment (VoidExpression)` (27).
   `call-effect-boundaries.ts#snapshotAcrossEffect`, `constprop/eval_forms.ts#voidValue`.
   Evaluate, discard, type `undefined`.
9. **Template literals.** `TemplateExpression` (42), `FirstTemplateToken` (9,
   no-substitution), `TemplateLiteralType` (17). Expressions reduce to string
   concatenation, which Lean does not yet derive either (`"Hello, " + name`
   fails in search: `string.ts#const_plus_const`, `cfg/linear.ts#greet`), so
   the concatenation rule comes first. Template literal *types* belong with 22.
10. **Mutable bindings.** `proposal: mutable binding requires an explicit fixed
    storage contract` (34: unannotated `let x = 0`), `source: a 'let' needs an
    initializer` (13), `module constant _ is read by a function, so it needs an
    annotation` (3), `proposal: assignment to immutable binding` (2:
    reassigning a parameter). Examples: `constprop/locals.ts#main`,
    `gap-definite-assignment-union-undefined.ts`. Needs: the producer proposes
    the widened initializer type as the storage contract (as TypeScript
    does); parameters as mutable cells; definite assignment for `let x: T;`.
11. **Compound/update assignments.** `proposal: expression update` (16),
    `logicalAssign` (3), `arrayAssign` (3), `nullishAssign` (1),
    `source: only field and local assignments are supported` (1).
    `complex-expressions.ts#testPostfixWithMultipleOps`. Desugar to read-op-write.
12. **Destructuring and parameters.** `proposal: statement pattern` (29),
    `statement arrayPattern` (10), `rest elements` (12), `default parameters`
    (10), `destructuring parameter` (10), `expected an ordinary closure
    parameter` (8), `array pattern holes` (6), `a rest parameter needs a tuple
    of required positions or a mutable array` (8), nested patterns (2), `let`
    pattern (1). `array-destructuring-rest.ts#restFromTuple`,
    `destructuring.ts#usefulDefault`. Desugar to reads (the Fragment already
    has field/index reads); defaults need the `undefined` test.
13. **Library globals.** `the global X is not an annotated variable`: Array
    (38, mostly `Array.isArray`), Symbol (30), Error (23, `throw new Error`),
    Promise (4), Set (3), Date, Map, String (2 each), Object, JSON (1 each);
    `proposal: unbound name` (2: `__SKJS_show`, `process`). Needs the lib's
    `declare var X: XConstructor` read as values (after 4) with the lib
    interfaces of 1 and 28. `Array.isArray` also needs a narrowing rule (17).
14. **Reads on unions/primitives; value-level `&&`/`||`.** `proposal: indexed
    read on non-object` (24), `field read on non-object` (19), `record index
    requires a string key` (1), `search: a dynamic string index write is
    outside the readonly dictionary fragment` (3), numeric array key (1);
    `proposal: operator &&` (15), `operator ||` (5). `and-or.ts#f`,
    `field-refinement.ts#testAndChain`. Needs member reads on primitive
    wrappers (`s.length`) and on unions, and `&&`/`||` returning an operand.
15. **Equality with string/boolean literals.** `search: unsupported source
    expression: equality requires a null, undefined or numeric singleton
    operand` (37; 9 of them literal-union operands, `x === y` with `x: 0 | 1`,
    after 3). `equality.ts#classDisjoint`,
    `local-vs-local-refinement.ts#testBothOverlapNarrowsLhs`,
    `unsound-refinement.ts#stableMemberScalar`. A Lean source-form restriction;
    lifting it is the base of 6 (case narrowing), 16 and 17.
16. **Discriminated-union narrowing.** `proposal: missing field _` (14): a
    field read after `if (s.kind === "circle")` on a union
    (`field-refinement.ts#testKindRefinement`, `unit.ts#check`,
    `algebraic-data-types-comprehensive.ts#getProgress`). Producer narrowing
    of unions by a literal tag, after 15.
17. **`in`/`instanceof`/`typeof`.** `binary operator outside the fragment
    (in)` (25), `(instanceof)` (18), `proposal: expression typeof` (24),
    `type outside the fragment (TypeQuery)` (21, `typeof x` in types). Guards
    and their narrowing; `typeof` in type position is a separate, declaration-
    reader-sized piece.
18. **Search found no derivation** — the pipeline reaches Lean and fails to
    prove an obligation (`source expression obligation … evidence search
    failed` 88, `closure expression claim` 9, `incoming edge obligation` 4).
    By cause, from the obligations:
    - flow narrowing Lean does not derive: field and local refinement by
      equality and truthiness, narrowing after assignment, snapshots of refined
      values (`field-refinement.ts` 17, `local-vs-local-refinement.ts` 5,
      `truthiness-safe/src/conditions.ts` 5, `unsound-refinement.ts` 4,
      `control-flow-refinement.ts` 2, others 1 each) — about 42;
    - async results and `Promise` subtyping (`object-literal-function-field-widening.ts`
      async fields 5, `promise-object.ts` 4) — 9;
    - contextual object/tuple literals into union alternatives
      (`spread-union-distribute.ts`, `typeof.ts#testMultipleTuples`,
      `function-union.ts`, `delayed-literal-union-contract.ts`) — 8;
    - function values into intersections, rest and `this: void` signatures
      (`function-intersection.ts` 4, `function-subtyping.ts`,
      `this-parameter-void-receiver.ts` 2) — 7;
    - index signatures on unions, writes through index signatures and
      optional fields (`index-signatures-ops.ts`, `local-objects.ts`,
      `object-type-readonly-fields.ts`, `readonly-inter-union.ts`) — 6;
    - inferred/evolving array literals (`array_literal_examples.ts` 4,
      `per-field-tvar-isolation.ts`, `literal-representation-lifetime.ts`) — 6;
    - string concatenation 4, `for-of` over strings 3, `void`/`??` on `unknown`
      and `void` 3, generic inheritance and large tuples 4;
    - **SKJS unsound**: `obj-literal-indexes.ts` (6 of its 8) and
      `callability.ts#testInstanceTypeofFunction` — see below.
19. **Classes.** `a class member modifier outside the fragment` (54:
    `private`/`protected`/`static`/`readonly`/`#x`), optional or
    definitely-assigned fields (17), parameter properties (9), inheritance
    (7 + 2 in the producer), constructor statements other than `this.f = e`
    (5), method receivers (4), optional/generator/generic methods (3).
20. **Generic classes.** `a generic class is outside the fragment` (45),
    after 19 and 21.
21. **Generics.** `only 'extends boolean', an earlier type parameter, or a
    non-generic named type is in the fragment` (38), `search: a union
    containing rigid types is outside a rigid claim` (29), `proposal: rigid
    type nested in a graph type` (24), `explicit type arguments are admitted
    on a method call only` (19), `unknown type parameter` (9; 6 are `as
    const`), `generic claim checking requires a checked variable-copy body`
    (5), `a closure under a binder needs its result annotation` (3), generic
    function types (2).
22. **Type forms.** Index signatures (`unsupported index signature` 28,
    multiple string indexes 6, expected string index 2), literal types (26:
    negative numbers, bigint), numeric/hex field names (`expected a required
    mutable field` 12), `keyof` (21), mapped types (11), indexed access (9),
    empty record `{}` (8), method signatures in type literals (14),
    intersections of aliases/params/arrays or of different shapes (23),
    `object` (4), template literal types (17, counted in 9).
23. **Loops.** `for-in` (13), `for(;;)` (8), `for (let … of …)` (1). `for(;;)`
    needs 2.
24. **Exceptions.** `TryStatement` (10), `ThrowStatement` (1); `throw new
    Error(…)` also needs 13.
25–31. See the table; each is a handful of gate or producer forms.
32. **bigint.** `BigIntLiteral` (129), the `BigInt` global (102), `non-decimal
    numeric literal type` (1). A new primitive in the calculus.
33. **Enums.** `top-level statement outside the fragment (EnumDeclaration)` (56).

**Dependencies.** 1 → 13 → 24 (`throw new Error`); 4 → 13; 2 → 23; 9 needs
string concatenation (in 18); 15 → 16, 6's case narrowing, 17; 19 + 21 → 20;
7 → 32 (negative bigint).

## Suspected SKJS unsoundnesses

Divergences: SKJS-accepted units the pipeline parses and proposes, and Lean
then refuses (337 units in `search`). 130 are the "no function" policy, 29
"unions with rigid types", 28 "equality with string literals" and the other
source-form refusals Lean states explicitly; those are fragment boundaries. The
rest were read obligation by obligation (group 18 above): all are pipeline
incompleteness except two families. Reading ambient declarations (task C)
reached a third.

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

### Undetermined

None of the other search refusals looked like SKJS errors on reading their
source and obligation; the candidates checked and found sound are
`array_literal_examples.ts#arrayCommittedTypeTest` (SKJS rejects the aliasing
variant), `tparam_shadow.ts` (read-only fields, so covariance is sound),
`function-intersection.ts`/`function-subtyping.ts` (fewer parameters),
`unsound-refinement.ts` snapshots, `void.ts#unsafeInTypescript`. Units refused
*before* Lean (source/proposal) were not examined for unsoundness; widening the
fragment will expose more divergences, so each widening task should rerun this
script and read new `search` refusals.

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
| E. Small expression forms | `void e`; string `+` then template literal expressions; compound and update assignments | ~100 / 30 | `fragment-parse.mts`, `SourceExtraction.lean`, `CertificateProducer.lean`, `proposal.ml` | — | D, F |
| F. Statement forms | `else if`/non-block branches, bare `return`, void block closures, dead code after `return`, `switch` (without literal narrowing), `for(;;)`, `for-in`, `try`/`catch`/`finally` | ~150 / 40 | `fragment-parse.mts`, `control-flow.mts`, `SourceExtraction.lean`, `ProgramTyping.lean` | D (for `<` in loops) | D, E, H |
| G. Mutable bindings | Storage contract from a widened initializer, parameters as cells, `let x: T;` with definite assignment, module constants | 52 / 22 | `proposal.ml`, `environment.ml`, `ProgramTyping.lean` | — | I |
| H. Destructuring and parameters | Object/array patterns, rest, holes, nested, parameter patterns, default and rest parameters | 96 / 22 | `fragment-parse.mts`, `proposal.ml`, `SourceExtraction.lean` | — | F |
| I. Literal equality and tag narrowing | Lean equality with string/boolean singletons; discriminated-union narrowing; `switch` case narrowing | 42+ / 10 (plus much of the 42 narrowing failures) | `SourceExtraction.lean`, `ProgramTyping.lean`, `CertificateProducer.lean`, `proposal.ml` | F for `switch` | G, J |
| J. Guards | `typeof`, `in`, `instanceof`, `Array.isArray`; `typeof` in type position | 88 / 16 | `fragment-parse.mts`, `proposal.ml`, Lean narrowing rules | I, K (`Array`) | I |
| K. Library globals | `Array`, `Symbol`, `Error`, `Promise`, `Set`, `Map`, `Date`, `JSON`, `String`, `Object` values from lib declarations | 108 / 29 | `declaration-graph.mts`, `fragment-parse.mts` (globals), `DeclarationGraph.lean` | B, C | B, C |
| L. Primitive and union reads | `s.length` and other primitive members, member/index reads on unions, value-level `&&`/`||`, dynamic string index writes | 68 / 30 | `proposal.ml`, `Calculus.lean`, `CertificateProducer.lean` | B (string lib) | I |
| M. Class members | Modifiers, optional/definite fields, parameter properties, constructor statements, receivers; then inheritance | 104 / 31 | `fragment-parse.mts` (classes), `proposal.ml`, class model in Lean | — | N |
| N. Generics | Constraint forms, explicit type arguments on calls, unions with rigid types in claims, rigid types in graph types, `as const`; then generic classes | 175 / 50 | `fragment-parse.mts`, `inference.ml`, `GenericSource.lean`, `TypeParams.lean` | M for generic classes | M |
| O. Type forms | Index-signature forms, numeric field names, negative-literal types, `{}`, `object`, method signatures, `keyof`, indexed access, mapped types, intersections | 168 / 41 | `fragment-parse.mts` (types), `declaration-types.mts`, `Types/*` | — | N |
| P. Search narrowing and async | Flow narrowing after assignment and refinement snapshots, `Promise`/async results and `await`, contextual literals into unions, function values into intersections | ~80 / 30 | `CertificateProducer.lean`, `ProgramTyping.lean`, `proposal.ml` | I | I, J |
| Q. Run setup | Map SKJS import stubs through `--project`; decide the init-only-module policy ("no function to verify") | 38 + 130 / 21 + 71 | `skjs-coverage.mts` (and the verifier if the policy changes) | — | — |
| R. Leftovers | Object-literal methods/accessors/spread, optional chaining, `.call`/spread calls/`Object.assign`, bigint, enums | 33 + 8 + 12 + 232 + 56 | various | D (bigint), O (enums) | — |

Suggested order: A, B, D in parallel (disjoint files except D's gate
entries); then C, E, G; then F, H; then I, K; then J, L, P; M, N, O last (the
largest). Q any time. After each task, rerun the script and read the diff of
`skjs-coverage.json`.
