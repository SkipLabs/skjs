# SKJS coverage by the OCaml pipeline

How much of what SKJS accepts in its own test suite the pipeline
(`check.mts`: parser → OCaml producer → Lean search and check) verifies, what
stops the rest, and where the two disagree because SKJS is wrong.

Measurement checkpoint: September 27, 2026, after explicit-comparator sorting,
sparse-array contracts and the ordinary-array construction invariant
(full census with SKJS confirmation).

**2,399 of 2,674 SKJS-accepted units verify (89.7%); 1,776 of 2,026
accepted functions (87.7%).** 285 of the 377 files with an accepted unit
verify entirely. There are 73 principled refusals, 10 registered SKJS-unsound
units, 184 gaps and 8 refusals not explained by the automatic classifier.

The user-approved semantics excludes custom array construction, including in
external code: arrays own no `constructor`, and standard constructor/species
behavior is preserved across calls. The array contract and realm invariant
now enforce the own-key exclusion. Under that explicit host assumption,
`map`, `filter` and `slice` have their audited invocation contracts again;
`map` promises a sparse result. `testTupleArrayMethod` in `typeof.ts` and
`contextualSortParams` in `gap-callback-param-contextual-typing.ts` verify
again. No previously verified unit is lost. See the
[native boundary](../DESIGN.md#exact-contracts-and-native-effects).

`testMapReturnsArray`, `mapArr`, and `testMapCallback` remain unverified,
now reaching their original density or callback obligations rather than
stopping at the missing native contract. Checked callback effects are still
needed; the construction assumption alone does not close those targets.

The eight automatic “unexplained” rows have inspected causes. Seven are
`testBasicArrayRefinement`, `testStringArrayRefinement`, `testMultipleUnion`,
`testNestedRefinement`, `testEarlyReturn`, `testCombinedWithTypeof` in
`array-isarray-refinement.ts`, and `testNarrowToArray` in
`array-object-union-operations.ts`. They return an arbitrary array found by
`Array.isArray` as `ReadonlyArray<unknown>`. The realm invariant correctly
permits holes; the source annotation still requires density. This is an
unnecessarily restrictive contract for unknown elements, not evidence that
the programs are unsafe. The curated `isarray-record-array` records the same gap.
The eighth, `testMapReturnsArray`, is the pure-callback dense-map gap above.
The original boundary repair's recursive Promise contracts and the
Promise-dependent framework target remain open; no erased contract is restored.

The SKJS-unsound list records independent runtime witnesses ([below](#suspected-skjs-unsoundnesses)).
Membership alone does not show that the pipeline reached the corresponding
obligation: an earlier refusal can mask it. Verified, gated and rejected outcomes
remain separate in the JSON; aggregate “done” totals are not a closure criterion.

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
| `tests/expect-error` | `@ts-expect-error` / `@skjs-expect-error` name the next non-annotation line (`tests/Helpers.sk` `findExpectErrors`); `@skjs-expect-warning` is not an error | 399 (374 with units) | 3,883 | 2,458 | 2,186 | 1,863 | 1,616 |
| `tests/callgraph` | no error allowed | 25 | 59 | 59 | 56 | 51 | 48 |
| `tests/constprop` | no error allowed | 14 | 66 | 66 | 66 | 49 | 49 |
| `tests/deadcode` | no error allowed | 7 | 27 | 27 | 27 | 16 | 16 |
| `tests/cfg` | no error allowed | 7 | 22 | 22 | 22 | 21 | 21 |
| `tests/projects` | expect-error markers, under the project's tsconfig | 24 of 68 | 44 | 34 | 34 | 23 | 23 |
| `tests/ts-conformance/cases` | lines listed in `reference/*.errors.txt` | 4 | 9 | 8 | 8 | 3 | 3 |
| **total** | | **480** | **4,110** | **2,674** | **2,399** | **2,026** | **1,776** |

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
| verified | 2,399 |
| source (gate) | 85 |
| proposal (producer) | 32 |
| search (Lean) | 158 |

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
  This labels the program, not the reason reached by the current run. An
  earlier gap may mask its unsoundness. A unit of that list that verifies is
  reported as a warning.

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

The script also prints $V + P + S$ as “done”, out of
$N = V + P + S + G + U$. This is bookkeeping, not evidence that every known
unsoundness was reached and refused for its original reason.

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

| Class | Units |
| --- | ---: |
| verified | 2,399 |
| principled (P) | 73 |
| SKJS unsound (S) | 10 |
| gap (G) | 184 |
| unexplained (U) | 8 |
| **accepted** | **2,674** |

Reason definitions and justifications live in `CLASSES` in
[skjs-coverage.mts](skjs-coverage.mts); measured counts live in
`summary.byReason` of [skjs-coverage.json](skjs-coverage.json).
This avoids maintaining another copy of the classifier here.

## Groups

First blocker, not every missing feature of a unit:

| Group | Units | Self | Dependency | Files |
| --- | ---: | ---: | ---: | ---: |
| generic contracts requiring an unsupported exact representation | 46 | 43 | 3 | 12 |
| TypeScript refuses the code too (the pipeline follows TypeScript's types) | 38 | 30 | 8 | 24 |
| destructuring and rest/default parameters | 14 | 9 | 5 | 5 |
| in / instanceof / typeof tests | 14 | 7 | 0 | 6 |
| classes: modifiers, inheritance, fields, parameter properties, receivers | 14 | 7 | 7 | 6 |
| implicit index signatures: a record at an index signature (`Closed<T>` read as `T` among them) | 14 | 14 | 0 | 3 |
| type forms: literal types, keyof, indexed access, mapped, object, index signatures, intersections, method signatures | 11 | 10 | 1 | 7 |
| generics: constraints, explicit type arguments, rigid types, generic function types | 11 | 7 | 3 | 8 |
| object growth: a key-adding write on an object another reference may hold, a dynamic index write | 11 | 11 | 0 | 5 |
| object literal members (methods, accessors, spreads) | 10 | 9 | 0 | 5 |
| calls: overloads, .call, spread arguments, Object.assign, arrow callee | 15 | 10 | 4 | 10 |
| a named function at a signature binding more parameters, or indifferent to the receiver it requires (its type is its annotated signature) | 7 | 7 | 0 | 4 |
| arrays and open records: `Array.isArray` on `unknown`, `length` of an array read as a record's | 8 | 8 | 0 | 5 |
| a non-null assertion on a read at a for...in key (that the object owns the key relates two values) | 8 | 8 | 0 | 1 |
| cells read at their contract (contents known only as primitives or as no `undefined`, and forgotten across a step that may write them) | 7 | 5 | 0 | 5 |
| tests on a value of a type parameter or `unknown` (no rule narrows a parameter row to its meet `T & number`; no object identity) | 7 | 7 | 0 | 4 |
| enums | 6 | 0 | 6 | 1 |
| sloppy (non-strict) code | 6 | 4 | 2 | 3 |
| iterables the program defines: an iterator whose type states no `return`, a spread or a pattern the protocol's lowering does not place, a well-known symbol key other than `Symbol.iterator` | 5 | 4 | 1 | 4 |
| equality: objects without a field (no identity), loose equality | 4 | 4 | 0 | 2 |
| reads on unions/primitives (field/index read on non-object, string keys) | 2 | 1 | 0 | 2 |
| relational operators (< <= > >=) and ** | 2 | 1 | 1 | 1 |
| search: no derivation found (evidence search failed) | 8 | 8 | 0 | 3 |
| dictionaries: a spread of one, a key `in` found in one | 2 | 2 | 0 | 2 |
| invariance: a writable element or field at a wider one (TypeScript relates them covariantly) | 2 | 2 | 0 | 1 |
| compound and update assignments (x++, \|\|=, ??=, a[i] op=) | 1 | 1 | 0 | 1 |
| an optional key found `undefined` (the key may be absent) | 1 | 1 | 0 | 1 |
| other source forms | 1 | 1 | 0 | 1 |
| type aliases and names the declaration reader cannot resolve | 1 | 0 | 1 | 1 |
| library globals as values (Array, Symbol, Error, Promise, Set, Map, Date, JSON, …) | 1 | 1 | 0 | 1 |
| **total** | **269** | | | |

## Suspected SKJS unsoundnesses

Divergences: SKJS-accepted units the pipeline parses and proposes, and Lean
then refuses (151 units in `search`, `summary.reachedButRefused`). The
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
