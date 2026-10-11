# SKJS coverage by the OCaml pipeline

How much of what SKJS accepts in its own test suite the pipeline
(`verify-source.mts`: parser → OCaml producer → Lean search and check) verifies, what
stops the rest, and where the two disagree because SKJS is wrong.

Measurement checkpoint: October 11, 2026 (full verifier-only run, using the
SKJS acceptance results recorded on October 9; SKJS was not rerun).
The reviewed nested-promise search failure is classified by its unit and
exact obligation.

**2,474 of 2,674 SKJS-accepted units verify (92.5%); 1,844 of 2,026
accepted functions (91.0%).** 296 of the 377 files with an accepted unit
verify entirely. There are 88 principled refusals, 10 registered SKJS-unsound
units, 102 gaps (2 of them under reasons no class entry matches,
`summary.unmatchedReasons`) and no unexplained refusals.

`mapArr` and `testMapCallback` fail at the native call: an arbitrary
one-argument callback supplies no contract for the three actuals `map` passes.
There is also an independent density problem: `mapArr<T, U>(arr: T[], f: (x: T) => U): U[]`
promises readable U[] for every U and an arbitrary callback. That contract is
false, for example when U is number.
Calling the unchanged function with `xs = [1, 2, 3]` and a callback that sets
`xs.length = 0` produces length 3 with only index 0 present. Neither custom
species nor external code is involved. Strengthening its callback parameter
would change its written contract and cannot silently repair it.
`testMapCallback` itself makes a safe call, but its extracted unit also checks
that invalid general declaration. The current classifier still includes these
rows among gaps; that classification is not a completeness claim.

The SKJS-unsound list records independent runtime witnesses ([below](#suspected-skjs-unsoundnesses)).
Membership alone does not show that the pipeline reached the corresponding
obligation: an earlier refusal can mask it. Verified, gated and rejected outcomes
remain separate in the JSON; aggregate “done” totals are not a closure criterion.

[skjs-coverage.mts](skjs-coverage.mts) measures coverage. Rerun:

```sh
node verification/pipeline/skjs-coverage.mts --skjs --width 3   # about 220 s
```

An explicitly requested `--skjs` run aborts if checker confirmation cannot run;
it never falls back to markers or publishes an unconfirmed coverage result.

It writes [skjs-coverage.json](skjs-coverage.json) (summary, one row per unit,
one line per row, so a rerun's movement is a line diff). `--skjs` runs SKJS in
Docker from the main checkout (`SKJS_ROOT`, `SKJS_BIN`, `DOCKER_IMAGE`,
`SKIP_DIR` override); without it the expectation markers alone decide.
`--only <substring>` narrows the corpus, `--keep` keeps check artifacts,
`--out` places the derived files (default `$TMPDIR/skjs-coverage`). The script
is not part of `verification/test-all.sh`.

## Method

**Corpus.** Every TypeScript file the SKJS harness type-checks with a verdict:

| Suite | Harness verdict | Files | Units | Accepted | Verified | Accepted functions | Verified functions |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `tests/expect-error` | `@ts-expect-error` / `@skjs-expect-error` name the next non-annotation line (`tests/Helpers.sk` `findExpectErrors`); `@skjs-expect-warning` is not an error | 399 (374 with units) | 3,883 | 2,458 | 2,260 | 1,863 | 1,683 |
| `tests/callgraph` | no error allowed | 25 | 59 | 59 | 57 | 51 | 49 |
| `tests/constprop` | no error allowed | 14 | 66 | 66 | 66 | 49 | 49 |
| `tests/deadcode` | no error allowed | 7 | 27 | 27 | 27 | 16 | 16 |
| `tests/cfg` | no error allowed | 7 | 22 | 22 | 22 | 21 | 21 |
| `tests/projects` | expect-error markers, under the project's tsconfig | 24 of 68 | 44 | 34 | 34 | 23 | 23 |
| `tests/ts-conformance/cases` | lines listed in `reference/*.errors.txt` | 4 | 9 | 8 | 8 | 3 | 3 |
| **total** | | **480** | **4,110** | **2,674** | **2,474** | **2,026** | **1,844** |

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

**SKJS confirmation (October 9).** SKJS (`check --import-stubs import-stubs`, default
truthiness, as the harness runs it) is run once over all 2,676 derived files of
marker-accepted units. It rejects 2: two `*-prettier-ignore.ts` files whose
expected *parse* errors the markers attribute to the wrong statement. They are
not counted. The remaining 2,674 are the accepted corpus.

**Environment.** SKJS checks a test in the environment its stubs give
(`--import-stubs import-stubs`); the pipeline gives each derived file the
same one, a project of its own extending
[`skjs-environment/tsconfig.json`](skjs-environment/tsconfig.json): a bare
import specifier resolves in `import-stubs`, and
[`skjs-environment.d.ts`](skjs-environment/skjs-environment.d.ts) restates the builtins
stub's globals TypeScript's library lacks (`__SKJS_show`, `process`,
`StringRecord<V>`, and `Closed<T>` read as `T`). These declarations are
assumptions of the result, as an import's are
([trust surface](../DESIGN.md#trust-surface)).

**Pipeline.** Each derived file goes through `checkApart` (exactly
`node verify-source.mts <file> --project <its project>`), 6 at a time, with
`verify-source.mts`'s 30 s step timeout.
A unit whose run ends in an infrastructure error (a step timeout, the
TypeScript service's "context canceled" under load — seen once) is run again
alone; no timeout remained. Outcome rows: `verified`, or the first blocker with its phase
(`source` = parser gate, `proposal` = producer `unsupported:`, `search` =
Lean found no derivation or refused a source form, `error`), its normalized
reason, its feature group, and where it lies: in the unit's own statement
(`self`), in a statement its closure brought (`dependency`), or `unknown`.

**Attribution.** A verified run counts for a unit only when it checked the
unit's own code: a function unit is among the functions `verify-source.mts` reports
verified, and any other unit (a class, a variable statement, top-level code)
contains a statement of the module initialization it reports checked
(`initialization`, the spans of the initialization unit Lean checked). A
verified run that checked neither would be the row `unverified`,
"attribution: the verified run checked none of this unit's own code"; none
is.

| Phase of first blocker | Units |
| --- | ---: |
| verified | 2,474 |
| source (gate) | 76 |
| proposal (producer) | 25 |
| search (Lean) | 99 |

**Refusal classes.** The project's goal is that every accepted unit either
verifies or is refused for a specific, principled reason. Each accepted unit
that does not verify is put in one class, by its first blocker's key
(`class` on its row, `summary.byClass`), through the table `CLASSES` in
[skjs-coverage.mts](skjs-coverage.mts), one entry per reason with its
justification; the first entry matching the key and any unit and diagnostic
guards decides. A reviewed search failure has both guards, so a changed
obligation is classified independently of the previous explanation:

- **principled** (P): the pipeline refuses because the construct is unsound,
  not faithful to JavaScript, or rejected by TypeScript itself, or because
  its soundness would need an assumption the project declines; nothing else.
  Each such entry is a row of the fragment boundary's
  [refused on principle](../SOURCE-FRAGMENT.md#refused-on-principle): TypeScript's
  implicit index signature, covariant writable storage, method extraction,
  `instanceof` narrowing `unknown` (an object gets a class's prototype without
  its constructor), a constructor or base class from outside the file, an
  iterator whose type states no `return`, thenable adoption, a contextual
  `any`, an empty intersection, a rest typed by an intersection, and code or declarations TypeScript rejects.
- **gap** (G): a sound construct the pipeline does not yet support: a
  [next step](../WORK.md#next-steps), or a [model limit](../SOURCE-FRAGMENT.md#model-limits)
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

For an accepted unit $`u`$, let $`r_i(u)`$ mean that entry $`i`$ matches
its first blocker key and any unit and diagnostic guards, and $`c_i`$ be
that entry's class:

```math
\mathrm{class}(u)=
\begin{cases}
\mathsf{verified} & \text{if } u \text{ verifies}\\
\mathsf{S} & \text{else if } u \in \texttt{SKJS\_UNSOUND}\\
\mathsf{U} & \text{else if } u \text{ ended in an error}\\
c_i & \text{else if } i=\min\{\, j \mid r_j(u) \,\}\\
\mathsf{G} & \text{otherwise}
\end{cases}
```

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
- Twelve producer refusals have no location (`where: "unknown"`).

## Refusals by class

Every accepted unit that does not verify, by the class and reason its first
blocker's key is given (`summary.byReason` and `summary.byClass` of
[skjs-coverage.json](skjs-coverage.json); definitions in the method,
"Refusal classes"). P principled, S SKJS unsound, G gap, U unexplained.

| Class | Units |
| --- | ---: |
| verified | 2,474 |
| principled (P) | 88 |
| SKJS unsound (S) | 10 |
| gap (G) | 102 |
| unexplained (U) | 0 |
| **accepted** | **2,674** |

Reason definitions and justifications live in `CLASSES` in
[skjs-coverage.mts](skjs-coverage.mts); measured counts live in
`summary.byReason` of [skjs-coverage.json](skjs-coverage.json).
This avoids maintaining another copy of the classifier here.

## Groups

First blocker, not every missing feature of a unit:

| Group | Units | Self | Dependency | Files |
| --- | ---: | ---: | ---: | ---: |
| TypeScript refuses the code too (the pipeline follows TypeScript's types) | 38 | 30 | 8 | 24 |
| destructuring and rest/default parameters | 14 | 9 | 5 | 5 |
| in / instanceof / typeof tests | 14 | 7 | 0 | 6 |
| implicit index signatures: a record at an index signature (`Closed<T>` read as `T` among them) | 14 | 14 | 0 | 3 |
| type forms: literal types, keyof, indexed access, mapped, object, index signatures, intersections, method signatures | 11 | 10 | 1 | 7 |
| object growth: a key-adding write on an object another reference may hold, a dynamic index write | 11 | 11 | 0 | 5 |
| generics: constraints, explicit type arguments, rigid types, generic function types | 10 | 8 | 1 | 7 |
| calls: overloads, .call, spread arguments, Object.assign, arrow callee | 10 | 7 | 3 | 6 |
| a named function at a signature binding more parameters, or indifferent to the receiver it requires (its type is its annotated signature) | 9 | 8 | 1 | 5 |
| arrays and open records: `Array.isArray` on `unknown`, `length` of an array read as a record's | 8 | 8 | 0 | 5 |
| cells read at their contract (contents known only as primitives or as no `undefined`, and forgotten across a step that may write them) | 6 | 4 | 0 | 4 |
| classes: modifiers, inheritance, fields, parameter properties, receivers | 6 | 3 | 3 | 3 |
| enums | 6 | 0 | 6 | 1 |
| tests on a value of a type parameter or `unknown` (no rule narrows a parameter row to its meet `T & number`; no object identity) | 6 | 6 | 0 | 3 |
| sloppy (non-strict) code | 6 | 4 | 2 | 3 |
| object literal members (methods, accessors, spreads) | 5 | 4 | 0 | 4 |
| iterables the program defines: an iterator whose type states no `return`, a spread or a pattern the protocol's lowering does not place, a well-known symbol key other than `Symbol.iterator` | 5 | 4 | 1 | 4 |
| await of non-promises and unions (the await bound) | 5 | 5 | 0 | 3 |
| relational operators (< <= > >=) and ** | 2 | 1 | 1 | 1 |
| search: no derivation found (evidence search failed) | 2 | 2 | 0 | 2 |
| reads on unions/primitives (field/index read on non-object, string keys) | 2 | 1 | 0 | 2 |
| dictionaries: a spread of one, a key `in` found in one | 2 | 2 | 0 | 2 |
| invariance: a writable element or field at a wider one (TypeScript relates them covariantly) | 2 | 2 | 0 | 1 |
| compound and update assignments (x++, \|\|=, ??=, a[i] op=) | 1 | 1 | 0 | 1 |
| an optional key found `undefined` (the key may be absent) | 1 | 1 | 0 | 1 |
| other source forms | 1 | 1 | 0 | 1 |
| type aliases and names the declaration reader cannot resolve | 1 | 0 | 1 | 1 |
| library globals as values (Array, Symbol, Error, Promise, Set, Map, Date, JSON, …) | 1 | 1 | 0 | 1 |
| unclassified: search: reject: unsupported source expression at _: strict equality of two operands that may both be values of no known kind, neither a primitive nor an object | 1 | 1 | 0 | 1 |
| **total** | **200** | | | |

## Performance on the pipeline cases

Measured September 29, 2026 over the 791 cases of [cases.mts](cases.mts),
on a machine shared with other jobs (load average 12 to 58 during the runs).

**Evidence and check time.** 311 cases reach the check step. For each, the
bytes of its `evidence.json`, and the wall-clock time of the check step
(`verifier --check-source-claims`, decoding and checking, one process run
alone, best of three, process start included):

| | min | median | p90 | p99 | max |
| --- | ---: | ---: | ---: | ---: | ---: |
| `evidence.json` (bytes) | 1,950 | 43,516 | 183,842 | 445,036 | 1,190,824 |
| check step (ms) | 23 | 32 | 73 | 285 | 519 |

The largest evidence is `sum-values-tuple`'s (1.19 MB, 519 ms), then
`for-of-program-iterable`'s (1.00 MB, 147 ms); the evidence of all 311 cases
totals 24.7 MB. Check time does not follow size: `sum-tuple-value` checks
2,436 bytes in 357 ms.

**Subtyping work** ([RECURSIVE-EQUATIONS §4](../RECURSIVE-EQUATIONS.md#4-subtyping)),
measured over all cases by [`tools/subtyping-trace.mts`](../tools/subtyping-trace.mts). Scope: the
questions are those the check step asks (the checker's `subset` premise
judgments and `core` family tables); the variance components and fallback
searches are counted in both verifier runs. The producer's proof search
(`CertificateProducer`) writes no line besides its fallback searches: its
strategies, where a coercion no strategy derives costs most (DESIGN row P),
are not measured.

- 169 questions (146 `subset`, 23 `core`), 28 of them holding. Work (`Inst`
  steps tried + 1) over size (source + target): median 0.33, p90 0.50, p99
  5.4, max 8.2.
- 164 questions take at most twice their size. Five take 19 to 48 `Inst`
  steps on types of total size 5 to 8 (`library-promise-statics`, a `core`
  table of sizes 3+3 with 48 steps, all by `Var`; four `subset` questions
  with 19, 25, 25 and 42 steps). Each of the five computes variances while it
  is answered, over components of 8 to 36 members. The largest types
  compared (size 39) take 1 step.
- `Var`: 177 steps, maximum nesting depth 5.
- Variance components: 206 computed, 1,813 members, at most 4 polarity
  rounds, 685 member checks, none weakened to invariant.
- Fallback searches: 4,009, 20 proved, none refused at growth or at the
  limit; at most 11 rows and 12 candidate pairs visited.

## Suspected SKJS unsoundnesses

Divergences: SKJS-accepted units the pipeline parses and proposes, and Lean
then refuses (100 units in `search`, `summary.reachedButRefused`). The
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
([SOURCE-MODEL](../SOURCE-MODEL.md#async-and-iteration)) and refuses the unit.
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
