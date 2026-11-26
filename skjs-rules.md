# SKJS TypeScript Subset Rules

Normative specification of the TypeScript subset checked by SKJS. Where a rule is stricter than `tsc --strict` for soundness, see also [docs/typescript-soundness-holes.md](docs/typescript-soundness-holes.md).

## Contents

- [Diagnostics: errors vs warnings](#diagnostics-errors-vs-warnings)
- [Conformance Mode](#conformance-mode)
- [Key Rules & Restrictions](#key-rules--restrictions)
  - Scope & bindings: [1. Top-level `let`](#1-no-toplevel-let-declarations) · [1b. Top-level `const` destructuring](#1b-no-destructuring-in-top-level-const-declarations) · [31. Annotated writes & evolving `let`](#31-writes-are-checked-against-an-explicit-annotation-only)
  - Types, literals & operators: [2. Delayed array literals](#2-array-literals-use-delayed-typing) · [8. `keyof`](#8-keyof-operator) · [9. Literal typing & `as const`](#9-literal-typing-and-as-const) · [17. No `any`](#17-the-any-type-is-not-supported) · [18. Template literal strings](#18-template-literal-strings) · [18b. Template literal types](#18b-template-literal-types-partially-supported) · [19. `as` casts](#19-as-casts-are-checked-for-soundness) · [30. Number literals](#30-number-literal-normalization) · [30b. String escapes](#30b-string-literal-escape-decoding) · [30c. Identifier chars](#30c-identifier-characters) · [31. Enums](#31-enums-value-set-semantics) · [33. Circular type params](#33-circular-type-parameter-defaults-and-constraints)
  - Objects, fields & mutability: [27. Readonly field soundness](#27-readonly-field-soundness-stricter-than-typescript) · [28. Optional fields exact](#28-optional-fields-are-exact-present--t) · [28. Index signatures](#28-index-signatures) · [28b. `Closed<T>`](#28b-closedt--closed-object-types-skjs-extension) · [28. Object spread soundness](#28-object-spread-soundness-stricter-than-typescript)
  - Functions & classes: [3. Class inheritance constructors](#3-class-inheritance-constructor-signatures) · [4b. Abstract classes/methods](#4b-abstract-methods-not-supported) · [4c. Static readonly fields](#4c-static-fields-must-be-readonly) · [10. Function overloads](#10-function-overloading-functions-methods-constructors-call-signatures) · [12. Function expressions](#12-function-expressions-not-supported) · [16. Explicit function annotations](#16-function-signatures-must-be-fully-annotated) · [16b. Ambient un-annotated class fields](#16b-un-annotated-class-fields-are-opaque-ambient-classes) · [32. `this` parameter](#32-the-this-parameter--differences-from-typescript) · [35. Nominal classes](#35-class-instance-types-are-nominal-stricter-than-typescript)
  - Narrowing & control flow: [13. Discriminated unions](#13-discriminated-unions) · [20. `for...of`](#20-forof-loop-constraints) · [20b. `switch` & jump edges](#20b-switch-clauses-must-not-fall-through) · [21. Promises & `async`/`await`](#21-promises-and-asyncawait) · [27b. `Array.isArray`](#27b-arrayisarray-narrowing-stays-readonly-unless-provably-mutable-stricter-than-typescript) · [27c. `instanceof` & `Symbol.hasInstance`](#27c-instanceof-narrowing-is-suppressed-for-custom-symbolhasinstance-stricter-than-typescript) · [27d. `typeof === "function"`](#27d-typeof-x--function-narrowing-uses-four-state-callability-stricter-than-typescript) · [27e. Generic `instanceof`](#27e-instanceof-narrowing-binds-hidden-type-arguments-rigidly-stricter-than-typescript) · [27f. `void`/`undefined` equality](#27f-void-and-undefined-overlap-in-equality-narrowing) · [27g. Incomparable function equality](#27g-incomparable-function-signatures-are-not-disjoint-in-equality-narrowing) · [29. Truthiness](#29-truthiness-tests-and-the-truthiness-option) · [36. Assertion signatures](#36-assertion-signatures-asserts-x-and-asserts-x-is-t)
  - Environment & modules: [5. Console surface](#5-console-surface-is-minimal) · [14. Import system](#14-import-system)
- [Coding Guidelines for SKJS](#coding-guidelines-for-skjs)

## Diagnostics: errors vs warnings

SKJS emits diagnostics at two severities:

- **Errors** are soundness-critical (type mismatches, unsupported constructs, unbound names, …). Any error fails the check (exit code `2`).
- **Warnings** are non-fatal, lint-style diagnostics that are not soundness-critical. They are reported, never abort checking of a definition, and exit `0` when no errors exist.

Diagnostics currently reported as warnings:

- **Redundant nullish / destructuring ops**: redundant optional chaining (`Useless '?.'`), redundant non-null assertions (`This operator is useless` when never null/undefined), redundant destructuring defaults (`Default is useless …` / `Element is always undefined`). *(Note: `!` on an operand that is **always** null/undefined stays an **error** — otherwise `x!` would become `never` and satisfy any type unsoundly.)*
- **Redundant boolean negation**: `This constant expression could have been simplified` on `!true` / `!false`.
- **Confusing `void` (`no-confusing-void-expression`)**: `An expression of type 'void' cannot be used here` in `??` / `!` / `===` / `typeof` (runtime-sound and tsc-permissive).
- **Non-thenable `await` (`await-thenable`)**: `'await' can only be applied to a Promise` (`await` passes non-thenables through unchanged at runtime, as tsc types it).
- **`switch` lint checks**:
  - Empty / single-branch switch: `A switch statement must have at least one case` (scrutinee is still checked) and `This switch has a single branch; use an 'if' statement instead`.
  - Unreachable clause: `This case is unreachable: …` / `This 'default' case is unreachable: …`.
  - Misplaced `default`: `The 'default' clause should be the last branch of a switch` (two `default` clauses in one switch stays a hard error, TS1113).
  - Non-exhaustive finite switch with no `default`: `Switch is not exhaustive; the following cases are unhandled` (SKJS does not rely on the warning for narrowing or reachability).
  - Fallthrough clause (TS7029 when `noFallthroughCasesInSwitch` is on): `Fallthrough case in switch; add a 'break'` — the clause fallen into is still fully type-checked (flag gates only the diagnostic, never the typing).
- **Statically-known `in` (`no-unnecessary-condition`)**: `This condition is always true` / `This condition is always false` (a `(false, false)` operand contradiction stays an error).
- **Strict comparison overlap & constant identity**:
  - `This comparison is always true/false because the operand types do not overlap` — only when operand value sets are provably disjoint: primitive kind mismatches (`number === string`), disjoint literals (`0 === 1`), impossible `null`/`undefined` checks (`x === null` when `x` cannot be null), and primitives vs non-boxing objects. Reference types (objects, functions, promises, class instances) are never reported because one value can inhabit both sides (width subtyping, never-returning functions, `Promise<never>`), even where tsc reports TS2367. Number literals are normalized at parse time (rule 30), so `1e3 === 1000` is reported as always true; literals beyond IEEE-754 double precision (>15 significant digits or out of double range) stay silent to avoid false always-false claims.
  - `This comparison is always true/false because the operands always hold the same single value` — when both operands hold the same singleton value (`"a"`, `0`, `true`, `null`, `undefined`). Syntactic literal expressions (including signed numbers like `-1`) are exempt so `else if (color.kind === "blue")` stays quiet, whereas hoisted constants (`x === BLUE`) warn.
- **Template interpolation (`restrict-template-expressions`)**: `Template literal expressions must be of type string, number, bigint, boolean, null, or undefined` (JS coerces via `String()`, tsc accepts it).
- **Loose equality (`eqeqeq`)**: `==` / `!=` warned at parse time; types as `boolean`, narrows nothing (coercion makes strict-style narrowing unsound), and emits no overlap diagnostic.
- **Empty `if` body (`no-empty`)**: `if (c);`.

In tests, warnings are asserted with `// @skjs-expect-warning`; see [docs/testing.md](docs/testing.md).

## Conformance Mode

SKJS-specific option — CLI `--conformance`, tsconfig `"conformance": true` — off by default. It relaxes SKJS-specific restrictions so that TypeScript files can be checked **verbatim, without modifications**, the way the TypeScript conformance suite (`tests/ts-conformance/`) requires:

- `var` declarations are accepted instead of rejected with the `no-var` error (`Unexpected 'var'; use 'let' or 'const' instead`). Inside a function body a `var` is checked **like `let`**: block-scoped and mutable. Hoisting and function scoping are not modeled (tracked in SkipLabs/skjs#841), so code that relies on them is still rejected.
- Top-level `let`/`var` are accepted instead of "toplevel let/var is not supported by SKJS". A top-level `var`/`let` reference reads at its annotation, else its widened initializer type, and top-level assignment to it is checked against that type (a top-level `const` stays read-only, TS2588). Top-level bindings do not narrow on write. Top-level expression statements of any type are also accepted (default mode requires them to be `void`).

Conformance mode deliberately trades some of SKJS's stricter guarantees for tsc compatibility; the default mode remains strict.

## Key Rules & Restrictions

### 1. No Toplevel `let` Declarations
- **Rule**: Cannot use `let` at top level in default mode (accepted in conformance mode — see [Conformance Mode](#conformance-mode)).
- **Error**: `"toplevel let is not supported by SKJS (ignored)"`
- **Workaround**: Use functions, classes, or top-level `const`.

### 1b. No Destructuring in **Top-Level** `const` Declarations
- **Rule**: Destructuring patterns are rejected when the `const` appears at module scope.
- **Error**: `"Top-level const declarations cannot use destructuring in SKJS"`
- **Reason**: SKJS loads top-level constants as literal scalars for predictable initialization; pattern binding would require tracking object/tuple shapes in the loader.
- **Workaround**: Bind the value to a simple `const tmp = ...` at the top level, then destructure inside a function or block (where regular `const` destructuring remains supported).

### 2. Array Literals Use Delayed Typing
- **Rule**: `[...]` literals defer their type (array vs tuple) until used in context.
- **Commits to Array**: when assigned to `Array<T>` / `T[]` / `readonly T[]`, used with `.push()` / `.map()` etc., or indexed with a non-literal number.
- **Commits to Tuple**: when assigned to a tuple type like `[number, string]`, or used only with literal indices.
- **Once committed, cannot change**: using an array-committed literal as a tuple (or vice versa) is an error.
- **Example**: `const nums: number[] = [1, 2, 3];` commits to array; `const pair: [number, string] = [1, "hello"];` commits to tuple.

### 3. Class Inheritance Constructor Signatures
- **Rule**: Child classes may define constructors with different parameter lists than their parent class as long as they call `super(...)` with arguments matching the parent's constructor signature (verified by `tests/expect-error/class_inheritance_test.ts`).

### 4b. Abstract Methods Not Supported
- **Rule**: `abstract class` declarations parse, but the `abstract` modifier on methods and type positions is not yet supported.
- **Error**: `"Method modifier 'abstract' is not yet supported by SKJS"` / `"The 'abstract' type modifier is not yet supported by SKJS"`
- **Workaround**: Use regular classes with interfaces or concrete base classes.

### 4c. Static Fields Must Be Readonly
- **Rule**: Static fields are supported but must have the `readonly` modifier.
- **Restrictions**:
  - Must use `static readonly` together
  - Must be initialized with a value
  - Cannot be marked as optional (`?`)
  - Only primitive types allowed (number, string, boolean, bigint, symbol — no objects)
  - Type annotation can be inferred from literal values
- **Errors**:
  - `static field: number = 42` → `"A static field must be marked 'readonly'"`
  - `static readonly field?: number = 42` → `"A static field cannot be optional"`
  - `static readonly field: number;` → `"This declaration must have an initializer"`
  - `static readonly obj: MyClass = new MyClass();` → `"The type of a top-level constant must be a primitive type, not an object"`
- **Supported**:
  ```typescript
  class Config {
    static readonly API_URL: string = "https://api.example.com";
    static readonly MAX_RETRIES = 3;  // Type inferred as literal 3
    static readonly DEBUG: boolean = true;
  }

  const url = Config.API_URL;  // Access via class name
  ```
- **Rationale**: Static readonly fields have the same restrictions as top-level `const` declarations to ensure predictable initialization and type safety.

### 5. Console Surface Is Minimal
- **Rule**: Only `console.log`, `console.assert`, and `console.error` are provided by `import-stubs/@types/skjs`; other console helpers (e.g., `console.table`) are unavailable.
- **Behavior**: The declared methods follow their TypeScript signatures (`log` and `error` are variadic, `assert` takes a condition plus optional message). `console.assert` only logs — it does not throw — so its condition is checked but proves nothing: no narrowing follows (issue #1042; tsc's lib declares no assertion signature for it either). Use `if (x === null) throw ...` for a checked assertion.
- **Workaround**: Create your own logging wrapper module (e.g., `logger.ts`) that exports the shapes you need, or extend `@types/skjs` locally before running the checker.
- **Verified by**: `examples/src/console_surface.ts` covers supported calls; `tests/expect-error/console.ts` ensures unsupported helpers like `console.table` stay blocked and that `console.assert` does not narrow.

### 8. `keyof` Operator
- **Rule**: `keyof T` is supported on concrete object types, interfaces, classes, tuples, arrays, index signatures, enums (`keyof typeof E`), and primitives.
- **Not yet supported**: `keyof` on an abstract type parameter (e.g., `type Keys<T> = keyof T`) is rejected with `"keyof on an abstract type is not yet supported by SKJS; use a known object or array shape with explicit type parameters"`.
- **Verified by**: `tests/expect-error/keyof.ts`, `tests/expect-error/abstract-type-projection.ts`.

### 9. Literal Typing and `as const`
- **Rule**: SKJS automatically uses precise literal types in some contexts but requires the use of `as const` in others
- **Automatic precise typing contexts**: 
  - **ADT `kind` fields**: `{ kind: "success" }` automatically gets literal type "success"
  - **`const` declarations**: `const x = "hello"` automatically gets literal type "hello"  
  - **Return statements**: `return "success"` gets literal type when function expects it
  - **Switch expressions/cases**: Precise typing applied, enables unused branch detection
  - **Array indexing**: `obj["key"]` uses precise literal type for the index string
  - **Class field initialization**: `status = "ready"` gets literal type in class fields
  - **Array/tuple literal elements**: elements stay literal when the expected type asks for literals — via annotation, parameter, return, nested tuple, or generic constraint (`['urgent']` matches `('urgent' | 'priority')[]`; `[0, 1]` matches `[0, number]`; `[[0, 1]]` satisfies `K extends 0 | 1`); they widen otherwise (`let x = [0, 1]; x.push(2)` makes `x` a `number[]`)
- **Warning for redundant 'as const'**: SKJS warns (but does not error) when `as const` is used unnecessarily
- **Manual 'as const' still needed for**: Non-ADT object properties, nested values, and array elements when nothing in the expected type asks for a literal (see the `save` example below)
- **`as const` on OBJECT/ARRAY literals**: an object literal becomes a deeply-frozen CLOSED object — every field readonly with a literal-pinned type, nested object/array literals frozen recursively, and never string/symbol index signatures stating every unnamed key is provably absent (the `Closed<T>` encoding, see §28b) — so an as-const config is assignable to Json-style readonly-index types. An array literal becomes a readonly tuple with literal-pinned elements. Non-literal values inside (identifiers, calls) type normally; only the field is readonly, matching tsc. Not yet supported under `as const`: spread (the source's hidden keys prevent proving closedness), methods, computed keys.

#### Examples - Automatic Literal Types:
```typescript
// ✓ ADT kind fields - automatic (unlike TypeScript)
type Result<T> = { kind: 'success'; data: T } | { kind: 'error'; message: string };
let result: Result<string> = { kind: 'success', data: 'hello' };  // 'success' is literal

// ✓ Const declarations - automatic  
const status = 'ready';  // gets literal type 'ready'
const count = 42;        // gets literal type 42

// ✓ Return statements - automatic when function expects literal
function getStatus(): 'ready' {
  return 'ready';  // automatically gets literal type
}

// ✓ Switch expressions - automatic precise typing + unreachable branch warning
function handleCode(code: 1 | 2): string {
  switch (code) {
    case 1: return 'first';
    case 2: return 'second';
    case 3: return 'third';  // Warning: "This case is unreachable: ..."
  }
}

// ✓ Array/tuple literal elements - automatic when the expected type asks for literals
const tags: ('urgent' | 'priority')[] = ['urgent', 'priority'];
const pair: [0, number] = [0, 1];

// ✓ 'as const' on object and array literals
function makeFrozen(): void {
  const pair = [0, 1] as const; // readonly [0, 1]
  const cfg = { name: 'app', nested: { debug: true } } as const; // deeply readonly Closed<...>
}
```

#### Examples - Where `as const` is still needed:
```typescript
// Non-ADT object properties need 'as const'
let config = { 
  kind: 'config',        // ✓ automatic literal (special 'kind' field)
  type: 'settings' as const,  // ✗ need 'as const' for non-kind fields
  level: 'high' as const      // ✗ need 'as const' for non-kind fields
};

// Array elements widen when nothing asks for a literal; 'as const' keeps the literal
declare function save<T>(xs: T[]): T;
let s1: 'urgent' = save(['urgent' as const]);  // ✓ T = 'urgent'
let s2: 'urgent' = save(['urgent']);           // ✗ Error: T widened to string
```

### 10. Function Overloading (Functions, Methods, Constructors, Call Signatures)
- **Rule**: Same-named function declarations form one overload set — top-level/`declare` functions, class/interface method declarations (including across merged interface declarations), constructor declarations (the class's `new` signatures), and call/construct signatures in object type literals and interface bodies. Call sites resolve first-match-wins in declaration order, with an arity filter: an overload that cannot accept the argument count (no rest parameter) is skipped. Interface call/construct signatures accumulate like object-literal ones: own declarations first (declaration order across merged declarations), then inherited ones from `extends` bases (derived-first, matching tsc). Call signatures in `class` bodies are still rejected (as in tsc). Assignability of an overloaded source requires every target signature to be matched by some source overload whose arity covers the target's parameters. The implementation signature (the one with a body, required to come last in non-ambient groups) is not callable from outside; hiding it is only done within one file's declaration group, never across files (a cross-file `declare module` augmentation cannot hide the implementation without checking against it).
- **Group rules** (tsc-compatible): duplicate implementations -> TS2393 (TS2392 for constructors); implementation not last or missing in a non-ambient group -> TS2391; overload incompatible with the implementation -> TS2394.
- **Soundness**: the implementation is checked against EVERY overload signature — either its signature is a subtype of the overload, or its body re-checks under the overload's signature (the trial keeps the implementation's own parameter list — names, defaults, `this` — and only swaps the types positionally; inside the trial, branches narrowed to `never` are unreachable and yield `never` without diagnostics). This is stricter than tsc's loose "comparable" rule (a known tsc soundness hole, see docs/typescript-soundness-holes.md): an implementation declared `number | string` under a `(): number` overload is rejected. Consequence: an implementation whose dead branches return types outside a given overload's return type is rejected even when path-insensitively fine — restructure the body so every return conforms per overload.
- **Intersections/unions**: a materialized intersection of overload sets is the concatenation of both sets (tsc's overloaded-intersection meaning; each signature carries the union of all members' call-graph nodes). A union of two differently-shaped overload sets is not callable (tsc TS2349); pairs with different type-parameter counts are skipped rather than merged.
- **`.call`/`.apply`/`.bind`** keep the whole overload set; `.bind` checks the `this` argument against the intersection of every overload's `this`.
- **Test**: [tests/expect-error/overloads.ts](tests/expect-error/overloads.ts), [tests/expect-error/interface-call-signatures-prettier-ignore.ts](tests/expect-error/interface-call-signatures-prettier-ignore.ts), [tests/expect-error/interface-construct-signatures.ts](tests/expect-error/interface-construct-signatures.ts)

### 12. Function Expressions Not Supported
- **Rule**: Anonymous/named `function (...) { ... }` expressions are rejected in expression position; use arrow functions (`(...) => ...`) or top-level `function` declarations instead.
- **Error**: `"Function expressions are not supported; use an arrow function (closure) instead"`

### 13. Discriminated Unions
- **Rule**: Narrowing works on any literal-typed discriminant field (`kind`, `type`, numeric tags, etc.), not only `kind`.
- **Example**: `if (e.type === "click")` or `if (s.kind === "circle")` narrows the union branch; `!==` eliminates it.
- **Verified by**: `tests/expect-error/field-refinement.ts`.

### 14. Import System
- **Rule**: Relative imports must start with `./` or `../`.
- **Extensions**: In `node16`/`nodenext` `moduleResolution` (default), relative imports must end with `.js`, `.mjs`, or `.cjs`. In `bundler` mode, extensions are optional.
- **Side-effect imports**: Module specifiers in side-effect imports (`import './side-effect.js'`, `import 'pkg'`) are always resolved (equivalent to tsc's `--noUncheckedSideEffectImports`), reporting TS2307 when the target cannot be found.
- **Bare imports**: Resolved against `--import-stubs` (`package.json` `types`/`typings` or `index.{d.ts,ts,tsx}`).

### 16. Function Signatures Must Be Fully Annotated
- **Rule**: Every function parameter requires an explicit type annotation — in function/method declarations, arrow callbacks, and function *type* annotations (e.g. `type F = (x) => void`). Named function declarations must also supply an explicit return type; arrow callbacks currently infer their return type but still need annotated parameters.
- **Error**: `TypeCheckFun.sk` emits "A parameter must have an explicit type annotation" for parameters without types and a "must have an explicit return type annotation" error if a named function omits its return type. Function-type annotations parse an omitted parameter type and report the same error from `TEnv.sk` (`normalizeFun`) rather than a `':' expected` parse error, matching tsc's TS7006 (`Parameter 'x' implicitly has an 'any' type`).
- **Workaround**: Declare signatures like `function handler(value: string | number): Result { ... }` and annotate callback parameters, adding `: T` return annotations where needed for clarity.
- **Verified by**: `tests/expect-error/function-args.ts`, `tests/expect-error/anonymous-function-annotations.ts`, `tests/expect-error/function-type-omitted-param-annotation.ts`, `tests/expect-error/function-type-parameter-names.ts`, and `tests/expect-error/missing-return-type.ts`.

### 16b. Un-annotated Class Fields Are Opaque (Ambient Classes)
- **Rule**: Every class field needs an explicit type annotation. A non-ambient class field without one is an error (`Member 'x' must have an explicit type annotation`). An **ambient** class (`declare class`) may omit the annotation — its bodies are never checked — but the field then has an **opaque** type: it is a subtype of nothing but itself and `unknown`, and no concrete value is a subtype of it. So both **reading** such a field into a concrete type and **writing** a concrete value into it are rejected. This is stricter than tsc, which treats the field as implicit `any` and reports the missing annotation (TS7008) at the declaration instead.
- **Soundness**: The field's runtime type is genuinely unknown, so it must not read as `never` — bottom is a subtype of everything, which would let the read flow into *any* type, including `never` (the unsoundness fixed in #775) — nor as `unknown` on the write side, which would accept any write. Two un-annotated fields with the same class and field name share one opaque atom, even across generic instantiations (`C<number>` vs `C<string>`), matching tsc's structural treatment: an un-annotated field cannot reference the class's type parameters, so the instantiations are structurally identical.
- **Verified by**: `tests/expect-error/declared-class-fields.ts`.

### 17. The `any` Type is Not Supported
- **CRITICAL RULE**: NEVER use the `any` type in SKJS code
- **Explanation**: The `any` type is not implemented in the SKJS type checker
- **Error**: Using `any` will cause type checking errors
- **Alternatives**: Use specific types, union types, or generic types instead
- **Example**:
  ```typescript
  // WRONG - will cause errors
  let value: any = "hello";
  
  // CORRECT - use specific types
  let value: string = "hello";
  
  // CORRECT - use union types for multiple possibilities
  let value: string | number = "hello";
  
  // CORRECT - use generics for flexible types
  function process<T>(value: T): T { return value; }
  ```

### 18. Template Literal Strings
- **Rule**: Template literals with backticks and string interpolation are fully supported. Interpolation expressions are parsed inline as first-class expressions (nested templates, strings, and comments inside `${...}` all work), fully typechecked, with diagnostics positioned on the offending expression.
- **Syntax**: Use backticks `` ` `` with `${expression}` for interpolation
- **Features**: 
  - Basic template literals: `` `Hello World` ``
  - String interpolation: `` `Hello ${name}` ``
  - Complex expressions: `` `Result: ${value.toString()}, Sum: ${a + b}` ``
  - Multiline templates with interpolation
  - Escaped `` \` ``, `\$`, and `\${` are literal text, not delimiters
- **Type Safety**: interpolated expressions must be `string`, `number`, `bigint`, `boolean`, `null`, or `undefined` (the `@typescript-eslint/restrict-template-expressions` rule; objects and arrays are rejected even when they have a `toString()`)
- **Escapes are validated**: an invalid escape sequence anywhere in a template (octal `\1`, `\8`/`\9`, malformed `\x`/`\u`) is a syntax error, exactly like quoted strings; a template with no interpolation is decoded, so its literal type equals its runtime value (`` `\x61` `` is the type `"a"`)
- **Line terminators are normalized**, as ECMA-262 requires of a template's value: a raw `<CR><LF>` or lone `<CR>` in the source is the single character `<LF>`, so a template spanning a line break has the same type whether the file is checked out LF or CRLF. `<LS>`/`<PS>` keep themselves, and an *escaped* carriage return (`\r`, `\x0D`) is not a line terminator and stays one
- **Syntax is strict after the expression**: the interpolation must be a single expression followed by `}`. Trailing tokens are rejected with `'}' expected` — `` `${a b}` `` matches tsc; `` `${a, b}` `` is also rejected because skjs has no comma operator (stricter than tsc)
- **Known divergence**: an *interpolated* template *expression* is typed `string`; tsc infers a template-literal type over literal substitutions (`` `a${1}b` `` is `"a1b"` in tsc). Template literal *types* are supported separately — see rule 18b
- **Example**:
  ```typescript
  // ✓ CORRECT - template literals work with complex expressions and multiline
  const message: string = `Hello ${name.toUpperCase()}, Status: ${age >= 18 ? "Adult" : "Minor"}`;
  const multiline: string = `Line 1: ${name}
  Line 2: ${age}`;
  ```

### 18b. Template Literal Types (Partially Supported)
- **Rule**: a template literal type has no type of its own. It **reduces** to a type that already exists in the string domain: either the finite set of strings it can produce (a string literal union) or the `string` primitive itself. Every reduction below is identical to tsc's, not merely assignable to it
- **Reduced** (all supported):
  - **No live hole** → one string literal, cooked exactly as an expression template is (rule 18: escapes decoded, line terminators normalized): `` `abc` `` and `` `a${"b"}c` `` are the type `"abc"`; `` `\x61` `` is `"a"`
  - **Finite holes distribute** into the cross-product: `` `${"a" | "b"}-${"x" | "y"}` `` is `"a-x" | "a-y" | "b-x" | "b-y"`
  - **`boolean`, `null`, `undefined`** fold into their literals: `` `${boolean}` `` is `"false" | "true"`; `` `${null}` `` is `"null"`
  - **`never` absorbs**: `` `x${never}y` `` is `never`, since no string can be built
  - **Bare `string` holes with no text** are `string` itself, not a pattern over it: `` `${string}` `` and `` `${string}${string}` `` are both exactly `string`. `string` absorbs any sibling still a string, so `` `${string | number}` `` is `string` too
  - Number and bigint literal holes stringify with ECMAScript semantics, not source text: `` `${1e21}` `` is `"1e+21"`, `` `${0xff}` `` is `"255"`, `` `${1n}` `` is `"1"`
- **Not supported (error)**: a hole with unboundedly many values, where the result is an infinite but *partial* set of strings. That is a `` `${number}` ``, `` `${bigint}` `` or abstract-type-parameter hole (`` type W<T> = `a${T}b` ``) whatever surrounds it, and a bare `string` hole once the template has text of its own (`` `a${string}b` ``) — the text being exactly what stops it from reducing to `string`. SKJS represents a string type as either the whole primitive or a finite literal set, with nothing in between, so this needs a pattern representation it does not have. Rejecting is sound — it never widens the annotation to `string`, which would silently accept `` const x: `a${string}` = "zzz" ``
- **Number literal holes reduce through the double**: a beyond-precision literal is named by the `String()` form of its double (rule 30), so `` `${9007199254740993}` `` and `` `${0x20000000000001}` `` both reduce to `"9007199254740992"`, and `` `${1e-400}` `` to `"0"`, as in tsc
- An overflowing literal is named `Infinity` (rule 30), so `` `${1e309}` `` reduces to `"Infinity"`, as in tsc
- **Hole constraint**: as in tsc, a hole must be `string`, `number`, `bigint`, `boolean`, `null`, or `undefined`. `object`, `symbol`, `unknown`, `void` and function types are rejected (TS2322, naming the offending type as tsc does). Any type *parses* in a hole — the restriction is a typecheck rule, not a syntactic one. The constraint outranks reducibility both across holes (`` `${object}${number}` `` reports the object) and within one (`` `${number | symbol}` `` reports the symbol)
- **Size limit**: the cross-product is refused past tsc's own union-size limit of 100,000 members, reported as TS2590, and is guarded before it is materialized
- **Not supported**: the case intrinsics (`Uppercase`, `Lowercase`, `Capitalize`, `Uncapitalize`) — they are a separate feature that operates on plain string literal types
- **Example**:
  ```typescript
  // ✓ CORRECT - reduces to a literal union
  type Corner = `${"top" | "bottom"}-${"left" | "right"}`; // "top-left" | ... (4 members)
  type Handler = `on${"Click" | "Hover"}`;                 // "onClick" | "onHover"
  const c: Corner = "top-left";

  // ✗ Error - an infinite, partial set of strings
  // type Hex = `#${string}`;
  // type Px = `${number}px`;
  ```
- **Verified by**: `tests/expect-error/template-literal-types.ts`

### 19. `as` Casts Are Checked for Soundness
- **Rule**: `e as T` is accepted only when the expression's stable source type is a subtype of `T` (sound upcasts; object aliases cannot rely on temporary field refinements).
- **Unsound casts**: Downcasts, sideways casts, and casts from `unknown` report `"This 'as' cast is unsound: the source type is not assignable to the target type"`, then continue checking with type `T` to avoid cascading errors.
- **Verified by**: `tests/expect-error/as-operator.ts`.

### 20. `for...of` Loop Constraints
- **Rule**: Only arrays, tuples, strings, or objects with an explicit string index signature are recognized as iterables. Plain object literals (without `[key: string]: ...`) and custom classes are rejected.
- **Error**: `TypeCheckStmt.getValueType` raises "Invalid iterable type for for-of loop" when the iterable type falls outside those shapes (see `tests/expect-error/for-of-object.ts`).
- **Semantics**: The element type is computed once from the iterable’s structure; there is no special flow refinement beyond the standard loop scopes. For objects with an index signature, the element type is the index value type; for strings it is `string`.
- **Workaround**: When you need to iterate a record-like object, first expose a string index signature (e.g., type `{ [key: string]: number }`) or convert the value to an array via `Object.keys` / `Object.values`.
- **Verified by**: `tests/expect-error/for_in_for_of_tests.ts` (arrays, tuples, strings, index signatures) and `tests/expect-error/for-of-object.ts` (plain objects rejected).

### 20b. Switch Clauses Must Not Fall Through

- **Rule**: A `case`/`default` clause that has statements and can complete normally must exit explicitly (`break` / `return` / `throw` / `continue`) when another clause follows it. This is `noFallthroughCasesInSwitch`, which SKJS turns **on** by default where `tsc` leaves it off, and honours either way — set it to `false` to allow deliberate fallthrough.
- **The option decides the diagnostic, never the typing**: a clause that falls through is still one the next clause is reached from, so the narrowing below applies whether or not the fallthrough is reported. Turning the option off allows the fallthrough; it does not make the clause fallen into assume its label matched.
- **Exempt**: an **empty** clause, which is how several labels are given one body (`case "a": case "b": …`), and the **last** clause, which has nothing to fall into. Falling *through* means running one clause's statements and then the next clause's too — neither of these does that. `noFallthroughCasesInSwitch` exempts both for the same reason. What kind of clause it is does not enter into it: a `default` with statements falls into the clause after it exactly as a `case` does, and is reported the same way.
- **Termination**: an empty clause takes the termination of the clause it falls into, so `case "a": case "b": return 1;` returns on every path. A clause that `break`s leaves the switch instead, so grouping labels in front of it does not make the switch return.
- **Narrowing**: a body is entered both by matching its own label and by falling through the clauses above it, so the scrutinee there is the union, over those entries, of its value on each — the label on a direct entry, and whatever a falling clause left it at on a fallthrough entry. With no reassignment this is just the disjunction of the labels — in `case 1: case 2: <body>` the scrutinee is `1 | 2`, not `2`. But a clause that reassigns the scrutinee carries the *reassigned* value across, not the label it matched: after `case "a": y = c;` falling into `case "b":`, `y` is `"b" | "c"` (the direct-entry "b", or the "c" carried), not `"a" | "b"` — dropping the "c" would be unsound, keeping the "a" over-wide. An empty `default` among the clauses makes the body reachable for any unmatched value, which the union covers through the `default`'s own complement narrowing.
- **Exhaustiveness**: a switch whose cases leave no value of the scrutinee unmatched always runs one of them, exactly as one with a `default` does — so it does not escape to the code after it (`switch (x: 1 | 2) { case 1: return …; case 2: return …; }` returns on every path, with no `default` and no trailing `return`), and it leaves no binding at its pre-switch value. This needs the scrutinee's values to be listable: a `number` or `string` scrutinee, or one case short, still escapes. A `boolean` is listable — `true` and `false` are all it can be — so `case true:` / `case false:` covers it.
- **Writes carry across**: the clause fallen from has also *run*, so a write it made is already in effect in the clause fallen into, which starts from what either entry leaves behind — after `case 1: y = "b";` falling into `case 2:`, `y` is `"a" | "b"` there, the write or whatever the switch was entered with. Only the clause fallen *into* is reached that way: a clause that `break`s does not carry its write into the next, and a later clause reached on its own label does not see it either.
- **Paths out**: after the switch, a binding is the union over the clauses that can actually *reach* the code after it — a clause that `break`s, or the last clause falling off the end — plus, when the switch is not exhaustive, matching no clause. A clause that falls into the next does not exit there (it runs on, its writes carried into the clause it falls into), so it is not a separate path out; nor is one that only returns/throws/continues. This keeps definite assignment precise (`case 1: case 2: y = …; break;` assigns `y` on every exit, so `y` is not "used before assigned" afterwards) and the merged value tight (a value a fall-through clause leaves that the next clause overwrites does not survive). A clause that can `break` *and* return is still a path out via the break.
- **Break edges carry their jump state**: a `break` leaves the switch with the state *at the jump*, which a later write in the same clause can change — so the state after the switch unions each break edge, not each clause's end-of-block scope. `case 1: if (c) break; y = "b"; break;` reaches the code after with `y` either "a" (the guarded break) or "b" (the end), so `y` is `"a" | "b"` there, not "b". Each break records a snapshot against the switch (a `JumpCatcher`) that the post-switch merge folds in (SkipLabs/skjs#910). Loops do the same for both kinds of edge: a `break` joins the state after the loop directly, and a `continue` re-enters the header, whose exit then leaves with the edge's state — in a `for`, continue edges run the increment and break edges skip it. The header's *writes* re-run on that re-entry, so they overwrite the edge's value before the loop can exit through it: in `while ((x = a) !== "a") { if (d) { x = b; continue; } x = a; }` every exit passes the header's `x = a`, so `x` is `"a"` after the loop, not `"a" | "b"` (SkipLabs/skjs#968). The same holds for the loop's entry path — the first header evaluation runs its writes before its test can turn false — while a `break` edge skips the header and keeps the value it jumped with. The header's *test* is checked against the widest values the loop can hold (loop-write widening shows the header every written binding's declared type), so a header like `while (x.go())` rejects when a `continue` edge can leave `x` null, as tsc does. An edge binds to the nearest construct that catches it: `break` to the nearest loop *or* switch, `continue` to the nearest loop, through any switch in between. And because the edge carries the state, an `if` branch that cannot complete normally is **not** merged into the code after the `if` — its state re-joins at the edge's target instead (or never, for return/throw). So a jump guard narrows exactly as a return guard does: after `if (x === undefined) continue;` the rest of the loop body sees `x` without `undefined`, and a write made on a branch that breaks reaches the code after the switch, not the clause fallen into. The edge speaks for every binding, not only the ones it wrote: one it leaves untouched was left at the state above the loop — in particular still *unassigned* if it was, so a `continue` past an assignment does not let the `for`-increment read the binding as assigned (SkipLabs/skjs#969).
- **`default` narrowing**: a `default` runs only for a value no `case` matched, so its body is narrowed to the switched type minus every case label — in `switch (x: 1 | 2 | 3) { case 1: …; case 2: …; default: … }` the scrutinee is `3` there. Every case rules its value out, including any written after the `default` — where the clauses sit says nothing about which values reach it.
- **Error**: "Fallthrough case in switch; add a 'break'" (TS7029), reported on the clause's last statement.
- **Verified by**: `tests/expect-error/switch-empty-cases.ts`, `tests/expect-error/switch-fallthrough-narrowing.ts`, `tests/expect-error/switch-scope-merge.ts`, `tests/expect-error/switch-exit-paths.ts`, `tests/expect-error/switch-scrutinee-reassign.ts`, `tests/expect-error/if-jump-branch-drop.ts`, `tests/expect-error/continue-break-narrowing-soundness.ts`, `tests/expect-error/gap-continue-guard-narrowing.ts`.

### 21. Promises and async/await
- **`Promise<T>` is a plain object type** declared in the builtin stubs with `then`/`catch`/`finally` methods, so promises follow the same structural typing as every other object (`in`, `keyof`, width subtyping, payload covariance all behave normally). The signatures are simplified relative to TypeScript: `then<U>(onfulfilled: (value: T) => U | PromiseLike<U>): Promise<U>` takes exactly one required callback — there is no `onrejected` second argument and the callback is not optional. The stubs also declare `PromiseLike<T>` (the minimal thenable shape, as in lib.es5), and `Promise<T> <: PromiseLike<T>` holds.
- **The `Promise` value** exposes the constructor (`new Promise<T>(executor)`, executor required) and the statics `Promise.resolve`, `Promise.reject`, and `Promise.all` (simplified: `all<T>(values: ReadonlyArray<Promise<T>>): Promise<Array<T>>` — no tuple/mixed-iterable form). Other statics (`race`, `any`, `allSettled`, ...) are not available.
- **`await` is structural**, like tsc: any object whose `then` is shaped like a thenable can be awaited. Applying `await` to a non-thenable is a **warning** (`'await' can only be applied to a Promise`, in the spirit of `@typescript-eslint/await-thenable`); tsc reports nothing and lets non-thenables pass through unchanged, and SKJS types it the same way — checking continues with the operand type. On a union that is only **partly** thenable, checking likewise continues, with the thenable branches unwrapped and the non-thenable parts passed through — again the same result type as tsc.
- **`await` flattens nested thenables recursively**, like tsc's `Awaited<T>`: `await p` with `p: Promise<Promise<T>>` has type `T`. Self-referential thenables (a type referenced in the fulfillment callback of its own `then`, directly or indirectly) never settle and are rejected with **TS1062** like tsc — at async declarations, async returns, async arrow bodies, and `await` expressions; after the error, an `await`'s continuation type is `unknown`.
- **Async `return` is compared by awaited type**, like tsc: `return p` with `p: Promise<T>` is accepted in an async function annotated `Promise<T>` (the returned promise settles to its payload), and an async arrow body settles likewise — `async () => p` has type `() => Promise<T>`.
- **Async return annotations must be the global `Promise<T>` type** (TS1064, like tsc) — an annotation that is merely a structurally well-shaped thenable is rejected.
- **Verified by**: `tests/expect-error/promise-object.ts`, `examples/src/async_method.ts`.

### 28. Optional Fields Are Exact (present ⇒ T)

- **Rule**: `f?: T` means the key **may be absent**; if the key is present, its value is `T` — not `T | undefined`. To allow a present-but-undefined value, add it to the type: `f?: T | undefined`. This is the same contract as index signatures (a present key holds `V`), keeping fields and indexes uniform.
- **Reads**: `v.f` types as `T | undefined` — the `undefined` accounts for absence only.
- **Narrowing**: `"f" in v` confirms presence, so `v.f` narrows to `T`; likewise `v.f !== undefined`.
- **Writes**: `v.f = x` requires `x: T`; writing `undefined` is an error unless `T` includes it.
- **Subtyping**: a source whose `f` can be **present** with a non-`T` value is not assignable to `{ f?: T }`: `{ f: undefined }` (literal), `{ f: T | undefined }`, `{ f?: T | undefined }`, and `{ [k: string]: T | undefined }` are all rejected. Mutable optional fields are invariant in the value type (`{ f?: T }` is not assignable to `{ f?: T | undefined }` — a wider alias could store `undefined` that the narrow view reads as `T`); `readonly` optional fields are covariant as usual.
- **Constructors**: unconditionally assigning an optional parameter to an optional field (`this.f = f` with `f?: T`) makes the field present with a possibly-undefined value and is rejected — declare the field `f?: T | undefined` (note: assigning conditionally does not currently help, as branch-grown fields are dropped at the join). The parameter-property shorthand `constructor(public f?: T)` is fine: its translation declares the field as `f?: T | undefined`, matching the runtime assignment.
- **TypeScript difference**: equals tsc's `--exactOptionalPropertyTypes`, applied unconditionally (default tsc conflates absence with present-undefined). SKJS is stricter than tsc-exact where tsc is unsound (an undefined-bearing *index* source is rejected), and resolves tsc-exact's parameter-property inconsistency the other way: instead of exempting the shorthand from the check, the translated field's type honestly includes `undefined`.
- **Verified by**: `tests/expect-error/optional-fields-exact.ts`, `tests/expect-error/parameter-property-optional.ts`, `tests/expect-error/in.ts`

### 28. Index Signatures
- **Rule**: Index signatures `[key: T]: V` accept key types `string`, `number`, `symbol`, or unions of these. Other key types (boolean, object, never, literal types, generics) are rejected.
- **Key kind coverage**: A `string` index covers number keys (since JS coerces numbers to strings). A `number` index only covers number keys. Multi-kind key types like `string | number` are split into separate per-kind entries; when multiple indexes map to the same kind, their value types are merged (getter: intersection, setter: union).
- **Bracket access**: `obj[key]` returns `valueType | undefined` for matching index signatures. Number keys try the number index first, then fall back to the string index. A **non-literal** key (e.g. `obj[k]` where `k: string`) also unions in the declared field types it could resolve to at runtime — a `string` key any field, a `number` key only numeric-named fields — so `{ a: number; [k: string]: boolean }[k]` is `boolean | number | undefined`. Because SKJS does not enforce TS2411 (see TypeScript difference below), declared fields may be incompatible with the index value type, and this union is what keeps the read sound; for index-compatible fields it is a no-op. Specific literal keys are unaffected (they read the named field, or only the index when no field matches). A **non-literal write** `obj[k] = v` is the mirror image: `v` must satisfy the _intersection_ of the index setter and every reachable declared-field setter, since `k` could name any of them (so `{ a: number; [k: string]: boolean }[k] = v` requires `v` of type `number & boolean`, i.e. is rejected; a `readonly` field the key could name likewise blocks the write). **Symbol keys** follow the same rules: a specific unique symbol is a literal key (it names exactly one declared symbol field, else falls back to the symbol index), while a general `symbol` is non-literal — it resolves through the symbol index and additionally unions (read) / intersects (write) every declared symbol field. With no symbol index, a general symbol is rejected (no index to resolve through), matching TypeScript.
- **Subtyping**: Per-kind index checks. A string-indexed type is assignable to a number-indexed type (string covers number), but not vice versa. A type with only a number index cannot satisfy a string index requirement. A named-field object _type_ with no index of its own is **not** assignable to an index-signature type (its named fields do not "fill in" the index) — see the soundness note below.
- **Union/intersection**: Per-kind. Union: getter = union, setter = intersection. Intersection: getter = intersection, setter = union.
- **Utility type**: Use `StringRecord<V>` instead of `Record<K, V>` for string-indexed record types.
- **TypeScript difference**: SKJS does not validate named field types against index value types at definition time (only during subtyping). SKJS checks index signatures with separate get/set types (like fields), making readonly index types stricter than TypeScript.
- **Soundness rule — named-field type ⊄ index signature (stricter than TS, on purpose)**: A named-field object _type_ with no index of its own is **not** assignable to an index-signature type, even when its field types are compatible with the index value type. Object types are open under width subtyping, so the value may carry extra keys of unrelated types; treating it as indexed would let those be read at the (wrong) index value type. TypeScript allows this assignment and is **unsound** as a result, so SKJS must not follow it. Object-literal _values_ are still accepted (every concrete field is checked against the index value type via a synthetic index); to use a named type as an indexed type, give it an explicit index signature. This fires uniformly for finite-numeric, non-finite-numeric, and non-numeric field names, which is also why `indexForFieldName`'s use of the finite `isJSNumericString` (vs `isJSNumberKeyName`) for `"Infinity"`/`"-Infinity"`/`"NaN"` is unobservable. Documented in `tests/expect-error/index-signatures.ts` "Test 25".
- **Verified by**: `tests/expect-error/index-signatures.ts`, `tests/expect-error/index-signatures-ops.ts`

### 28b. `Closed<T>` — closed object types (SKJS extension)
- **Rule**: `Closed<T>` closes an object type: every key not named in `T` is provably absent. It is encoded as never-valued string and symbol index signatures (indexes are residual — they cover exactly the unnamed keys — so a `never` index states those keys cannot hold any value; number keys fall back to the string index). Since `never` writes are already impossible, a readonly and a mutable never index are the same type; no `readonly` modifier is involved.
- **Name resolution**: the checker reserves `SKJS_Closed` — a 1-ary `SKJS_Closed<...>` application is intercepted before name resolution and means the closed-object operator. User code writes `Closed<T>`, declared in the SKJS stubs (`import-stubs/@types/skjs`) as `type Closed<T> = SKJS_Closed<T>`, so it works with no user declaration. For tsc compatibility, a tsc-only stub declares `type SKJS_Closed<T> = T`, making tsc read `Closed<T>` as the identity. Type lookup consults the built-in stubs first, so `Closed<T>` refers to the stub alias. In value positions, a module's own value bindings and value imports take precedence over built-in stubs.
- **Validation**: `T` must expand to a statically known object type (single object or union of objects — a union distributes, closing each branch) without declared index signatures. Primitives, arrays/tuples, abstract type parameters, and indexed object types are rejected (`Closed<T> requires ...` errors). Closing is deferred/shallow (preserving symbolic nested aliases and anchoring errors at the outermost instantiation site, including through wrapper aliases) and idempotent (`Closed<Closed<T>>` and `Closed<typeof asConst>` succeed without double-wrapping).
- **Consequences**: a `Closed` object type IS assignable to readonly index-signature supertypes (e.g. `type Json = ... | { readonly [k: string]: Json }`), the ergonomic opt-out of the "named-field type ⊄ index signature" soundness rule above; excess properties in literals are rejected; reading or writing an unnamed key is "Property does not exist"; `keyof Closed<T> = keyof T`. Assignability to MUTABLE index supertypes stays rejected (the index's write capability contradicts closedness).
- **Never-index principle (applies beyond `Closed`)**: any index whose value type is `never` (e.g. from intersecting incompatible indexes) contributes no members to access, no keys to `keyof`, and no general-key resolution — reading a provably-valueless key is rejected rather than silently typed `never`/`undefined` (tsc types such reads as silent `never`).
- **Verified by**: `tests/expect-error/closed-type.ts`, `tests/expect-error/closed-type-undeclared.ts`

### 27. Readonly Field Soundness (Stricter than TypeScript)
- **Rule**: A type with a `readonly` field cannot be assigned where a mutable field is expected
- **TypeScript difference**: TypeScript allows this (unsound — a mutable alias can write through a readonly field)
- **SKJS enforcement**: Fields have separate get/set types internally; `readonly` fields have `set = bottom`. The contravariant set-type check rejects `bottom <: T`
- **Examples**:
  ```typescript
  interface ReadonlyPet { readonly name: string; }
  interface MutablePet { name: string; }
  function mutate(p: MutablePet): void { p.name = "changed"; }
  const r: ReadonlyPet = { name: "original" };
  mutate(r); // Error in SKJS, allowed in TypeScript
  ```
- **Intersection**: `{readonly x: T} & {x: T}` makes `x` mutable (set = union(bottom, T) = T)
- **Union**: `{readonly x: T} | {x: U}` makes `x` readonly (set = inter(bottom, U) = bottom)
- **Class inheritance**: A subclass cannot make a mutable parent field readonly; a subclass can make a readonly parent field mutable
- **Verified by**: `tests/expect-error/pr437-set-check-unsound.ts`, `tests/expect-error/readonly-inter-union.ts`, `tests/expect-error/readonly-inheritance.ts`

### 27b. `Array.isArray` Narrowing Stays Readonly Unless Provably Mutable (Stricter than TypeScript)
- **Rule**: `Array.isArray(x)` narrows `x` by intersecting with `ReadonlyArray<unknown>`. A genuinely mutable array stays mutable (`push`/`pop` allowed); a readonly array, a tuple, or a non-array object narrows to a readonly array and cannot be mutated
- **TypeScript difference**: TypeScript's `Array.isArray` guard narrows to `any[]` (mutable), which is unsound — a value typed as a plain object (e.g. `{ readonly length: number }`, or even `{ a: string; b: number }`) can be inhabited at runtime by a readonly array carrying extra properties, so allowing `push`/`pop` would mutate a readonly array
- **SKJS enforcement**: `evalIsArray` intersects with `ReadonlyArray<unknown>`. Intersecting index signatures unions the set types, and `union(T, bottom) = T`, so an already-mutable array keeps its writable index while every other shape gets a readonly one. e.g. `number[] | { readonly length: number }` narrows to `number[] | readonly unknown[]`
- **Examples**:
  ```typescript
  function f(x: number[] | { readonly length: number }): void {
    if (Array.isArray(x)) {
      x.push(1); // Error in SKJS (x could be a readonly array), allowed in TypeScript
    }
  }
  ```
- **Verified by**: `tests/expect-error/isarray-readonly.ts`

### 27c. `instanceof` Narrowing Is Suppressed for Custom `Symbol.hasInstance` (Stricter than TypeScript)
- **Rule**: `x instanceof C` narrows `x` to `C` only when `C` uses the default `instanceof` membership test. If `C` declares a `static [Symbol.hasInstance]` (directly or inherited), narrowing is suppressed and `x` keeps its prior type
- **TypeScript difference**: `static [Symbol.hasInstance]` overrides `instanceof` at runtime — the method decides membership and may return `true` for values that are not `C` (or `false` for values that are). So `x instanceof C` being `true` no longer implies `x` is a `C`, and narrowing to `C` is unsound. tsc narrows anyway (TypeScript is unsound here too — see issue #776)
- **SKJS enforcement**: `rhsDeclaresHasInstance` checks the RHS value's static side (`typeof C`) for a `[Symbol.hasInstance]` symbol field; when present, `evalCond` skips `evalInstanceof`. An *instance-level* `[Symbol.hasInstance]` lives on the prototype, not the constructor, so it does not affect `instanceof` and does not suppress narrowing
- **Examples**:
  ```typescript
  class C {
    a: number = 1;
    static [Symbol.hasInstance](_x: unknown): boolean {
      return true;
    }
  }
  function f(x: unknown): void {
    if (x instanceof C) {
      x.a; // Error in SKJS (x is still unknown), allowed in TypeScript
    }
  }
  ```
- **Verified by**: `tests/expect-error/instanceof-hasinstance.ts`

### 27d. `typeof x === "function"` Narrowing Uses Four-State Callability (Stricter than TypeScript)
- **Rule**: every object-type branch tracks callability and constructibility as present-with-signature / provably-callable-without-signature (the `Function` state) / definitely-absent / unknown. `typeof x === "function"` keeps a branch whose call mode is not definitely-absent — a class-constructor value is `typeof "function"` at runtime even though calling it without `new` still errors (issue #774): its call mode is provably-callable, and construction maintains "construct signature ⟹ call mode at least provably-callable" — and drops only branches provably without [[Call]]: instances of nominal classes (rule 35; an ambient `.d.ts` class is structural, so its instances may be callable), arrays and tuples, object literals and spread results, enum objects. Structural object types (`{}`, `{ a: number }`, interfaces, `object`) survive the "function" branch, because a function carrying the right properties inhabits them (`Object.assign(function () {}, { a: 1 })` is a `{ a: number }`); symmetrically they survive the else of `typeof x === "object"`. A successful "function" test is a proof of [[Call]], so surviving unknown branches strengthen to provably-callable — a nested `typeof === "object"` check then drops them, matching tsc's `{} -> Function -> never` (issue #805) — and in branches proven not `typeof "function"`, unknown strengthens to definitely-not-callable, so a later `typeof x === "object"` else drops them. Symbolic types narrow by intersection in the true branch: a type parameter `T` becomes `T & Function` and `unknown` becomes `Function`, matching tsc; their else branches stay unrefined ("T minus functions" needs a complement type, issue #806)
- **The `Function` type**: declared by the stubs with the `__SKJS_isFunction` brand, which folds into the provably-callable state. Functions, class-constructor values, and construct-signature values are assignable to `Function`; unknown-callability objects, class instances, and arrays are not (nothing launders into the positive brand). A `Function`-typed value is **not invocable** — its signature is unknown — where tsc allows the call at an implicit `any` (unsound); `new f()` is rejected (tsc agrees); it is a valid `instanceof` right-hand side; in conditions it reports the generic truthiness restriction, not the always-true heuristic (TS2774 targets forgotten calls, and a non-invocable value cannot be one — tsc is silent there too)
- **TypeScript difference**: tsc narrows property-bearing object types to `never` in the "function" branch and drops the object arm of `(() => T) | { a: number }` (allowing `x()`); both are unsound — the `Object.assign` value above inhabits the object arm with an unrelated signature, so tsc lets it be called at the wrong type. SKJS keeps such arms; calling `x` after the guard then requires every surviving arm to carry a call signature. A function — or a `Function`-typed value — is also **not assignable to a class-instance type** (even an empty class; tsc accepts) — that inflow rejection is what keeps the precise `never`-narrowing of class instances honest
- **SKJS enforcement**: `Callability` four-state (`CPresent`/`CFunction`/`CAbsent`/`CUnknown`) on `TFields.call`/`.new`; `evalTypeofEquality` narrows per branch on the call mode; `isSubCallability` rejects `CPresent/CFunction <= CAbsent` and `CUnknown/CAbsent <= CFunction` while keeping `CUnknown <= CAbsent` for TS structural compatibility (`{ a: number } -> C`), so `CAbsent` remains a brand-like approximation, like `isArray` in 27b (two-step laundering `Function -> {} -> C` remains, documented)
- **Verified by**: `tests/expect-error/callability.ts`, `tests/expect-error/function-type.ts`

### 27e. `instanceof` Narrowing Binds Hidden Type Arguments Rigidly (Stricter than TypeScript)
- **Rule**: `x instanceof C` for a generic `C` proves only that the runtime object *has* some type arguments — not which. Each hidden argument is bound to a fresh rigid witness (a synthetic type parameter), not to an inference variable. Reads observe the argument's declared bound; writes require the exact hidden type, so no expected type, write, or call-site inference can choose it. A branch of `x` that already satisfies the test keeps its own precise arguments — the witness is only introduced where the argument is genuinely unknown
- **TypeScript difference**: tsc narrows through its `any` escape hatch (`x instanceof Box` gives `Box<any>`, `x instanceof Array` gives `any[]`), so a read at any type and a write of any value are both accepted. SKJS's narrowing is `any`-free, so the unknown argument must be represented rather than erased; the cost is that operations naming the argument in an input position are rejected (issues #772, #791)
- **SKJS enforcement**: `evalInstanceof` mints one witness per class type parameter via `makeSkolemTArgs` and intersects it into each branch that does not already satisfy the test. Witness identity is per type-check, not per source site, so two independently narrowed objects never share one
- **Consequences**: a write below the declared bound is rejected (`x.tag = "a"` for `Tagged<T extends string>`), as is admission at a concrete instantiation (`takesBoxString(x)`), while round trips through the same occurrence are accepted (`cell.put(cell.take())`). The same applies to `instanceof Array`: element writes are rejected, element-independent reads (`x[0]`, `x.length`) are not. Operations whose parameter names the hidden argument are rejected even when they are pure queries — `Map.get`/`Map.has`/`Set.has`/`Array.includes`/`Array.indexOf` — and there is no cast that recovers them, since `x as Map<unknown, unknown>` is itself rejected as unsound. Returning a narrowed value at its top instantiation (`function toArray(x: unknown): unknown[]`) is rejected for the same reason the covariant mutable upcast `Array<number>` → `Array<unknown>` is; annotate the return as `ReadonlyArray<unknown>`, or make the field `readonly`, to accept it
- **Known limitation**: a witness stands for the hidden argument of whichever object each *runtime execution* narrows, but is minted once per type-check. Any channel that lets a witness-typed value outlive one execution — an inferred closure result, a captured container of inferred element type, or a loop body — pools distinct hidden arguments under one identity and admits a cross-object write. Such programs are still accepted today; see `tests/expect-error/instanceof-generic-skolem-args.ts` ("Known holes") and issue #903
- **Example**:
  ```typescript
  class Box<T> {
    v: T;
    constructor(v: T) {
      this.v = v;
    }
  }
  function f(x: unknown): void {
    if (x instanceof Box) {
      const u: unknown = x.v; // OK: reads observe the declared bound
      x.v = "s"; // Error in SKJS (the hidden argument is not known to be string), allowed in TypeScript
    }
  }
  ```
- **Diagnostics**: a hidden argument prints as `C#P` — the class it belongs to and the parameter it stands for, e.g. `Box#T` — rather than the bare `T` the class declared, so a message naming two of them usually distinguishes them by itself (`Box#T` against `Crate#T`, `Pair#A` against `Pair#B`). When two still print alike — two narrowings of the same class, or a shadowed name the program declared — they are numbered `#1`/`#2` in the message that mentions both, ordered by identity so a parameter keeps its number, followed by a line saying the names collide. All of this is display-only: `#` cannot appear in a type reference, and none of it reaches a suggestion offered as code to paste — a "Consider adding explicit type arguments" hint whose `e.g., <...>` example would have to name a hidden argument keeps the advice but drops the example, since the program has no way to write one. `--verbose` prints the qualified ids and none of it
- **Readonly is preserved**: a field or index the scrutinee declared `readonly` stays readonly through the narrowing — the intersection with the class view may restrict what it reads as, but never grants a write the value's type withheld (`x.a = x.b` on a narrowed `{ readonly a; readonly b }`, or `a[0] = a[1]` on a `ReadonlyArray<string>` narrowed by `instanceof Array`, is rejected). tsc narrows to `C<any>` / a mutable `string[]` and accepts it
- **Verified by**: `tests/expect-error/instanceof-generic-skolem-args.ts`, `tests/expect-error/tparam-name-collision.ts`, `tests/expect-error/instanceof-readonly-field.ts`

### 27f. `void` and `undefined` Overlap in Equality Narrowing
- **Rule**: `void`'s only runtime value is `undefined`, so `void` and `undefined` overlap: `void & undefined` is `undefined` (not `never`), and a strict comparison between them is not reported as always-false. In `if (x === y)` with `x: void` and `y: undefined` the true branch narrows `x` to `undefined` — the branch is reachable at runtime, so narrowing to `never` would be unsound (issue #1041). `void` and `null` stay disjoint (`undefined === null` is false at runtime). Like tsc, SKJS accepts `undefined` where `void` is expected (`const v: void = undefined`, `return undefined;` from a void function, `() => undefined` as a `() => void` callback — issue #871); `null` stays rejected under SKJS's strict-null semantics. Only the intersection/overlap treat the two as the same value.
- **Verified by**: `tests/expect-error/void.ts`

### 27g. Incomparable Function Signatures Are Not Disjoint in Equality Narrowing
- **Rule**: two call signatures neither of which subsumes the other can still be inhabited by one function (parameter contravariance: `(x: unknown) => void` is a subtype of both `(s: string) => void` and `(n: number) => void`). So in `if (k === g)` the true branch must not narrow `k` to `never` — the branch is reachable at runtime (issue #768). Refinement keeps the left signature as a sound over-approximation of the shared values. Intersection-type *construction* is unaffected: a materialized `((s: string) => void) & ((n: number) => void)` still collapses to `never`, so an initializer that inhabits only one side is rejected.
- **Verified by**: `tests/expect-error/equality.ts`

### 28. Object Spread Soundness (Stricter than TypeScript)
- **Rule**: In an object literal with spreads, fields defined before a spread are dropped from the result type
- **TypeScript difference**: TypeScript keeps pre-spread fields in the result type, which is unsound — the spread value could overwrite them at runtime (structural subtyping allows extra properties)
- **SKJS enforcement**: When encountering a spread, all previously accumulated fields are cleared. Only the spread's own fields plus fields explicitly set after the last spread appear in the result type
- **Examples**:
  ```typescript
  const obj: {} = { a: 1 };

  // Error: 'a' is before the spread, so it's forgotten
  const bad: { a: string } = { a: "", ...obj };

  // OK: 'a' is after the spread, so it's kept
  const good: { a: string } = { ...obj, a: "" };

  // Only fields from the last spread + trailing fields survive
  function extend(x: { f1: number }): { f0: boolean; f1: number; f2: string } {
    // Error: f0 is before the spread, forgotten from result type
    return { f0: true, ...x, f2: "a" };
  }
  ```
- **Workaround**: Move fields after the spread, or restructure the object literal so that fields you need in the result type appear after the last spread
- **Verified by**: `tests/expect-error/objects.ts`
- **Spreading a union-typed source**: `{ ...x }` where `x: A | B` **distributes** over the union — the result is `(spread A) | (spread B)`, one branch per source member, as in TypeScript (`{ ...x }` is assignable back to the bare union). Because a spread still contributes a `[string]: unknown` / `[symbol]: unknown` index for the source's possible excess properties (a declared type is an open width-subtype), the result stays stricter than TypeScript in three sound ways: a field that must survive a spread lacking it — one written before the spread, or carried across a cross-producted second spread — widens to `unknown`; a Partial-style target that names an optional field a branch lacks (e.g. `{ a?: number; b?: string }`) is rejected, since in that branch the field is covered only by the excess index; and discriminating the result with `in` does not recover the field's type (`'a' in o` leaves `o.a` at `unknown` in the branch that lacks `a` — the source may carry an excess `a` of any type). TypeScript assumes no excess and accepts all three. Verified by `tests/expect-error/spread-union-fields.ts` and `spread-union-distribute.ts`.
- **Branch cap (10,000 deduplicated branches)**: distributing spreads and intersecting unions of objects cross-product their branches; past the cap the two sites behave differently. A **distributed object spread degrades soundly** (construction A, SkipLabs/skjs#1091): the worklist collapses to a single open over-approximation that **keeps the fields present in every source branch** of the overflowing spread (unioning their per-branch types, widened to optional when any branch is optional or a no-op-primitive arm leaves the state unchanged) and folds an index signature common to every branch, while retaining the `[string]/[symbol]: unknown` excess indexes — so fields not common to all branches, and every pre-spread field, still read as `unknown`. The literal still type-checks and SKJS emits a **warning** (SKJS9009). The common fields match TypeScript (which distributes up to ~100,000 constituents and keeps them precisely); only non-common fields may read as `unknown` in SKJS past the cap. An **intersection of unions is still rejected** as too complex (TS2590-style, the definition is abandoned): unlike a spread literal (a covariantly-used produced value), an intersection type flows into contravariant positions where widening it would be unsound, so no sound degradation exists. Verified by `tests/expect-error/spread-union-distribute.ts` (`tooManyUnionSpreads`, `capDegradeDropsCommonSourceField`, `capDegradeFieldMissingInOneBranch`), `spread-union-cap.ts`, and `intersection-branch-cap.ts`. Only a few over-cap cases are pinned per file: each over-cap spread retains ~1 GB of checker memory (the pre-collapse worklist) until the enclosing file's check ends, and the CI runner's memory budget cannot absorb many of them in one test process (#1091).

### 29. Truthiness Tests and the `truthiness` Option
- **Rule**: A value used in a boolean-test position — `if`/`while`/`for` conditions, the ternary `?` condition, unary `!`, and the operands of `&&`/`||` — is checked according to the SKJS-specific `truthiness` mode. The mode only decides which diagnostics are emitted; type-checking always continues with **JavaScript value semantics**, so a rejected condition is still narrowed (its truthy part in the then-branch, falsy part in the else-branch) — errors are recoverable.
- **Modes** (`boolean ⊂ safe ⊂ typescript ⊂ javascript`):
  - **`boolean`**: the condition must be a subtype of `boolean`.
  - **`safe`** (default): also accepts a type with **exactly one falsy value and at least one truthy value** (e.g. `T | undefined`/`T | null` with `T` always truthy, bare `string` (only `""`), bare `bigint` (only `0n`), literal unions like `0 | 1`). Rejects `number` (0/-0/NaN — a common footgun), unions with two or more falsy values (e.g. `string | undefined`), unconstrained generics, always-truthy or always-falsy constant conditions, and any condition whose type contains `void` (e.g. `void | number` — stricter than `tsc`, which rejects only a purely-`void` condition).
  - **`typescript`**: matches `tsc` — accepts everything except a purely-`void` condition (TS1345) and always-truthy function/method references (TS2774). A `void | T` union is accepted (only a whole-`void` condition is rejected). Accepts `number`, always-truthy plain objects, `string | undefined`, `unknown`/generics, class references, etc.
  - **`javascript`**: accepts any type with no truthiness diagnostics.
- **`&&` / `||`**: these are value-returning, matching JavaScript: `a && b` has type `(falsy part of a) | typeof b` and `a || b` has type `(truthy part of a) | typeof b` (for boolean operands the result stays `boolean`). The falsy part is precise where soundness allows, matching `tsc`: full `string` narrows to `""` and full `bigint` to `0n` (so `s && b` is `"" | typeof b`), and a literal union keeps its falsy literals. Exception: full `number` keeps its whole falsy side (its falsy values are `0`, `-0` and `NaN`, and `NaN` has no literal type — `tsc`'s `0` would be unsound), so `n && s` is `number | string` where `tsc` has `0 | string`. Only the left operand is truthiness-tested (and so subject to the mode); the right operand's value flows through unchecked.
- **Setting it**: `"truthiness": "boolean" | "safe" | "typescript" | "javascript"` in tsconfig `compilerOptions`, or `--truthiness <mode>` on the command line (the flag overrides the tsconfig value). Default is `safe`. Note: `truthiness` is SKJS-specific, so running `tsc` on the same tsconfig reports `TS5023: Unknown compiler option`.
- **Relationship to TypeScript**: `tsc` rejects only a purely-`void` condition (TS1345) and always-truthy function/method references (TS2774). `boolean`, `safe`, and `typescript` are never more permissive than `tsc` (they reject at least those). `javascript` *is* more permissive: it accepts any condition, including pure `void` and always-truthy function refs that `tsc` rejects.
- **Verified by**: `tests/projects/truthiness-{boolean,safe,typescript,javascript}/`

### 30. Number Literal Normalization
- **Rule**: Number literals are normalized to their canonical `String(Number(x))` form at parse time, so different spellings of the same value are the same literal type (identity, assignability and hashing all use the canonical name; diagnostics print the canonical value by default, or the spelling the user wrote — e.g. an error about `0xf` prints `0xf`, not `15` — when the SKJS-specific `userLiteralSpelling` option is on, via CLI `--user-literal-spelling` or tsconfig `"userLiteralSpelling": true`): `1.0` = `1`, `0x10` = `16`, `0b10` = `2`, `0o17` = `15`, `1_000` = `1000`, `1e3` = `1000`, `1e+3` = `1000`, `1e-3` = `0.001`, and `-0` = `0`. Bigint literals normalize the same way (`1_000n` = `1000n`, `0x10n` = `16n`, `-0n` = `0n`), exactly at any magnitude. This applies to literal types, object field names, and expression literal types.
- **Matches TypeScript**: tsc keys number literal types by their double value, and so does SKJS: a literal beyond double precision (more than 15 significant digits, a radix literal above 2^53, an exponent outside the double range) is named by the ECMAScript `String()` form of the double it denotes, so `9007199254740993` = `0x20000000000001` = `9007199254740992`, `0.300000000000000044` = `0.30000000000000004`, `1e-400` = `0`, and a value that overflows is named `Infinity` / `-Infinity` (`1e309` = `2e309` = `Infinity`, as tsc prints it) (issue #781). The digits come from Skip's `Float.toString` (Ryu's shortest round-trip form since std 0.5.0, SkipLabs/skip#1288), which always reads back to the same double, so every parsed literal is rewritten.
- **Invalid forms are syntax errors**: malformed numeric literals (`0b12`, `0o8`, `0x`, `1e`, misplaced separators `1__0`/`1_`, legacy octal `010`) are parse errors matching tsc (TS1177/TS1178/TS1125/TS1124/TS6188/TS6189/TS1121).
- **Current caveats**: a literal the runtime cannot parse (250+ characters even after dropping zero padding) keeps its spelled form, so two such spellings stay distinct literal types for assignability (sound, stricter than tsc); equality narrowing and truthiness then assume it may be any value. The always-true/false comparison warnings are suppressed only when such a kept spelling is involved: every other name is the `String()` form of its double, so distinct names are distinct values (as tsc reports, TS2367).
- **Warnings on surprising literals** (stricter than tsc, which stays silent): a number literal that JS reads as a different value than the exact decimal written produces a warning in every literal position (expression, type, property name, enum initializer, template hole) — SKJS2080 overflow to `Infinity`/`-Infinity` (`1e309`), SKJS2081 underflow to `0` (`1e-400`, `2e-324`), SKJS2082 rounding/precision loss (`9007199254740993` is read as `9007199254740992`, `9e-324` as `1e-323`, `0x20000000000001` as `9007199254740992`). Cosmetic respellings of the same value (`1e3`, `0x10`, `1.0`, `1_000`, `-0`) and exactly representable values (`0.1`, `1e21`, `5e-324`) stay silent. Malformed literals remain parse errors.

### 30b. String Literal Escape Decoding
- **Rule**: String literals are decoded to their runtime String Value at parse time, so different spellings of the same value are the same literal type: `"\x61"` = `"\u{61}"` = `"a"`, `"\n"` = `"\x0a"`, `"\0"` = `"\x00"`, `"\a"` (a NonEscapeCharacter) = `"a"`, and a surrogate pair (`"\uD83D\uDE00"`) = the astral code point (`"\u{1f600}"`). A LineContinuation (backslash + line terminator) is elided, so its value is `""` (empty, hence falsy). This applies to literal types, string values, object field names, and module specifiers.
- **Matches TypeScript**: tsc keys string literal types by their decoded String Value, so escaped and plain spellings collapse to one type.
- **Invalid forms are syntax errors**: legacy octal (`"\1"`, `"\0"` followed by a digit) and NonOctalDecimal (`"\8"`, `"\9"`) escapes, truncated `\x`/`\u`, and out-of-range `\u{110000}` are parse errors matching tsc (TS1487/TS1488/TS1125/TS1198).
- **Stricter than TypeScript (soundness-required)**: a lone (unpaired) surrogate escape (`"\uD800"`) is rejected. tsc keeps it as a lone UTF-16 code unit, but a Skip `Char` is a Unicode code point and cannot represent a surrogate, so decoding it is impossible and rejecting is the sound choice. Template literal types are decoded the same way (see rule 18b), so `` `\x61` `` is the type `"a"`.
- **Verified by**: `tests/expect-error/string-literal-escapes-prettier-ignore.ts`, `tests/expect-error/string-literal-line-continuation-prettier-ignore.ts`, `tests/expect-error/string-escape-*-prettier-ignore.ts`

### 30c. Identifier Characters
- **Rule**: an identifier's characters are the Unicode properties **ID_Start** and **ID_Continue** (ECMA-262 sec 12.7), from a table pinned to **Unicode 15.1** — the vintage tsc 6.0.3's scanner uses — so the accepted set matches tsc character for character (verified exhaustively over the whole code space). `café`, `α`, `переменная`, `変数` and CJK Extension I names are ordinary identifiers, property names included
- **ECMAScript's additions**: `$` and `_` may start a name; the joiners `<ZWNJ>`/`<ZWJ>` may continue one
- **Continue-only characters cannot start a name**: a middle dot (`a·b` ✓, `·x` ✗), the joiners, digits, combining marks. Look-alikes that are not identifier characters at all stay invalid: emoji, a math minus (U+2212), U+180E, U+200B
- **A private name needs an IdentifierStart after its `#`**: `#x` and `#a·b` are fine; `#1` and `#·x` are invalid (TS1127), as in tsc
- **An identifier may not immediately follow a numeric literal** (sec 12.9.3): `2z`, `2é`, `1né` are syntax errors (TS1351), not two adjacent tokens
- **Unicode escapes are supported**: an identifier character may be written as `\uXXXX` or `\u{...}`, and the name is the decoded text — `caf\u00e9` and `café` are one symbol. The escape must denote a character valid where it sits (`\u0031` cannot start a name but continues `a\u0031b` = `a1b`)
- **Reserved words may not name bindings or declarations**: a value binding (`const if`, a parameter `if`, destructuring), or a declaration name (function/class/enum/type-alias/type-parameter), in either spelling — `const if` and `const \u0069f` alike — is a syntax error (TS1359). The same word is an ordinary property name (`{ if: 1 }.if`, `enum E { if }`, `class C { static() {} }`). The always-reserved words plus the strict-mode set are covered; TypeScript's contextual keywords (`type`, `async`, `readonly`, …) are not reserved and may name things
- **Known gaps**: `await` is not treated as reserved (it is only inside async code, which is not tracked); and import/export bindings and reference positions do not yet reject reserved words (#938)
- **Verified by**: `tests/expect-error/unicode-identifiers.ts`, `tests/expect-error/identifier-escapes-prettier-ignore.ts`, `tests/Lexer.sk`, `tests/JSIdentifierChars.sk`

### 31. Enums (Value-Set Semantics)

- **Rule**: An enum member's type is its number/string literal type, and the type `E` is the union of its member types (SkipLabs/skjs#762). The value `E` is a frozen object: a readonly field per member plus, when every member value is statically known (and every numeric value is in canonical form), readonly reverse-mapping fields (`E[0]` has the precise member-name literal type; the last member wins for duplicate values, in both expression and type position, matching the runtime object). `const enum` checks like a regular enum. Narrowing (`x === E.A`) and switch exhaustiveness work off the literal machinery, and enum member reads (`case E.A:`, `case E["A"]:`) are valid switch case expressions.
- **Constant initializers** are folded: literals, unary `+`/`-`/`~`, binary arithmetic and bitwise operators (JS int32 semantics) and string concatenation over constants, and references to already-initialized members — bare (`B = A`), qualified (`B = E.A`), element access (`B = E["A"]`), and members of enums provably initialized first (same-file enums declared earlier, or imported ones). Uninitialized members auto-increment from the previous member's value. Arithmetic folds with JS double semantics, as tsc does, and the result is named by its `String()` form (`0.1 + 0.2` is `0.30000000000000004`, `1e308 * 10` is `Infinity`, `1.5 | 0` is `1`). Three cases soundly widen the member to `number`: a NaN result (NaN has no literal type), division by zero (the sign of a zero divisor is not kept in its name), and a power that is not an exact integer within 2^53 (engines compute other powers with an unspecified last-bit rounding; tsc folds them with its own engine's). References that read a not-yet-initialized member — self references, members declared after the referencing initializer (in the same or another enum), and cyclic cross-enum chains — are rejected with tsc's TS2651 in every folded shape; a *bare* forward name (`A = B, B = 1`) instead reports the unresolved name.
- **Computed members**: a non-constant initializer is typed as an expression and must be a number (TS18033); the member's type widens to `number` — which also widens `E` to `number`, reproducing tsc's computed-member opt-out (`5 -> G` accepted, `G.A -> 1` rejected). In a `const enum` they are rejected (TS2474), and in an ambient enum too (TS1066). A non-constant initializer referencing a sibling member by *bare* name reports the unresolved name; qualify it (`E.A`) instead. Reverse-mapping fields are omitted whenever any member value is unknown or non-canonical: such a value could collide with a known key, so no individual reverse entry is trustworthy (tsc types `G[4]` as `string`).
- **Ambient enums**: matching tsc, an uninitialized member of a (non-const) `declare enum` — including enums nested in `declare namespace`/`module`/`global` — is opaque `number`; the declaration's implied auto-increment is not trusted. `declare const enum` members are constant.
- **More permissive than TypeScript (sound)**: cross-enum assignment is accepted when the value sets allow it (`E.A -> F`; tsc rejects nominally, but its wall is one expression deep: `const d: F = E.A as 0` passes tsc), and a matching literal is assignable to a string enum (`"a" -> SE`; tsc is outbound-only for string enums). Reverse lookups get precise member-name literal types where tsc says `string`, and `keyof typeof E` includes the reverse-mapping keys (`0`, `"0"`) that really exist on the runtime object (tsc reports member names only).
- **Stricter than TypeScript (soundness-required)**: `number -> E` is rejected for enums with all-known values — an arbitrary number is not in the enum's value set (tsc deliberately keeps this hole; the classic bit-flags combinations fold, and non-constant ones should be typed as `number`). Out-of-range literals are rejected like tsc 5.0. `E[n]` with a non-literal `number` key is rejected (the enum object has no number index signature). An empty enum has no values (tsc treats it as number-like).
- **Other diagnostics**: duplicate member names (TS2300), a member needing an initializer after a computed or string member (TS1061), unknown member type references `E.C` (TS2694), `new E()` (TS2351), `x instanceof E` (TS2359), assignment to members (rejected via the readonly field's `never` setter, TS2322; tsc reports TS2540). A member whose direct-literal value duplicates an earlier member's numeric value gets a `no-duplicate-enum-values` **warning** (its reverse mapping is shadowed at runtime); member-reference aliases (`B = A`) are exempt. Unreachable switch cases over enums state the true reason (value not in the switched type vs. already handled by an earlier case, e.g. a duplicate-value alias member).
- **Known gaps**: `const enum` values may be used like regular enum objects (`const o = CE`, `CE[0]`); tsc restricts const enums to member access (TS2475) because its default emit inlines them — FIXME if SKJS ever targets inlining emit. String-literal member names (`enum E { "a b" = 1 }`, legal TS) are a parse error (deliberate, PR #293).
- **Verified by**: `tests/expect-error/enums.ts`, `tests/expect-error/enums-string.ts`, `tests/expect-error/enums-computed.ts`

### 31. Writes Are Checked Against an Explicit Annotation Only

An explicit type annotation is a hard constraint: every write to the binding must satisfy the declared type.

```ts
let x: string = "a";
x = 5; // Error: Type is not assignable to the variable's type
```

- A parameter's type is an annotation too, so reassigning a parameter is checked the same way.
- A write *within* the declared type is accepted and still narrows the binding for later reads in the same frame: after `let x: string | number = "a"; x = 5;`, `x` is a `number`.
- A `++`/`--` on a plain variable is a write, checked and narrowed exactly like `x = x + 1`: the binding holds `number` afterwards, not whatever it was narrowed to, so after `let y: number = 0; if (y !== 0) return; y++;` reading `y` as `0` is rejected (SkipLabs/skjs#1017). A `++`/`--` on a member or index target keeps its declared type as before.
- **More permissive than TypeScript (sound)**: without an annotation the inferred type *evolves* on assignment, so `let x = "a"; x = 5;` is accepted and `x` becomes a `number`, where tsc pins `let x = "a"` to `string` and rejects the write. This stays sound because reads see the written type, so any misuse is still caught where the value is read. A bare `let x = null`/`undefined` evolves the same way (TypeScript's evolving `any`).
- A write that escapes the current frame — across a loop iteration, or into a captured enclosing-function local from inside a lambda — is checked against the declared type even when the binding is un-annotated, because the narrowing cannot be trusted there (SkipLabs/skjs#769).
- An **array-destructuring assignment** writes each of its targets the same way, so all of the above applies per target (SkipLabs/skjs#839): `[x] = [5]` behaves exactly like `x = 5`, `[o.f] = [5]` like `o.f = 5`, and a target captured by a lambda is checked like any other captured write. Element types are derived as they are for a destructuring declaration: per index from a tuple (a target past the end reads `undefined`), or the iterator's element type widened with `undefined` from anything else iterable, with the rest target taking the remaining elements. Destructuring a rest allocates a *fresh* array, so nothing aliases it at a fixed arity: it is typed like an array literal and can be read as either a tuple or a growable array, whichever the target asks for (`[x, ...r] = [1, 2, 3]` works for `r: [number, number]` and for `r: number[]`). An **existing** tuple stays un-assignable to an array (`const a: number[] = tup` is rejected, where tsc accepts it unsoundly), because writing through the array view would break the tuple's arity. Object-destructuring assignment (`({ a: x } = e)`) remains unsupported.
- **Verified by**: `tests/expect-error/annotated-write-enforcement.ts`, `tests/expect-error/captured-local-write.ts`, `tests/expect-error/increment-narrowing.ts`

### 32. The `this` Parameter — Differences from TypeScript
SKJS supports the `this` parameter (explicit `this: T`, the implicit class
`this` on every method, and `.call`/`.apply`/`.bind`). Only the places where it
**differs from TypeScript** are documented here — it is soundly stricter in some
cases and conservatively under-approximates a few others.

- **Detached method calls are rejected** (sound; `tsc --strict` accepts them).
  `const g = obj.m; g()` loses the receiver, so the `this` context (`void`) is
  not assignable to the method's `this`.
- **`.call` / `.apply` / `.bind` check the receiver** against an implicit class
  `this` (sound). TS resolves `ThisParameterType` to `unknown` for an implicit
  `this` and accepts any receiver; SKJS requires the class instance, since the
  method body reads the class's fields off the rebound `this`.
- **Generic call signatures** report "Unbound field" for `.call`/`.apply`/`.bind`
  (TS resolves their type parameters to `unknown` through these methods).
- **`.apply` models only required positional parameters**, and partial
  application **`.bind(thisArg, ...args)`** is rejected (a `never[]` rest) rather
  than dropping the bound parameters (`OmitThisParameter`).
- **A no-`this` function type is a free-call permit** (sound; TS erases the
  distinction). A `this`-declaring function or a class method is NOT assignable
  where `() => R` is expected — `const b: () => void = fnBase` then `b()` would
  run the body with no receiver — and neither is passing a method as a no-`this`
  callback or storing one in a property-syntax member (`m: () => R`).
- **Method-syntax members of object-literal types are attach-only.** In
  `{ m(): R }` the member's receiver is the object it is accessed on (rendered
  `(this: <shape>) => R`). Extracting the member for a free call
  (`const f = shape.m; f()`), laundering it through a no-`this` type,
  re-attaching an extracted shape method to another object (`{ m: other.m }`),
  or spreading a shape carrier onto a new object (`{ ...other }`) is rejected,
  and `.call`/`.apply`/`.bind` are not synthesized for it (its carrier type is
  erased). Property-syntax members stay genuinely free functions.
  - A method or `this`-declaring function (class/interface method, explicit
    `this: T`, or boxed primitive method) inhabits a method-syntax shape member
    `{ m(): R }` iff the enclosing carrier branch itself satisfies the method's
    declared receiver (`carrier <: thisParam`; SkipLabs/skjs#1020). This
    restores structural inhabitance for class instances, interfaces, and
    carrier-satisfied object literals while rejecting all `#993` laundering
    patterns (such as `{ m: f }` where the literal does not satisfy `f`'s
    `this`, or re-attaching an extracted shape method to a different carrier).
    Direct primitive-to-object subtyping (`number <: { toFixed(): string }`)
    remains tracked separately by SkipLabs/skjs#982.
- **`this: void` / `this: undefined` is receiver-less.** Such a function is a
  free function: assignable to a no-`this` type, usable as a no-`this` callback,
  and its `.call`/`.apply`/`.bind` accept any receiver (more permissive than TS,
  which restricts the `.call` receiver). To keep that sound, the body may not
  observe `this` — any use is rejected (stricter than TS, which types `this` as
  `void`/`undefined` inside the body).
- **Verified by**: `tests/expect-error/this-parameter*.ts`

### 33. Circular Type-Parameter Defaults and Constraints

A type parameter's default fills the parameter when a reference omits it. A
default that reaches its own alias with too few arguments to break the recursion
(`type A<T = A>`, or through an array/tuple element, a `keyof` operand, a
union/intersection member, or a reference's arguments) denotes nothing.
`type A<T = A<string>>` supplies its argument and stays well-founded.

- **Reported and resolved to `unknown`** (matches tsc, which reports TS2716). A
  value declared at the alias is caught the moment it is used at a concrete type,
  rather than laundered through as the empty type would allow — assigning *into*
  the alias is fine, drawing a value back out is not.
- **A cycle that only closes through a second alias's default is refused** where
  a reference forces the defaults to be filled (`Type instantiation is
  excessively deep and possibly infinite`), reported at the alias the cycle
  reaches back to. tsc reports a circular default at a declaration instead; both
  are sound.
- **A self-referential constraint is refused** — `type C<T extends C<string>>`.
  Satisfying it requires instantiating the alias again, a check SKJS cannot
  discharge, so every instantiation is refused, including the well-typed
  `C<string>`. This is a **sound over-refusal**: tsc accepts `C<string>`.
- **Verified by**: `tests/expect-error/circular-type-param-default.ts`

### 35. Class Instance Types Are Nominal (Stricter than TypeScript)

- **Rule**: a class instance type `C` is inhabited only by values constructed by `C` or a subclass. Object literals, structurally identical sibling classes (including a same-named class from another module), spread and rest copies, values of unknown provenance (`{}`), interface-typed values and `implements C` implementers are **not** assignable to `C`, even when they have every member. Interfaces and object types stay structural: an instance of `C` is still assignable to any interface or object type it matches, and `interface I extends C` inherits `C`'s members but not its identity. Classes declared in `.d.ts` stubs (`Array`, `Map`, `Promise`, …) stay structural, since literals and tuples inhabit them.
- **Intersections**: two unrelated classes share no instance, so `A & B` is `never`; for a class and its subclass, `Base & Sub` is `Sub` (single inheritance). tsc keeps `A & B` for public-only classes.
- **`instanceof`**: `x instanceof C` narrows `x` to `C`, also when `x`'s declared type already had `C`'s members.
- **TypeScript difference**: tsc compares classes structurally (`const p: Pt = { x: 1, y: 2 }` type-checks), apart from `private`/`#private`/`protected` members. Flow makes classes nominal for the same reasons.
- **Why**: SKJS narrowing relies on facts that hold only for real instances: methods live on the prototype, instances are neither callable nor arrays, and `instanceof C` is true for them. Under structural class types each of those facts was a soundness hole (issues #1038, #1062, and the `instanceof`-else entry in docs/typescript-soundness-holes.md).
- **Migration**: describe plain-object shapes with an `interface` or object type; construct instances with `new`.
- **Error**: assigning a non-instance reports `Only an instance of class 'C' (or a subclass) has this type; use 'new' or an interface for structural shapes`.
- **SKJS enforcement**: `TFields.classIds` holds the class identity of an object branch: `None` for structural types, or a `ClassIdentity` (the declaration of a class plus those of its ancestors, never empty by construction; `TEnv::classIdentity`). Subtyping requires the source to be the target's class or a subclass of it; intersection keeps the subclass of two related classes and is empty otherwise; property copies drop it. Identity is not a member, so `keyof`, spread, index signatures and printing are unaffected.
- **Narrowing facts follow identity**: an instance of a nominal class is provably not an array and not callable or constructible, so `Array.isArray(c)` and `typeof c === "function"` narrow it to `never`. An ambient class's instance type is structural, so an array or function carrying its members inhabits it, and those facts are unknown (tsc likewise keeps the branch).
- **Verified by**: `tests/expect-error/class-nominal.ts`, `tests/projects/class-nominal-same-name/`, `tests/projects/class-ambient-claims/`

### 36. Assertion Signatures (`asserts x` and `asserts x is T`)

- **Rule**: Assertion return types (`asserts x`, `asserts x is T`, `asserts this`, `asserts this is T`) are supported on **declared/ambient** functions, interface/class method declarations, object-type call/method signatures, and function type annotations (`(x: unknown) => asserts x is string`). Their runtime return type is `void`.
- **Bodied implementations are rejected (soundness)**: A function or method with a body cannot declare an `asserts` return type (`SKJS9013`), matching how SKJS rejects bodied `x is T` type predicates — SKJS does not verify that a body throws whenever the claimed condition fails. Construct signatures (`new (...) => asserts ...`) and nested positions (`Promise<asserts x is string>`) are likewise rejected (`TS1228`), as are unknown parameter names (`TS1225`) and rest parameters (`TS1229`).
- **Statement-level narrowing**: Calling an assertion function as a top-level expression statement (`assertString(x);`, `assertTruthy(x);`, `assertCondition(typeof x === "string");`, `box.assertReady();`) narrows the asserted local variable for the remainder of the enclosing scope after the call returns normally. Calls whose result is used (`const r = assertString(x)`), optional-chained calls (`box?.assertReady()`), and calls where union branches disagree on the assertion predicate do not narrow. Inside `try { assertString(x); ... } catch { ... }`, the narrowing applies only after the call in `try`, never in `catch`.
- **Soundness guards on narrowing (stricter than TypeScript)**:
  - A captured mutable `let` (a local reassigned inside a nested closure) is **not** narrowed by an assertion call: the callee could invoke a closure that reassigns the outer binding before returning normally, invalidating the asserted value.
  - A local written by a sibling argument in the same call (e.g., `assertFirst(x, (x = 1))`) is **not** narrowed.
  - Calling `.bind(...)` on an `asserts this` method drops the `this` assertion predicate on the bound function.
- **Subtyping (stricter than TypeScript)**:
  - An assertion function is assignable to a plain `(...) => void` function (dropping the assertion predicate).
  - A plain `(...) => void` function is **not** assignable to an assertion function type (tsc unsoundly allows this).
  - Two assertion functions are compatible when they assert on the same subject (`this` or the same positional parameter index) and have compatible kinds: `asserts x` matches `asserts x`, and `asserts x is T1` matches `asserts x is T2` covariantly when `T1 <: T2` (sound because assertions never return normally on failure, so there is no false-branch subtraction).
- **Verified by**: `tests/expect-error/assertion-signatures.ts`

## Coding Guidelines for SKJS

- **Avoid top-level `let`**: Define mutable state inside functions or classes (rule 1).
- **Annotate function signatures & cross-statement bindings**: Parameters and named-function returns need explicit types (rule 16). Without an annotation, inference for `[]`, `new Container()`, and some generic-call results can depend on later use; for a `const`, an annotation or explicit type arguments make it order-independent. Prefer `const` — an un-annotated `let`'s type evolves on assignment (rule 31).
- **Declare the widest type a value will ever need at its creation site**: Mutable element and field types are invariant (soundness, rule 27); on read-only parameters, use `readonly` fields/arrays so narrower arguments are accepted.
- **Never use `any`**: Use specific types, unions, `unknown`, or generics (rule 17).
- **Static fields must be `static readonly`** with primitive initializers (rule 4c).
- **Prefer small, focused files**: Smaller files maximize incremental checking precision (`--data`) and keep diagnostics localized. See `examples/src/` for working programs following these rules.
