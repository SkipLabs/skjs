# SKJS TypeScript Subset Rules

This document describes the rules and restrictions of the SKJS type checker, which implements a sound subset of TypeScript.

## Diagnostics: errors vs warnings

SKJS emits diagnostics at two severities:

- **Errors** are soundness-critical (type mismatches, unsupported constructs, unbound names, …). A file with any error fails the build (exit code `2`).
- **Warnings** are non-fatal, lint-style diagnostics that are not soundness-critical. They are reported but do **not** fail the build — a file whose only diagnostics are warnings exits `0`. They also never abort checking of a definition, so they don't hide later errors.

Diagnostics currently reported as warnings: redundant optional chaining (`Useless '?.'`) and redundant non-null assertions (`This operator is useless` on an operand that is never null/undefined), redundant destructuring defaults (`Default is useless …` / `Element is always undefined`), useless/unused `switch` constructs (`Useless switch` / `Unused branch`), and non-overlapping strict comparisons (`This comparison is always true/false because the operand types do not overlap`, only when the operands' value sets are provably disjoint: primitive kind mismatches like `number === string`, disjoint literal sets like `0 === 1`, comparisons against `null` or `undefined` that the other operand can never hold (`x === null` when `x` cannot be null is dead code — reported even though tsc is silent), and primitives against object types they cannot box into. Reference types — objects, functions, promises, class instances — are never reported, because a single value can inhabit both sides (width subtyping, never-returning functions, `Promise<never>`), even where tsc reports TS2367. One divergence in the other direction: SKJS compares numeric literal types textually, so `1e3 === 1000` is reported even though tsc knows the values are equal). SKJS additionally warns when both operands of a strict comparison can only hold one identical value (`This comparison is always true/false because the operands always hold the same single value`, e.g. `x === y` with both typed `"a"`, `0`, `true`, `null`, or `undefined`) — tsc reports nothing there. Comparisons where either operand is a literal expression (including signed numbers like `-1`) are exempt: re-checking a narrowed discriminant on the last variant of a union (`else if (color.kind === "blue")`) is idiomatic, not a bug. The exemption is syntactic, so re-checking against a hoisted constant (`x === BLUE`) still warns. A non-null assertion (`!`) whose operand is *always* null or undefined stays an **error**: `x!` would then have the empty type and satisfy any annotation, so accepting it would be unsound. Parser-level lint rules (e.g. `==`/`!=`, empty `if`) are still reported as errors.

In tests, warnings are asserted with `// @skjs-expect-warning`; see [docs/testing.md](docs/testing.md).

## Key Restrictions Discovered

### 1. No Toplevel `let` Declarations
- **Rule**: Cannot use `let` at the top level of files
- **Error**: "toplevel let is not supported by SKJS"
- **Workaround**: Use function declarations or class methods instead

### 1b. No Destructuring in **Top-Level** `const` Declarations
- **Rule**: Destructuring patterns are rejected when the `const` appears at module scope.
- **Error**: "Top-level const declarations cannot use destructuring in SKJS"
- **Reason**: SKJS loads top-level constants as literal scalars for predictable initialization; pattern binding would require tracking object/tuple shapes in the loader.
- **Workaround**: Bind the value to a simple `const tmp = ...` at the top level, then destructure inside a function or block (where regular `const` destructuring remains supported).

### 2. Array Literals Use Delayed Typing
- **Rule**: `[...]` literals defer their type (array vs tuple) until used in context
- **Commits to Array**: when assigned to `Array<T>` / `T[]` / `readonly T[]`, used with `.push()` / `.map()` etc., or indexed with a non-literal number
- **Commits to Tuple**: when assigned to a tuple type like `[number, string]`, or used only with literal indices
- **Once committed, cannot change**: using an array-committed literal as a tuple (or vice versa) is an error
- **Example**: `const nums: number[] = [1, 2, 3];` commits to array; `const pair: [number, string] = [1, "hello"];` commits to tuple

### 3. Class Inheritance Constructor Signatures
- **Rule**: Child class constructors must have same signature as parent
- **Error**: "Invalid extends" when constructor signatures differ
- **Requirement**: `constructor(a: T, b: U)` in parent requires same in child
- **Workaround**: Design inheritance hierarchies with consistent constructor patterns

#### 4b. Abstract Classes Not Supported
- **Rule**: Abstract classes and abstract method modifiers are not implemented
- **Error**: "Method modifier 'abstract' is not yet supported by SKJS"
- **Workaround**: Use regular classes with interfaces, or avoid abstract patterns

#### 4c. Static Fields Must Be Readonly
- **Rule**: Static fields are supported but must have the `readonly` modifier
- **Restrictions**:
  - Must use `static readonly` together
  - Must be initialized with a value
  - Cannot be marked as optional (`?`)
  - Only primitive types allowed (number, string, boolean, bigint, symbol - no objects)
  - Type annotation can be inferred from literal values
- **Errors**:
  - `static field: number = 42` → "A static field must be marked 'readonly'"
  - `static readonly field?: number = 42` → "A static field cannot be optional"
  - `static readonly field: number;` → "This declaration must have an initializer"
  - `static readonly obj: MyClass = new MyClass();` → "The type of a top-level constant must be a primitive type, not an object"
- **Supported**:
  ```typescript
  class Config {
    static readonly API_URL: string = "https://api.example.com";
    static readonly MAX_RETRIES = 3;  // Type inferred as literal 3
    static readonly DEBUG: boolean = true;
  }

  const url = Config.API_URL;  // Access via class name
  ```
- **Rationale**: Static readonly fields have the same restrictions as top-level `const` declarations to ensure predictable initialization and type safety

### 5. Console Surface Is Minimal
- **Rule**: Only `console.log`, `console.assert`, and `console.error` are provided by `import-stubs/@types/skjs`; other console helpers (e.g., `console.table`) are unavailable.
- **Behavior**: The declared methods follow their TypeScript signatures (`log` and `error` are variadic, `assert` takes a condition plus optional message).
- **Workaround**: Create your own logging wrapper module (e.g., `logger.ts`) that exports the shapes you need, or extend `@types/skjs` locally before running the checker.
- **Verified by**: `examples/src/console_surface.ts` covers supported calls; `tests/expect-error/console.ts` ensures unsupported helpers like `console.table` stay blocked.

### 6. Undefined Method Access
- **Rule**: Cannot call methods on potentially undefined values
- **Error**: "Invalid '.'" when accessing methods on `T | undefined`
- **Workaround**: Explicit undefined checks required

### 7. Generic Classes Work Properly ✅
- **Rule**: Generic classes with type parameters work correctly
- **Status**: Fixed - `new Array<T>()` assignment works in generic class constructors
- **Example**: `class Stack<T> { items: Array<T>; constructor() { this.items = new Array<T>(); } }`

### 8. Keyof Operator Not Implemented
- **Rule**: The `keyof` operator is not supported
- **Error**: "Invariant violation: TODO keyof"
- **Workaround**: Use explicit property access or type-specific functions

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
- **Error for redundant 'as const'**: SKJS errors when `as const` is used unnecessarily
- **Manual 'as const' still needed for**: Non-ADT object properties, nested values

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

// ✓ Switch expressions - automatic precise typing + unused branch detection
function handleCode(code: 1 | 2): string {
  switch (code) {
    case 1: return 'first';
    case 2: return 'second';
    case 3: return 'third';  // Error: "Unused branch" 
  }
}

// ✓ Array/tuple literal elements - automatic when the expected type asks for literals
const tags: ('urgent' | 'priority')[] = ['urgent', 'priority'];
const pair: [0, number] = [0, 1];
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

### 10. Function Overloading Not Supported
- **Rule**: Function overloading is not supported in SKJS
- **Workaround**: Use different function names or union types with type guards

### 11. Generic Type Method Calls
- **Rule**: Cannot call methods like `.toString()` on unconstrained generic types
- **Error**: "Invalid '.' for type: T extends"
- **Workaround**: Use type constraints or avoid calling methods on raw generic types

### 12. Nested Function Declarations Not Supported
- **Rule**: Cannot declare functions inside other functions
- **Error**: "Function expressions are not supported; use an arrow function (closure) instead"
- **Workaround**: Declare all functions at module level

### 13. Algebraic Data Types with 'kind' Field ✅
- **Rule**: ADTs must use `kind` field for discriminated unions
- **Syntax**: `type Foo = { kind: 'variant1', ... } | { kind: 'variant2', ... }`
- **Pattern Matching**: Use `if (value.kind === 'variant1')` for type narrowing
- **Special**: Only `kind` field enables ADT pattern matching, other field names won't work

### 14. Import System ✅
- **Rule**: Relative imports must start with `./` or `../`.
- **Extensions**: In `node16`/`nodenext` moduleResolution (default), imports must end with `.js`, `.mjs`, or `.cjs`. In `bundler` mode, extensions are optional.
- **Syntax**: `import { functionName, TypeName } from './filename.js'`
- **Example**: `import { add, User } from './utils.js'`

### 15. Only Locals Can Be Compared to null/undefined
- **Rule**: Only local variables can be directly compared to `null`, `undefined`, or string literals
- **Limitation**: Cannot compare property access expressions like `x.foo` or `obj.property` to null/undefined
- **Error**: Expressions like `if (x.foo != null)` or `while (current.next !== null)` will fail
- **Workaround**: Assign property to local variable first, then perform comparison
- **Example**: 
  ```typescript
  // Won't work - comparing property access to null
  if (x.foo != null) {
    x.foo.someMethod(); // Error: "Only locals can be compared to null/undefined"
  }
  
  // Works - compare local variable to null
  let foo = x.foo;
  if (foo != null) {
    foo.someMethod(); // Success: local comparison works
  }
  
  // Won't work - comparing property in loop
  while (current.next !== null) { // Error
    current = current.next;
  }
  
  // Works - use local variable in loop
  let nextNode = current.next;
  while (nextNode !== null) {
    current = nextNode;
    nextNode = current.next;
  }
  ```


### 16. Function Signatures Must Be Fully Annotated
- **Rule**: Every function parameter requires an explicit type annotation. Named function declarations must also supply an explicit return type; arrow callbacks currently infer their return type but still need annotated parameters.
- **Error**: `TypeCheckFun.sk` emits "A parameter must have an explicit type annotation" for parameters without types and a "must have an explicit return type annotation" error if a named function omits its return type.
- **Workaround**: Declare signatures like `function handler(value: string | number): Result { ... }` and annotate callback parameters, adding `: T` return annotations where needed for clarity.
- **Verified by**: `tests/expect-error/function-args.ts`, `tests/expect-error/anonymous-function-annotations.ts`, and `tests/expect-error/missing-return-type.ts`.

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

### 18. Template Literal Strings ✅
- **Rule**: Template literals with backticks and string interpolation are fully supported
- **Syntax**: Use backticks `` ` `` with `${expression}` for interpolation
- **Features**: 
  - Basic template literals: `` `Hello World` ``
  - String interpolation: `` `Hello ${name}` ``
  - Complex expressions: `` `Result: ${value.toString()}, Sum: ${a + b}` ``
  - Multiline templates with interpolation
- **Type Safety**: Interpolated expressions must be convertible to string (primitives, objects with toString(), etc.)
- **Example**:
  ```typescript
  // ✓ CORRECT - template literals work with complex expressions and multiline
  const message: string = `Hello ${name.toUpperCase()}, Status: ${age >= 18 ? "Adult" : "Minor"}`;
  const multiline: string = `Line 1: ${name}
  Line 2: ${age}`;
  ```

### 19. Boolean Literal Type Casting Not Supported
- **Rule**: Casting boolean values to literal boolean types is not supported
- **Error**: "Construction not supported" when using `false as false` or `true as true`
- **Workaround**: Use explicit boolean comparisons or different type definitions
- **Example**:
  ```typescript
  // WRONG - will cause errors
  let result: 'true' | 'false' = false as false;
  
  // CORRECT - use conditional expressions
  let result: 'true' | 'false' = condition ? 'true' : 'false';
  ```

### 20. `for...of` Loop Constraints
- **Rule**: Only arrays, tuples, strings, or objects with an explicit string index signature are recognized as iterables. Plain object literals (without `[key: string]: ...`) and custom classes are rejected.
- **Error**: `TypeCheckStmt.getValueType` raises "Invalid iterable type for for-of loop" when the iterable type falls outside those shapes (see `tests/expect-error/for-of-object.ts`).
- **Semantics**: The element type is computed once from the iterable’s structure; there is no special flow refinement beyond the standard loop scopes. For objects with an index signature, the element type is the index value type; for strings it is `string`.
- **Workaround**: When you need to iterate a record-like object, first expose a string index signature (e.g., type `{ [key: string]: number }`) or convert the value to an array via `Object.keys` / `Object.values`.
- **Verified by**: `examples/src/for_in_for_of_tests.ts` (arrays, tuples, strings, index signatures) and `tests/expect-error/for-of-object.ts` (plain objects rejected).

### 21. Promises and async/await
- **`Promise<T>` is a plain object type** declared in the builtin stubs with `then`/`catch`/`finally` methods, so promises follow the same structural typing as every other object (`in`, `keyof`, width subtyping, payload covariance all behave normally). The signatures are simplified relative to TypeScript: `then<U>(onfulfilled: (value: T) => U | PromiseLike<U>): Promise<U>` takes exactly one required callback — there is no `onrejected` second argument and the callback is not optional. The stubs also declare `PromiseLike<T>` (the minimal thenable shape, as in lib.es5), and `Promise<T> <: PromiseLike<T>` holds.
- **The `Promise` value** exposes the constructor (`new Promise<T>(executor)`, executor required) and the statics `Promise.resolve`, `Promise.reject`, and `Promise.all` (simplified: `all<T>(values: ReadonlyArray<Promise<T>>): Promise<Array<T>>` — no tuple/mixed-iterable form). Other statics (`race`, `any`, `allSettled`, ...) are not available.
- **`await` is structural**, like tsc: any object whose `then` is shaped like a thenable can be awaited. Applying `await` to a non-thenable is an **error** (`'await' can only be applied to a Promise`, in the spirit of `@typescript-eslint/await-thenable`); tsc instead lets non-thenables pass through unchanged. On a union that is only **partly** thenable the error is non-fatal and checking continues with the thenable branches unwrapped and the non-thenable parts passed through — the same result type as tsc (which reports nothing).
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

## Coding Guidelines for SKJS

1. **Avoid toplevel variables**: Define everything inside functions or classes
2. **Array literals use delayed typing**: `[...]` commits to array or tuple based on usage context
3. **Keep constructor signatures simple**: Match parent class constructors exactly
4. **Use single console.log arguments**: Concatenate strings before logging
5. **Avoid private modifiers**: Use public fields only
6. **Handle undefined explicitly**: Check for undefined before method calls
7. **Generic classes work well**: Both generic functions and generic classes are fully supported
8. **Array literals work for initialization**: `const arr: number[] = [1, 2, 3]` works; `new Array<T>()` also works
9. **Static fields must be readonly**: Use `static readonly` together for class constants with primitive types only
10. **Use local variables for null/undefined comparisons**: Always assign properties to locals before comparing to null/undefined
11. **NEVER use the `any` type**: The `any` type is not supported in SKJS - use specific types or union types instead
13. **Avoid the `!` operator**: Use explicit comparisons like `=== false` instead of `!` for better type safety
14. **Template literals work as expected**: Use backticks and `${expression}` syntax for string interpolation and multiline strings

## File Organization and Structure Guidelines

### 22. Prefer Small, Focused Files
- **Rule**: Split code into as many separate files as possible
- **Guideline**: Aim for one function per file whenever practical
- **Rationale**: Small files are easier to type-check, debug, and maintain in SKJS
- **Example Structure**:
  ```typescript
  // math_add.ts
  export function add(a: number, b: number): number {
    return a + b;
  }
  
  // math_multiply.ts  
  export function multiply(a: number, b: number): number {
    return a * b;
  }
  
  // math_utils.ts - aggregates multiple utilities
  import { add } from './math_add.js';
  import { multiply } from './math_multiply.js';
  export { add, multiply };
  ```

### 23. Keep Classes Minimal
- **Rule**: Define only core methods in classes (constructor, essential primitives)
- **Guideline**: Move complex logic to separate utility functions
- **Rationale**: Smaller classes are easier to type-check and less prone to SKJS limitations
- **Example**:
  ```typescript
  // user.ts - minimal class
  export class User {
    name: string;
    email: string;
    
    constructor(name: string, email: string) {
      this.name = name;
      this.email = email;
    }
  }
  
  // user_validation.ts - separate utility
  import { User } from './user.js';
  export function validateUser(user: User): boolean {
    return user.name.length > 0 && user.email.includes('@');
  }
  
  // user_formatting.ts - separate utility
  import { User } from './user.js';
  export function formatUserDisplay(user: User): string {
    return user.name + ' (' + user.email + ')';
  }
  ```

### 24. File Size Guidelines
- **Target**: Aim for files under 50 lines when possible
- **Maximum**: Keep files under 100 lines for optimal SKJS performance
- **Benefits**: 
  - Faster type checking
  - Easier debugging
  - Better modularity
  - Reduced complexity per file
- **When to Split**: If a file has multiple functions, consider splitting into separate files

### 25. Logical File Organization
- **Group by Feature**: Create separate files for related functionality
- **Separate Concerns**: Keep types, utilities, and business logic in different files
- **Example Directory Structure**:
  ```
  src/
  ├── types/
  │   ├── user.ts
  │   ├── product.ts
  │   └── order.ts
  ├── utils/
  │   ├── string_utils.ts
  │   ├── math_utils.ts
  │   └── validation_utils.ts
  ├── business/
  │   ├── user_service.ts
  │   ├── order_processing.ts
  │   └── inventory_management.ts
  └── main.ts
  ```

### 26. Import/Export Organization
- **Rule**: Use barrel exports to aggregate related functionality
- **Pattern**: Create index files that re-export from multiple small files
- **Example**:
  ```typescript
  // utils/index.ts
  export { add, subtract } from './math_add.js';
  export { multiply, divide } from './math_multiply.js';
  export { validateEmail } from './email_validator.js';
  
  // main.ts
  import { add, validateEmail } from './utils/index.js';
  ```

### Benefits of Small Files in SKJS
1. **Faster Compilation**: SKJS type-checks smaller files more quickly
2. **Easier Debugging**: Isolated functions are easier to test and debug
3. **Better Modularity**: Encourages clean separation of concerns
4. **Reduced Complexity**: Each file focuses on a single responsibility
5. **Improved Maintainability**: Changes affect smaller, more focused areas
6. **Better Error Localization**: Type errors are easier to locate in small files

## What Works Well in SKJS

- Function generics (`function identity<T>(arg: T): T`)
- Generic classes (`class Stack<T> { ... }`)
- Interface definitions
- Union types (`string | number`)
- Tuple types (`[number, string, boolean]`)
- Algebraic Data Types with `kind` field discrimination
- Import/export system with relative paths
- Basic class definitions
- Method calls with proper type checking
- Explicit type annotations
- String concatenation and basic operations
- Template literal strings with interpolation
- Math operations and comparisons

## Recommended Patterns

### Array Literals (Delayed Typing)
```typescript
// Good - array literal commits to Array via type annotation
const nums: number[] = [1, 2, 3];
nums.push(4);

// Good - array literal commits to Array via method usage
const items = [1, 2, 3];
items.push(4); // commits to Array<number>

// Good - array literal commits to Tuple via type annotation
const pair: [number, string] = [42, "hello"];
const coordinate: [number, number] = [10, 20];

// Error - once committed, cannot change
const values = [1, 2];
values.push(3);  // commits to Array<number>
const tuple: [number, number] = values; // Error: already committed to Array
```

### Class Design
```typescript
// Good - simple class
class Person {
    name: string;
    constructor(name: string) { this.name = name; }
}

// Good - static readonly fields for constants
class Config {
    static readonly API_URL: string = "https://api.example.com";
    static readonly MAX_RETRIES = 3;  // Type inferred
}
const url = Config.API_URL;

// Good - generic classes work well
class Stack<T> {
    items: Array<T>;
    constructor() { this.items = new Array<T>(); }
}

// Good - inheritance with matching constructors
class Student extends Person {
    constructor(name: string, age: number) { super(name, age); }
}

// Avoid - static fields without readonly
class Bad {
    static count: number = 0;  // Error: static fields must be readonly
}

// Avoid - inheritance with different constructor signatures
class Student extends Person {
    constructor(name: string, age: number, id: string) { ... } // Error: signature mismatch
}
```

### Function Organization
```typescript
// Good - everything in functions
function main(): void {
    let x: number = 10;
    console.log(x.toString());
}

// Avoid - toplevel variables
let x: number = 10; // "Construction not supported: toplevel let"
```

### String Literals and 'as const' Syntax
```typescript
// Good - both quote styles work in type definitions
type Status = 'active' | 'inactive' | 'pending';   // ✓ creates literal types
type Status = "active" | "inactive" | "pending";   // ✓ also creates literal types

// Good - use 'as const' in expressions for literal types
let config = { status: 'active' as const, id: 123 };      // ✓ 'active' is literal
let config = { status: "active" as const, id: 123 };      // ✓ also works

// Good - regular string values don't need 'as const'
let message: string = "Hello, world!";                     // ✓ regular string

// Now works - automatic literal types for kind field
let result = { kind: 'success', data: 'hello' };          // ✓ 'success' is automatically literal
```

### Algebraic Data Types
```typescript
// Good - ADT type definition (no 'as const' needed in types)
type Shape = 
    | { kind: 'circle', radius: number }
    | { kind: 'square', side: number };

// Good - ADT object creation (automatic literal types for kind field)
function createShapes(): void {
    let circle: Shape = { kind: 'circle', radius: 5 };
    let square: Shape = { kind: 'square', side: 4 };
}

// Good - pattern matching works with 'as const' objects
function calculateArea(shape: Shape): number {
    if (shape.kind === 'circle') {
        return Math.PI * shape.radius * shape.radius;
    } else if (shape.kind === 'square') {
        return shape.side * shape.side;
    }
    return 0;
}

// Now works - automatic literal types for kind field  
let badCircle: Shape = { kind: 'circle', radius: 5 };  // ✓ 'circle' is automatically literal

// Avoid - using different discriminator field
type BadShape = 
    | { type: 'circle', radius: number }  // Won't enable pattern matching
    | { type: 'square', side: number };
```

### Import/Export System
```typescript
// Good - proper import syntax
import { add, multiply, User } from './math_utils.js';
import { Result, Option } from './types.js';

// Export functions and types
export function helper(): void { ... }
export type MyType = { ... };
export interface MyInterface { ... }

// Avoid - incorrect import paths (in node16/nodenext mode)
import { add } from 'math_utils';        // Missing ./ and .js
import { add } from './math_utils';      // Missing .js extension (OK in bundler mode)
import { add } from './math_utils.ts';   // Wrong extension
```

### Template Literal Patterns
```typescript
// Avoid - non-stringifiable objects (will cause type errors)
// const badTemplate: string = `Object: ${someComplexObject}`; // Error if object lacks toString()
```

### Null/Undefined Comparison Patterns
```typescript
// Good - compare local variables to null/undefined
function processUser(user: { name: string | null, age: number | null }): void {
    let name = user.name;
    let age = user.age;
    
    if (name != null) {
        console.log(name.toUpperCase()); // Works: local comparison
    }
    
    if (age != null) {
        console.log(age.toString()); // Works: local comparison
    }
}

// Good - handle linked list traversal with locals
function traverseList<T>(head: ListNode<T> | null): void {
    let current = head;
    let nextNode = current?.next;
    
    while (nextNode !== null) {
        current = nextNode;
        nextNode = current.next;
    }
}

// Good - handle union types with local assignment
function handleResponse(response: { data: string } | { error: string }): void {
    let data = response.data;
    let error = response.error;
    
    if (data != null) {
        console.log(data); // Works: local comparison
    } else if (error != null) {
        console.log(error); // Works: local comparison
    }
}

// Avoid - comparing property access directly to null/undefined
function badProcessUser(user: { name: string | null }): void {
    if (user.name != null) { // Error: "Only locals can be compared to null/undefined"
        console.log(user.name.toUpperCase());
    }
}

// Avoid - comparing property in loops
function badTraverseList<T>(head: ListNode<T> | null): void {
    let current = head;
    while (current.next !== null) { // Error: property comparison to null
        current = current.next;
    }
}
```

## Working Examples Summary

The following TypeScript files demonstrate patterns that work well with SKJS:

### Basic Examples
- **basic_types.ts**: Variable declarations, functions, basic types
- **classes.ts**: Class definitions without inheritance
- **algorithms.ts**: Array operations, recursive algorithms

### Advanced Examples  
- **advanced.ts**: Interfaces, generics, union types, type annotations
- **generic_examples.ts**: Comprehensive generic classes (Container, Collection, Stack, Pair)
- **tuple_examples.ts**: Tuple types, mixed-type collections, tuple operations
- **simple_adt_examples.ts**: Algebraic Data Types with `kind` field pattern matching
- **state_machines.ts**: State machine patterns using ADTs and pattern matching
- **working_patterns.ts**: Practical patterns - branded types, Result type, validation
- **data_structures.ts**: Stack implementations with concrete types
- **functional_programming.ts**: Map, filter, reduce, function composition
- **recursion_examples.ts**: Factorial, Fibonacci, string reversal
- **string_processing.ts**: String manipulation, palindrome checking
- **edge_cases.ts**: Optional parameters, null checks, boundary conditions
- **complex_types.ts**: Type aliases, nested interfaces, type-safe operations
- **mathematical_computations.ts**: Prime numbers, matrix operations, statistics

### Module System Examples
- **math_utils.ts**: Exportable math functions and utilities
- **array_utils.ts**: Array manipulation functions for import/export
- **types.ts**: Shared type definitions and interfaces
- **result_utils.ts**: Result type utilities with validation functions
- **business_logic.ts**: Complex business logic using multiple imports
- **import_demo.ts**: Comprehensive demonstration of the import system

### Enhanced Builtins
The builtins.ts file has been extended with:
- Additional Array methods: `filter`, `reduce`, `join`, `slice`
- More Math functions: `min`, `ceil`, `round`, `abs`, `pow`, `sqrt`
- Extended string methods: `substring`, `indexOf`, `split`, `toLowerCase`, `toUpperCase`

All examples follow SKJS constraints and pass type checking successfully.
