# SKJS TypeScript Subset Rules

This document describes the rules and restrictions of the SKJS type checker, which aims to implement a sound subset of TypeScript.

## Diagnostics: errors vs warnings

SKJS emits diagnostics at two severities:

- **Errors** are soundness-critical (type mismatches, unsupported constructs, unbound names, …). A file with any error fails the build (exit code `2`).
- **Warnings** are non-fatal, lint-style diagnostics that are not soundness-critical. They are reported but do **not** fail the build — a file whose only diagnostics are warnings exits `0`. They also never abort checking of a definition, so they don't hide later errors.

Diagnostics currently reported as warnings: redundant optional chaining (`Useless '?.'`) and redundant non-null assertions (`This operator is useless` on an operand that is never null/undefined), redundant destructuring defaults (`Default is useless …` / `Element is always undefined`), a redundant negation of a boolean literal (`This constant expression could have been simplified` on `!true` / `!false` — a valid but pointless way to write the literal), a `void`-typed expression used as a value in `??`/`!`/`===`/`typeof` (`An expression of type 'void' cannot be used here`, the `no-confusing-void-expression` rule — runtime-sound and tsc-permissive), `await` applied to a value that is not (always) a thenable (`'await' can only be applied to a Promise`, the `await-thenable` rule — `await` passes a non-thenable through unchanged at runtime, as tsc types it; SKJS is deliberately stricter but non-fatal), a `switch` that cannot do anything (`A switch statement must have at least one case` — sound, and accepted silently by tsc, so the code is pointless rather than wrong; the scrutinee is still checked — and `This switch has a single branch; use an 'if' statement instead`), an unreachable clause (`This case is unreachable: …` / `This 'default' case is unreachable: …`), a `default` clause that is not the last branch of a switch (`The 'default' clause should be the last branch of a switch`; a lint concern only, since `default` runs only when no `case` matches regardless of its position; two `default` clauses in one switch, by contrast, is rejected as a hard error, `A 'default' clause cannot appear more than once in a 'switch' statement` (TS1113, since it is a JavaScript SyntaxError)), a non-exhaustive `switch` over a finite type with no `default` (`Switch is not exhaustive; the following cases are unhandled` — tsc does not require exhaustiveness and SKJS does not rely on the verdict for narrowing or reachability), a statically-known `in` check whose result is a foregone conclusion (`This condition is always true` / `This condition is always false`, the `no-unnecessary-condition` rule — the check is well-typed and sound to evaluate, so it warns rather than erroring; a `(false, false)` contradiction between the operand types stays an error), and non-overlapping strict comparisons (`This comparison is always true/false because the operand types do not overlap`, only when the operands' value sets are provably disjoint: primitive kind mismatches like `number === string`, disjoint literal sets like `0 === 1`, comparisons against `null` or `undefined` that the other operand can never hold (`x === null` when `x` cannot be null is dead code — reported even though tsc is silent), and primitives against object types they cannot box into. Reference types — objects, functions, promises, class instances — are never reported, because a single value can inhabit both sides (width subtyping, never-returning functions, `Promise<never>`), even where tsc reports TS2367. Number literals are normalized at parse time (see rule 30), so `1e3 === 1000` compares one single value and is reported as always true; for literals beyond IEEE-754 double precision (more than 15 significant digits, or outside the double range), two spellings can denote the same runtime double, so the overlap warnings stay silent rather than risk a false always-false claim). SKJS additionally warns when both operands of a strict comparison can only hold one identical value (`This comparison is always true/false because the operands always hold the same single value`, e.g. `x === y` with both typed `"a"`, `0`, `true`, `null`, or `undefined`) — tsc reports nothing there. Comparisons where either operand is a literal expression (including signed numbers like `-1`) are exempt: re-checking a narrowed discriminant on the last variant of a union (`else if (color.kind === "blue")`) is idiomatic, not a bug. The exemption is syntactic, so re-checking against a hoisted constant (`x === BLUE`) still warns. A non-null assertion (`!`) whose operand is *always* null or undefined stays an **error**: `x!` would then have the empty type and satisfy any annotation, so accepting it would be unsound. Parser-level lint rules (e.g. `==`/`!=`, empty `if`) are still reported as errors.

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
- **Warning for redundant 'as const'**: SKJS warns (but does not error) when `as const` is used unnecessarily
- **Manual 'as const' still needed for**: Non-ADT object properties, nested values, and array elements when nothing in the expected type asks for a literal (see the `save` example below)

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

// ✓ 'as const' on an array literal - a readonly tuple of the elements' 'as const' types
function makeReadonlyTuple(): void {
  const pair = [0, 1] as const; // readonly [0, 1]
  const nested = [[0, 1]] as const; // readonly [readonly [0, 1]]
}
// (the whole-object form `{ ... } as const` is not yet supported)
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

### 18. Template Literal Strings ✅
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
- **Also not supported**: a number hole whose spelling does not pin down a single double — a beyond-precision decimal (`` `${9007199254740993}` ``) or a radix literal past 2^53 (`` `${0x20000000000001}` ``). tsc reduces these by round-tripping through the double; SKJS rejects rather than name a string no runtime value produces (see rule 30 on literal normalization)
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

### 20b. Switch Clauses Must Not Fall Through

- **Rule**: A `case`/`default` clause that has statements and can complete normally must exit explicitly (`break` / `return` / `throw` / `continue`) when another clause follows it. This is `noFallthroughCasesInSwitch`, which SKJS turns **on** by default where `tsc` leaves it off, and honours either way — set it to `false` to allow deliberate fallthrough.
- **The option decides the diagnostic, never the typing**: a clause that falls through is still one the next clause is reached from, so the narrowing below applies whether or not the fallthrough is reported. Turning the option off allows the fallthrough; it does not make the clause fallen into assume its label matched.
- **Exempt**: an **empty** clause, which is how several labels are given one body (`case "a": case "b": …`), and the **last** clause, which has nothing to fall into. Falling *through* means running one clause's statements and then the next clause's too — neither of these does that. `noFallthroughCasesInSwitch` exempts both for the same reason. What kind of clause it is does not enter into it: a `default` with statements falls into the clause after it exactly as a `case` does, and is reported the same way.
- **Termination**: an empty clause takes the termination of the clause it falls into, so `case "a": case "b": return 1;` returns on every path. A clause that `break`s leaves the switch instead, so grouping labels in front of it does not make the switch return.
- **Narrowing**: a body is entered both by matching its own label and by falling through the clauses above it, so the scrutinee there is the union, over those entries, of its value on each — the label on a direct entry, and whatever a falling clause left it at on a fallthrough entry. With no reassignment this is just the disjunction of the labels — in `case 1: case 2: <body>` the scrutinee is `1 | 2`, not `2`. But a clause that reassigns the scrutinee carries the *reassigned* value across, not the label it matched: after `case "a": y = c;` falling into `case "b":`, `y` is `"b" | "c"` (the direct-entry "b", or the "c" carried), not `"a" | "b"` — dropping the "c" would be unsound, keeping the "a" over-wide. An empty `default` among the clauses makes the body reachable for any unmatched value, which the union covers through the `default`'s own complement narrowing.
- **Exhaustiveness**: a switch whose cases leave no value of the scrutinee unmatched always runs one of them, exactly as one with a `default` does — so it does not escape to the code after it (`switch (x: 1 | 2) { case 1: return …; case 2: return …; }` returns on every path, with no `default` and no trailing `return`), and it leaves no binding at its pre-switch value. This needs the scrutinee's values to be listable: a `number` or `string` scrutinee, or one case short, still escapes. A `boolean` is listable — `true` and `false` are all it can be — so `case true:` / `case false:` covers it.
- **Writes carry across**: the clause fallen from has also *run*, so a write it made is already in effect in the clause fallen into, which starts from what either entry leaves behind — after `case 1: y = "b";` falling into `case 2:`, `y` is `"a" | "b"` there, the write or whatever the switch was entered with. Only the clause fallen *into* is reached that way: a clause that `break`s does not carry its write into the next, and a later clause reached on its own label does not see it either.
- **Paths out**: after the switch, a binding is the union over the clauses that can actually *reach* the code after it — a clause that `break`s, or the last clause falling off the end — plus, when the switch is not exhaustive, matching no clause. A clause that falls into the next does not exit there (it runs on, its writes carried into the clause it falls into), so it is not a separate path out; nor is one that only returns/throws/continues. This keeps definite assignment precise (`case 1: case 2: y = …; break;` assigns `y` on every exit, so `y` is not "used before assigned" afterwards) and the merged value tight (a value a fall-through clause leaves that the next clause overwrites does not survive). A clause that can `break` *and* return is still a path out via the break.
- **Break edges carry their jump state**: a `break` leaves the switch with the state *at the jump*, which a later write in the same clause can change — so the state after the switch unions each break edge, not each clause's end-of-block scope. `case 1: if (c) break; y = "b"; break;` reaches the code after with `y` either "a" (the guarded break) or "b" (the end), so `y` is `"a" | "b"` there, not "b". Each break records a snapshot against the switch (a `JumpCatcher`) that the post-switch merge folds in (SkipLabs/skjs#910). Loops do the same for both kinds of edge: a `break` joins the state after the loop directly, and a `continue` re-enters the header, whose exit then leaves with the edge's state — in a `for`, continue edges run the increment and break edges skip it. An edge binds to the nearest construct that catches it: `break` to the nearest loop *or* switch, `continue` to the nearest loop, through any switch in between.
- **`default` narrowing**: a `default` runs only for a value no `case` matched, so its body is narrowed to the switched type minus every case label — in `switch (x: 1 | 2 | 3) { case 1: …; case 2: …; default: … }` the scrutinee is `3` there. Every case rules its value out, including any written after the `default` — where the clauses sit says nothing about which values reach it.
- **Error**: "Fallthrough case in switch; add a 'break'" (TS7029), reported on the clause's last statement.
- **Verified by**: `tests/expect-error/switch-empty-cases.ts`, `tests/expect-error/switch-fallthrough-narrowing.ts`, `tests/expect-error/switch-scope-merge.ts`, `tests/expect-error/switch-exit-paths.ts`, `tests/expect-error/switch-scrutinee-reassign.ts`.

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
- **Name resolution**: the checker reserves `SKJS_Closed` — a 1-ary `SKJS_Closed<...>` application is intercepted before name resolution and means the closed-object operator. User code writes `Closed<T>`, declared in the SKJS stubs (`import-stubs/@types/skjs`) as `type Closed<T> = SKJS_Closed<T>`, so it works with no user declaration. For tsc compatibility, a tsc-only stub declares `type SKJS_Closed<T> = T`, making tsc read `Closed<T>` as the identity. Note include resolution is stubs-first engine-wide, so a file-local redefinition of `Closed` (like any stub-declared name) is inert.
- **Validation**: `T` must expand to a statically known object type (single object or union of objects — a union distributes, closing each branch) without declared index signatures. Primitives, arrays/tuples, abstract type parameters, and indexed object types are rejected (`Closed<T> requires ...` errors).
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
- **Rule**: every object-type branch tracks callability and constructibility as present-with-signature / provably-callable-without-signature (the `Function` state) / definitely-absent / unknown. `typeof x === "function"` keeps a branch whose call mode is not definitely-absent — a class-constructor value is `typeof "function"` at runtime even though calling it without `new` still errors (issue #774): its call mode is provably-callable, and construction maintains "construct signature ⟹ call mode at least provably-callable" — and drops only branches provably without [[Call]]: class instances, arrays and tuples, object literals and spread results, enum objects. Structural object types (`{}`, `{ a: number }`, interfaces, `object`) survive the "function" branch, because a function carrying the right properties inhabits them (`Object.assign(function () {}, { a: 1 })` is a `{ a: number }`); symmetrically they survive the else of `typeof x === "object"`. A successful "function" test is a proof of [[Call]], so surviving unknown branches strengthen to provably-callable — a nested `typeof === "object"` check then drops them, matching tsc's `{} -> Function -> never` (issue #805) — and in branches proven not `typeof "function"`, unknown strengthens to definitely-not-callable, so a later `typeof x === "object"` else drops them. Symbolic types narrow by intersection in the true branch: a type parameter `T` becomes `T & Function` and `unknown` becomes `Function`, matching tsc; their else branches stay unrefined ("T minus functions" needs a complement type, issue #806)
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
- **Readonly is preserved**: a field the scrutinee declared `readonly` stays readonly through the narrowing — the intersection with the class view may restrict what the field reads as, but never grants a write the value's type withheld (`x.a = x.b` on a narrowed `{ readonly a; readonly b }` is rejected). tsc narrows to `C<any>` and accepts it
- **Verified by**: `tests/expect-error/instanceof-generic-skolem-args.ts`, `tests/expect-error/tparam-name-collision.ts`, `tests/expect-error/instanceof-readonly-field.ts`

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
- **Branch cap (10,000 deduplicated branches)**: distributing spreads and intersecting unions of objects cross-product their branches; past the cap the two sites behave differently. A **distributed object spread degrades soundly**: the overflowing spread is over-approximated as an arbitrary object, so its source fields are dropped and every pre-spread field widens to `unknown` (plus the `[string]/[symbol]: unknown` excess indexes); the literal still type-checks and SKJS emits a **warning** (SKJS9009). This is sound but less precise than TypeScript, which distributes up to ~100,000 constituents — so a property TypeScript keeps precisely may read as `unknown` in SKJS past the cap. An **intersection of unions is still rejected** as too complex (TS2590-style, the definition is abandoned): unlike a spread literal (a covariantly-used produced value), an intersection type flows into contravariant positions where widening it would be unsound, so no sound degradation exists. A more precise spread collapse (keeping fields common to every source branch) is tracked as SkipLabs/skjs#747. Verified by `tests/expect-error/spread-union-distribute.ts` (`tooManyUnionSpreads`, `capDegradeDropsCommonSourceField`), `spread-union-cap.ts`, and `intersection-branch-cap.ts`.

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
- **Rule**: Number literals are normalized to their canonical `String(Number(x))` form at parse time, so different spellings of the same value are the same literal type: `1.0` = `1`, `0x10` = `16`, `0b10` = `2`, `0o17` = `15`, `1_000` = `1000`, `1e3` = `1000`, `1e+3` = `1000`, `1e-3` = `0.001`, and `-0` = `0`. Bigint literals normalize the same way (`1_000n` = `1000n`, `0x10n` = `16n`, `-0n` = `0n`), exactly at any magnitude. This applies to literal types, object field names, and expression literal types.
- **Matches TypeScript**: tsc keys number literal types by their double value; textual canonicalization agrees with it for all values within IEEE-754 double precision.
- **Invalid forms are syntax errors**: malformed numeric literals (`0b12`, `0o8`, `0x`, `1e`, misplaced separators `1__0`/`1_`, legacy octal `010`) are parse errors matching tsc (TS1177/TS1178/TS1125/TS1124/TS6188/TS6189/TS1121).
- **Current caveats** (pinned with FIXME tests in `tests/expect-error/`):
  - Literals whose exact value is not representable in a double (radix literals above 2^53, exponents beyond ~1e6) are left in their spelled form and compare textually: sound, but stricter than tsc for two spellings of the same double. The always-true/false comparison warnings are suppressed when such a literal (or any literal with more than 15 significant digits, or outside the double range) is involved.

### 30b. String Literal Escape Decoding
- **Rule**: String literals are decoded to their runtime String Value at parse time, so different spellings of the same value are the same literal type: `"\x61"` = `"\u{61}"` = `"a"`, `"\n"` = `"\x0a"`, `"\0"` = `"\x00"`, `"\a"` (a NonEscapeCharacter) = `"a"`, and a surrogate pair (`"\uD83D\uDE00"`) = the astral code point (`"\u{1f600}"`). A LineContinuation (backslash + line terminator) is elided, so its value is `""` (empty, hence falsy). This applies to literal types, string values, object field names, and module specifiers.
- **Matches TypeScript**: tsc keys string literal types by their decoded String Value, so escaped and plain spellings collapse to one type.
- **Invalid forms are syntax errors**: legacy octal (`"\1"`, `"\0"` followed by a digit) and NonOctalDecimal (`"\8"`, `"\9"`) escapes, truncated `\x`/`\u`, and out-of-range `\u{110000}` are parse errors matching tsc (TS1487/TS1488/TS1125/TS1198).
- **Stricter than TypeScript (soundness-required)**: a lone (unpaired) surrogate escape (`"\uD800"`) is rejected. tsc keeps it as a lone UTF-16 code unit, but a Skip `Char` is a Unicode code point and cannot represent a surrogate, so decoding it is impossible and rejecting is the sound choice. Template literal types are decoded the same way (see rule 18b), so `` `\x61` `` is the type `"a"`.
- **Verified by**: `tests/expect-error/string-literal-escapes-prettier-ignore.ts`, `tests/expect-error/string-literal-line-continuation-prettier-ignore.ts`, `tests/expect-error/string-escape-*-prettier-ignore.ts`

### 30c. Identifier Characters ✅
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
- **Constant initializers** are folded: literals, unary `+`/`-`/`~`, binary arithmetic and bitwise operators (JS int32 semantics) and string concatenation over constants, and references to already-initialized members — bare (`B = A`), qualified (`B = E.A`), element access (`B = E["A"]`), and members of enums provably initialized first (same-file enums declared earlier, or imported ones). Uninitialized members auto-increment from the previous member's integer value. Integer arithmetic folds exactly within the double-safe range; fractional or out-of-range results (e.g. `1.5 + 1`, auto-increment past 2^53) soundly widen the member to `number` where tsc folds precisely (FIXME-pinned in the tests). References that read a not-yet-initialized member — self references, members declared after the referencing initializer (in the same or another enum), and cyclic cross-enum chains — are rejected with tsc's TS2651 in every folded shape; a *bare* forward name (`A = B, B = 1`) instead reports the unresolved name.
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
- **More permissive than TypeScript (sound)**: without an annotation the inferred type *evolves* on assignment, so `let x = "a"; x = 5;` is accepted and `x` becomes a `number`, where tsc pins `let x = "a"` to `string` and rejects the write. This stays sound because reads see the written type, so any misuse is still caught where the value is read. A bare `let x = null`/`undefined` evolves the same way (TypeScript's evolving `any`).
- A write that escapes the current frame — across a loop iteration, or into a captured enclosing-function local from inside a lambda — is checked against the declared type even when the binding is un-annotated, because the narrowing cannot be trusted there (SkipLabs/skjs#769).
- An **array-destructuring assignment** writes each of its targets the same way, so all of the above applies per target (SkipLabs/skjs#839): `[x] = [5]` behaves exactly like `x = 5`, `[o.f] = [5]` like `o.f = 5`, and a target captured by a lambda is checked like any other captured write. Element types are derived as they are for a destructuring declaration: per index from a tuple (a target past the end reads `undefined`), or the iterator's element type widened with `undefined` from anything else iterable, with the rest target taking the remaining elements. Destructuring a rest allocates a *fresh* array, so nothing aliases it at a fixed arity: it is typed like an array literal and can be read as either a tuple or a growable array, whichever the target asks for (`[x, ...r] = [1, 2, 3]` works for `r: [number, number]` and for `r: number[]`). An **existing** tuple stays un-assignable to an array (`const a: number[] = tup` is rejected, where tsc accepts it unsoundly), because writing through the array view would break the tuple's arity. Object-destructuring assignment (`({ a: x } = e)`) remains unsupported.
- **Verified by**: `tests/expect-error/annotated-write-enforcement.ts`, `tests/expect-error/captured-local-write.ts`

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
  `(this: <shape>) => R`), which is what lets primitives and class instances
  inhabit such shapes soundly. Extracting the member for a free call
  (`const f = shape.m; f()`) or laundering it through a no-`this` type is
  rejected, and `.call`/`.apply`/`.bind` are not synthesized for it (its
  carrier type is erased). Property-syntax members stay genuinely free
  functions.
- **Verified by**: `tests/expect-error/this-parameter*.ts`

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
15. **Annotate bindings that are used across statements**: without an annotation, inference for `[]`, `new Container()`, and some generic-call results can depend on later use; for a `const`, an annotation or explicit type arguments make it order-independent. Prefer `const` — a `let`'s type follows its assignments
16. **Declare the widest type a value will ever need at its creation site**: declared mutable element and field types do not widen with use (sound invariance, stricter than tsc); on parameters that only read, use `readonly` element types so narrower arguments are accepted

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
// Avoid - object/array interpolations (rejected even when they have toString())
// const badTemplate: string = `Object: ${someComplexObject}`; // restrict-template-expressions error
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
