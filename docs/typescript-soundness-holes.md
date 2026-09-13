# TypeScript Soundness Holes

A soundness hole is a program `tsc --strict` accepts in which a runtime value contradicts its static type: a `string`-typed binding holding `42`, a `readonly` field being written, a tuple whose `length` is typed `2` and evaluates to `3`. Most of the entries below are *deliberate* TypeScript design decisions — method-parameter bivariance, mutable-container covariance, numeric enums accepting `number`, user-defined type predicates — that trade soundness for ergonomics; they are not compiler bugs, and where that is the case it is said so explicitly. This catalogue exists because SKJS targets a sound subset of TypeScript and therefore must refuse some programs tsc accepts; each entry records what SKJS does instead, including the cases where SKJS shares the hole. Every repro here was run against the pinned tsc 6.0.3 under `--strict` and observed to compile with zero errors; where a non-`--strict` flag (`--noUncheckedIndexedAccess`, `--exactOptionalPropertyTypes`) closes a hole, that is noted. Most entries are pinned by a test in `tests/expect-error/`; the few that are not are marked. Repros contain no `any`, `as`, or `!` unless the entry says otherwise — the escape hatches TypeScript documents as unsound are out of scope, except where the compiler synthesizes the `any` itself. This list is not exhaustive: it covers the holes SKJS has had to reason about.

## Contents

- [Mutability & readonly](#mutability--readonly)
- [Narrowing & control flow](#narrowing--control-flow)
- [Object literals, spread & excess properties](#object-literals-spread--excess-properties)
- [Index signatures](#index-signatures)
- [Optional fields & definite assignment](#optional-fields--definite-assignment)
- [Functions, callability & this](#functions-callability--this)
- [Generics & type parameters](#generics--type-parameters)
- [Classes, interfaces & declarations](#classes-interfaces--declarations)
- [Enums](#enums)
- [Standard library declarations](#standard-library-declarations)

## Mutability & readonly

### readonly property modifiers are ignored by assignability

`readonly` is not part of tsc's assignability relation, so `{ readonly name: string }` is assignable to `{ name: string }` — as an argument, a variable initializer, or an `extends` clause. Only `readonly` *array/tuple* types get a dedicated check (TS4104); object members get none. The mutable alias then writes a field the source declared unwritable, so a value every reader is entitled to treat as fixed changes under them. With an actually frozen object (`Object.freeze` returns `Readonly<T>`, itself assignable back to `T`) the write is a runtime TypeError in strict mode.

```ts
function mutate(p: { name: string }): void {
  p.name = "changed";
}
function go(r: { readonly name: string }): void {
  mutate(r); // tsc: OK — r.name is readonly, yet written through p
}
```

**Test:** [tests/expect-error/pr437-set-check-unsound.ts](../tests/expect-error/pr437-set-check-unsound.ts), [tests/expect-error/readonly-inheritance.ts](../tests/expect-error/readonly-inheritance.ts), [tests/expect-error/readonly-inter-union.ts](../tests/expect-error/readonly-inter-union.ts) · **SKJS:** rejects — `error: Argument is not assignable to the parameter's type`, with `This would not be an error if this field were readonly` pointing at the mutable `name`; fields carry separate get/set types and a `readonly` field has `set = bottom` ([skjs-rules.md](../skjs-rules.md) rule 27)

### Mutable property covariance

tsc relates object properties covariantly regardless of writability: `{ v: string }` is assignable to `{ v: string | number }`, `Box<string>` to `Box<string | number>`, and a `{ x: 1 }` value may be stored in a field declared `{ x: number }`. No check is made that the target's write capability is safe for the source. A write through the widened alias stores a value the narrow type excludes; both views alias one object, so `const s: string = b.v` binds `42`. The object-literal form is the same hole with the alias created by the literal itself: `const o: { a: { x: number } } = { a: e }` then `o.a.x = 99` makes `e.x` read `99` at type `1`.

```ts
function widen(b: { v: string | number }): void {
  b.v = 42;
}
function go(b: { v: string }): void {
  widen(b); // tsc: OK — properties are covariant even when writable
  const s: string = b.v; // s holds 42 at runtime
}
```

**Test:** [tests/expect-error/pr437-edge-cases.ts](../tests/expect-error/pr437-edge-cases.ts), [tests/expect-error/pr437-set-check-unsound.ts](../tests/expect-error/pr437-set-check-unsound.ts), [tests/expect-error/readonly-hint.ts](../tests/expect-error/readonly-hint.ts), [tests/expect-error/suggest-readonly.ts](../tests/expect-error/suggest-readonly.ts), [tests/expect-error/obj-literal-var-field-growth.ts](../tests/expect-error/obj-literal-var-field-growth.ts), [tests/expect-error/obj-literal-indexes.ts](../tests/expect-error/obj-literal-indexes.ts) · **SKJS:** rejects — `Type 'number'` / `is not assignable to type 'string'` / `This would not be an error if this field were readonly`; the contravariant setter check fails, and making the field `readonly` drops the setter and the assignment is then accepted

### Mutable array (and Map/Set) element covariance

tsc measures `Array<T>` as covariant in `T` — its mutating members are methods, and methods are compared bivariantly (a documented `strictFunctionTypes` exemption) — so `string[]` is assignable to `(string | number)[]`, `number[]` to `unknown[]`, `Dog[]` to `Animal[]`, and `Map<string, string>` to `Map<string, string | number>`. `push`/`set` through the widened view stores an element the original element type excludes; a later read at the declared element type yields the wrong type. Both bindings alias one array.

```ts
function go(xs: string[]): void {
  const ys: (string | number)[] = xs; // tsc: OK — arrays are covariant
  ys.push(42);
  const s: string = xs[1]; // s holds 42 at runtime
}
```

**Test:** [tests/expect-error/instanceof-generic-skolem-args.ts](../tests/expect-error/instanceof-generic-skolem-args.ts), [tests/expect-error/unit.ts](../tests/expect-error/unit.ts), [tests/expect-error/pr437-edge-cases.ts](../tests/expect-error/pr437-edge-cases.ts) · **SKJS:** rejects — mutable arrays are invariant: `Type of value is not assignable to the variable's type annotation` / `Function parameter types are checked contravariantly: target parameter type 'number | string' must be assignable to source parameter type 'string'`; the `Map` form is rejected the same way

### A tuple is assignable to a mutable array of its element type

tsc treats `[number, number]` as a subtype of `number[]`, so a tuple can be aliased at the array type and then grown or shrunk through that alias while keeping its tuple type. Length-changing operations (`push`, `pop`, `splice`) break the tuple's arity: `tup.length` is statically the literal `2` and evaluates to `3`, and `const [x, y] = tup` no longer describes the value. The tuple type's central claim — exactly this many elements, at these positions — is falsified.

```ts
function go(): void {
  const tup: [number, number] = [1, 2];
  const a: number[] = tup; // tsc: OK
  a.push(3);
  const two: 2 = tup.length; // tup.length is 3 at runtime
}
```

**Test:** [tests/expect-error/destructuring-assignment.ts](../tests/expect-error/destructuring-assignment.ts), [tests/expect-error/readonly-rest-params.ts](../tests/expect-error/readonly-rest-params.ts) · **SKJS:** rejects — `Type '[number, number]' is not assignable to type { readonly concat: ...; readonly copyWithin: ...; ... }`; the tuple has positional fields, not the mutable number index `Array` requires

### Tuple types expose arity-changing Array methods

A tuple type inherits the whole mutable `Array` API, so `t.push(3)` / `t.pop()` / `t.splice(...)` are accepted directly on a `[number, number]` — no assignment or widening required — while `t.length` keeps the literal type `2`. Reads a tuple type is supposed to make total (`const [a, b] = t`, `t[1]`) stop describing the object, and `pop()` makes `t[1]` read as `number` when it is `undefined`. Logically independent of the tuple-to-array assignability hole: fixing either one leaves the other standing.

```ts
function go(t: [number, number]): void {
  t.push(3); // tsc: OK — the whole mutable Array API is on a tuple
  const two: 2 = t.length; // t.length is 3 at runtime
}
```

**Test:** [tests/expect-error/isarray-readonly.ts](../tests/expect-error/isarray-readonly.ts) · **SKJS:** rejects — `error: This index key is not assignable to the index signature: expected 'number', got 'string'`; a tuple has fixed positional fields and no mutable number index, so `push` is not available on it

### instanceof narrowing discards the scrutinee's readonly modifiers

When the class named on the right of `instanceof` is a subtype of the declared type, tsc replaces the declared type outright instead of intersecting. The class's own declaration says the field is mutable, so a `readonly` modifier the scrutinee carried disappears inside the guarded branch. `instanceof` is a runtime test about the prototype chain and says nothing about write permission, so the branch hands out write access the declared type explicitly withheld: `f(Object.freeze(new Cell()))` is also accepted by tsc, the frozen instance passes the guard, and the write throws `TypeError: Cannot assign to read only property 'a'`.

```ts
class Cell {
  a: string = "";
}
function f(o: { readonly a: string }): void {
  if (o instanceof Cell) {
    o.a = "x"; // tsc: OK — readonly erased by the instanceof narrowing
  }
}
```

**Test:** [tests/expect-error/instanceof-readonly-field.ts](../tests/expect-error/instanceof-readonly-field.ts) · **SKJS:** rejects — `Type 'string'` / `is not assignable to type 'never'`; the readonly field's setter is bottom and SKJS intersects rather than replaces, so the setter stays bottom through the narrowing ([skjs-rules.md](../skjs-rules.md): narrowing may restrict what can be written, never widen it) · **Issue:** SkipLabs/skjs#898

### An accessor's write type is dropped by assignability

tsc enforces a setter's parameter type on a direct write (`b.v = "hello"` on a `Box`-typed binding is TS2322), but when the same object is assigned to a plain property type it compares only the getter's read type. A class with `get v(): string` / `set v(x: number)` is therefore accepted as `{ v: string }`, and the write through that alias invokes the setter with a string — the very write tsc rejects when spelled directly on the `Box`.

```ts
class Box {
  n: number = 0;
  get v(): string {
    return String(this.n);
  }
  set v(x: number) {
    this.n = x;
  }
}
function go(): void {
  const o: { v: string } = new Box(); // tsc: OK — only the getter type is compared
  o.v = "hello"; // setter gets a string; this.n: number holds "hello"
}
```

**Test:** [skjs-rules.md](../skjs-rules.md) rule 27 · **SKJS:** on this exact spelling SKJS stops earlier at a feature gap — `error: Function 'v' must have an explicit return type annotation`. With SKJS's required spelling (`set v(x: number): void`, which tsc rejects as TS1095) SKJS rejects the aliasing assignment: `Type of value is not assignable to the variable's type annotation` + `This would not be an error if this field were readonly`; SKJS keeps separate get/set types per field

### A derived class may re-declare an inherited mutable member as readonly

Because `readonly` is not part of assignability, the derived-member compatibility check (TS2416, and TS2430 for the interface analogue) accepts a subtype that adds `readonly` to a member the base declares mutable, and the subtype stays assignable to the base. A base-typed alias then exposes the member as writable. tsc rejects `d.value = 99` written directly on the `Derived`-typed binding (TS2540) but accepts the identical mutation one line later through the widening alias.

```ts
class Base {
  value: number = 1;
}
class Derived extends Base {
  readonly value: number = 2;
}
function go(d: Derived): void {
  const b: Base = d; // tsc: OK
  b.value = 99; // writes through Derived's readonly field
}
```

**Test:** [tests/expect-error/readonly-inheritance.ts](../tests/expect-error/readonly-inheritance.ts) · **SKJS:** rejects — `error: This class incorrectly extends its base class`, with `This would not be an error if this field were readonly`; SKJS also rejects the widening `const b: Base = d` ([skjs-rules.md](../skjs-rules.md) rule 27)

## Narrowing & control flow

### A for increment preserves a stale pre-loop narrowing

Strict tsc accepts this read as `string`, although `continue` executes the
increment and the next iteration reads `null`:

```ts
function staleIncrementRead(x: string | null, again: boolean): void {
  if (x !== null) {
    for (; again; x = null) {
      const text: string = x;
      continue;
    }
  }
}
```

**Test:** [loop-carried-narrowing.ts](../tests/expect-error/loop-carried-narrowing.ts)
· **SKJS:** rejects the read by widening possibly assigned bindings at loop
entry. A condition that checks `x !== null` on every iteration remains usable.
The analogous while-body and for-of-body writes are rejected by strict tsc.


### A destructuring assignment default is treated as unconditional

TypeScript preserves a narrowing established by a write inside an assignment
default even though a supplied element skips the default. The declaration
form correctly keeps both paths.

```ts
function skippedAssignmentDefault(seed: number | undefined): number {
  let state: number | null = null;
  let value: number | undefined = 0;
  [value = (state = 1)] = [seed];
  return state; // null whenever seed is supplied
}
```

**Test:** [destructuring.ts](../tests/expect-error/destructuring.ts),
`skippedAssignmentDefaultKeepsPreviousValue` · **SKJS:** rejects the return;
the scope after a local default merges its effects with the untouched path.

### Array.isArray narrows to a mutable any[]

`Array.isArray` is declared `arg is any[]`, so its true branch type is a *mutable* array: a `readonly number[]` scrutinee narrows to a pushable array, a tuple loses its arity, and in a union like `number[] | { a: string; b: number }` the object arm is dropped in favour of the mutable arm. The guard proves only that the value is *an* array, never that it is mutable at its declared type. `a.push(1)` then mutates a value its declared type forbids mutating — a `TypeError: Cannot add property 2, object is not extensible` when the argument is frozen, which `readonly number[]` permits. The union form is unsound for a second reason: a plain object type can be inhabited at runtime by a readonly array carrying extra properties (`readonly number[] & { a: string; b: number }` is a legal argument), so dropping the object arm hands out a mutable view of a readonly array.

```ts
function go(a: readonly number[]): void {
  if (Array.isArray(a)) {
    a.push(1); // tsc: OK — narrowed to any[]; mutates a readonly array
  }
}
```

**Test:** [tests/expect-error/isarray-readonly.ts](../tests/expect-error/isarray-readonly.ts), [tests/expect-error/array-isarray-refinement.ts](../tests/expect-error/array-isarray-refinement.ts) · **SKJS:** rejects — `error: This index key is not assignable to the index signature: expected 'number', got 'string'`; `isArray` intersects with `ReadonlyArray<unknown>`, so only an already-mutable array keeps its writable index ([skjs-rules.md](../skjs-rules.md) rule 27b). For the union/object-arm variant SKJS reports `Property 'push' exists on some but not all members of the union type, so it may be absent` · **Issue:** SkipLabs/skjs#709

### instanceof ignores a custom static [Symbol.hasInstance]

tsc narrows `x instanceof C` to `C` in the then-branch (and subtracts `C` in the else-branch) purely from the nominal class, even when `C` declares or inherits a `static [Symbol.hasInstance]` returning plain `boolean`. That method *is* the runtime membership test and can return `true` for any value, so the branch is entered by a value with none of `C`'s members: `x.a` reads `undefined` at type `number`. The mirror case (`return false`) is equally broken — a real `C` reaches the else-branch, which tsc narrows to `never`, laundering it into any type.

```ts
class C {
  a: number = 1;
  static [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}
function f(x: unknown): number {
  if (x instanceof C) return x.a; // tsc: OK — x need not be a C
  return 0;
}
const n: number = f("not a C"); // runtime: undefined
```

**Test:** [tests/expect-error/instanceof-hasinstance.ts](../tests/expect-error/instanceof-hasinstance.ts) · **SKJS:** rejects — `error: Cannot access a property on type 'unknown'`; SKJS suppresses `instanceof` narrowing entirely when the right-hand class declares or inherits a static `[Symbol.hasInstance]` ([skjs-rules.md](../skjs-rules.md) rule 27c)

### instanceof else-branch narrows a structurally-typed class to never

In the false branch of `x instanceof C`, tsc subtracts `C` from the declared type; when the declared type *is* `C` the result is `never`, so any expression there is assignable to anything. But class types are structural in tsc, so a plain object literal is assignable to `C` without being an instance of it, and it reaches the else branch as a live value tsc typed `never`.

```ts
class C {
  a: number = 1;
}
function f(x: C): number {
  if (x instanceof C) return 0;
  return x; // tsc: OK — x is `never` here, yet a structural { a: 5 } lands here
}
const n: number = f({ a: 5 }); // runtime: { a: 5 }
```

**Test:** [tests/expect-error/instanceof-hasinstance.ts](../tests/expect-error/instanceof-hasinstance.ts) · **SKJS:** rejects — `Type 'C'` / `is not assignable to type 'number'`; SKJS never narrows the `instanceof` else-branch

### typeof x === "function" removes object constituents that callable values inhabit

In the `typeof x === "function"` branch tsc drops every non-function constituent: a non-union object type that is neither a supertype nor a subtype of `Function` (`{ a: number }`, an interface, a class-instance type) narrows to `never`, and in a union the object arm is dropped so the call is checked at the function arm's signature. A callable value carrying properties genuinely inhabits such a type — `Object.assign(() => {}, { a: 1 })` is accepted as a `{ a: number }` — and `typeof` on it is `"function"`, so the branch tsc declared unreachable is reached. Since `never` is assignable to everything, the value flows anywhere; in the union form it is instead called at an unrelated signature, so `call(bad)` computes `(1).length` and returns `undefined` from a `number`-typed slot.

```ts
function f(x: { a: number }): string {
  if (typeof x === "function") return x; // tsc: OK — x is `never` here
  return "";
}
function caller(): string {
  return f(Object.assign(() => {}, { a: 1 })); // returns a function, typed string
}
```

**Test:** [tests/expect-error/callability.ts](../tests/expect-error/callability.ts), [tests/expect-error/typeof.ts](../tests/expect-error/typeof.ts), [tests/expect-error/function-type.ts](../tests/expect-error/function-type.ts) · **SKJS:** rejects — `Type '{ a: number; }'` / `is not assignable to type 'string'`; SKJS keeps structural object arms in the `"function"` branch because such types admit callable inhabitants. On the union-call form it reports `This expression is not callable` / `may be callable, but its signature is unknown` ([skjs-rules.md](../skjs-rules.md) rule 27d)

### typeof x === "object" else-branch drops object types that primitives inhabit

In the *false* branch of `typeof x === "object"` tsc removes every object-typed union arm, so `number | { length: number }` narrows to `number`. A primitive inhabits a structural object type through its apparent type — `const s: { length: number } = "abc"` is accepted by tsc — and that value is `typeof "string"`, so it reaches the else branch where tsc has already concluded it must be the `number` arm.

```ts
function f(x: number | { length: number }): number {
  if (typeof x === "object") return 0;
  return x; // tsc: OK — a string inhabits { length: number }
}
const s: { length: number } = "abc";
const n: number = f(s); // runtime: "abc"
```

**Test:** [tests/expect-error/typeof.ts](../tests/expect-error/typeof.ts) · **SKJS:** rejects — `Type '{ length: number; }'` / `is not assignable to type 'number'` ([skjs-rules.md](../skjs-rules.md) rule 27d)

### `in` filters union arms although width subtyping allows the key anywhere

`"f" in x` on `{ f: number } | { g: number }` narrows `x` to `{ f: number }`: tsc treats the presence of a key as proof that the value belongs to the arm declaring it. But a declared object type is an open width-subtype, so a value of the `{ g: number }` arm may carry an excess `f` of a completely unrelated type — and excess properties survive assignment through a variable, which suppresses the freshness check.

```ts
function get(x: { f: number } | { g: number }): number {
  if ("f" in x) return x.f; // tsc: OK — the { g } arm may carry an f of any type
  return 0;
}
function attack(): number {
  const bad = { g: 1, f: "oops" };
  return get(bad); // "oops" typed number
}
```

**Test:** [tests/expect-error/in.ts](../tests/expect-error/in.ts) · **SKJS:** rejects — `error: Property 'f' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)`

### A user-defined type predicate's body is never checked against the claim

tsc accepts `x is T` on an implemented function and only requires the body to return something boolean-ish; it never checks that the returned condition implies `T`. Call sites narrow on the declared claim, so a lying implementation silently retypes values. This is an *intentional escape hatch* — a predicate is an assertion, like `as` — but the assertion is invisible at the use site: nothing at `if (isString(x))` marks it as unchecked.

```ts
function isString(x: unknown): x is string {
  return typeof x === "number"; // tsc: OK — body contradicts the claim
}
function f(x: unknown): number {
  if (isString(x)) return x.length;
  return 0;
}
const n: number = f(42); // runtime: undefined
```

**Test:** [tests/expect-error/type-predicate-requires-no-body.ts](../tests/expect-error/type-predicate-requires-no-body.ts), [tests/expect-error/type-predicate-syntax.ts](../tests/expect-error/type-predicate-syntax.ts), [tests/expect-error/gap-type-predicate-narrowing.ts](../tests/expect-error/gap-type-predicate-narrowing.ts) · **SKJS:** rejects — `error: A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature`

### A narrowing survives a call that invalidates it

tsc's control-flow analysis resets a narrowing only on a syntactic assignment to the same reference in the same function. Assignments performed inside a nested function body are not part of the enclosing function's flow graph, so a call that reassigns the narrowed local through a closure leaves the narrowing in force. `reset()` runs synchronously and sets `x` to `null` before the read, so `x`, statically `string`, is `null`. The property form is the same rule: after `if (x.f !== null) { sideEffect(); }`, `x.f` is still typed `number` although the callee may have written `null` through an alias. This is a well-known deliberate tsc trade-off.

```ts
function f(): string {
  let x: string | null = "hello";
  const reset = (): void => {
    x = null;
  };
  if (x !== null) {
    reset();
    return x; // tsc: OK — null at runtime
  }
  return "";
}
```

**Test:** [tests/expect-error/unsound-refinement.ts](../tests/expect-error/unsound-refinement.ts) · **SKJS:** also accepts — SKJS shares the hole; the repo files it under "Known-unsound refinements that SKJS currently accepts" · **Issue:** SkipLabs/skjs#599

### A `finally`'s writes are lost on jump edges that leave through it

tsc snapshots the flow state at a `break`/`continue` inside a `try` and uses that as the state arriving at the jump's target, without applying the writes the `finally` block performs on the way out. An `Eq<typeof x, "a">` probe confirms tsc types `x` as exactly `"a"` after the loop. But a jump out of a `try` runs its `finally` first, so if `c()` returns true even once, `x` is `"b"` at runtime while `y` is statically typed `"a"`.

```ts
function breakThroughFinally(c: () => boolean, a: "a", b: "b"): void {
  let x: "a" | "b" = a;
  while (c()) {
    try {
      break;
    } finally {
      x = b;
    }
  }
  const y: "a" = x; // tsc: OK — x holds "b" here at runtime
}
```

**Test:** [tests/expect-error/jump-through-finally.ts](../tests/expect-error/jump-through-finally.ts) · **SKJS:** rejects — `error: Type of value is not assignable to the variable's type annotation`, then `Type '"a" | "b"'` / `is not assignable to type '"a"'` / `Value '"b"' is missing`. The same pin covers `continue`, `break` out of a `switch`, and a conditional `finally` write

### Writes inside a nested try/catch are invisible to the enclosing catch's entry state

tsc builds a `catch` clause's entry state from the state before the `try` plus the assignments registered while binding the try block — but a nested `try` statement with its own `catch` replaces the exception target, so assignments inside it are registered only with the inner catch. The outer catch is entered with the pre-`try` state. The inner `try` completes normally with `y === "b"`, then `t()` throws, so the outer catch runs with `y === "b"`. The nested-try-with-catch is load-bearing: a plain assignment, a bare block, or a nested `try`/`finally` in its place all make tsc report TS2322, so this is a specific non-compositionality of catch entry states.

```ts
function nestedTryEscapesOuterCatch(a: "a", b: "b", t: () => void): void {
  let y: "a" | "b" = a;
  try {
    try {
      y = b;
    } catch {}
    t();
  } catch {
    const z: "a" = y; // tsc: OK — y holds "b" when t() throws
  }
}
```

**Test:** [tests/expect-error/catch-entry-writes.ts](../tests/expect-error/catch-entry-writes.ts) · **SKJS:** rejects — `error: Type of value is not assignable to the variable's type annotation`, then `Type '"a" | "b"'` / `is not assignable to type '"a"'` / `Value '"b"' is missing`

### Truthiness narrowing types the falsy part of `number` as the literal `0`

tsc types `a && b` as the definitely-falsy part of `a` unioned with `typeof b`, and maps the falsy part of the whole `number` type to the literal `0`; symmetrically the falsy branch of `if (n)` narrows `n` to `0`. `number` has three falsy values — `0`, `-0` and `NaN` — and `NaN` has no literal type, so `NaN && "x"` evaluates to `NaN` at a position typed `0 | string`. `Object.is(result, 0)` is false for a value the type says is the literal `0`, and `if (v !== 0) v.toUpperCase()` then type-checks and throws.

```ts
function firstFalsy(n: number, s: string): 0 | string {
  return n && s; // tsc: OK — firstFalsy(NaN, "x") returns NaN
}
```

**Test:** [tests/projects/truthiness-typescript/src/and-or.ts](../tests/projects/truthiness-typescript/src/and-or.ts) · **SKJS:** rejects — in the default `safe` truthiness mode the condition itself is refused: `error: A condition is expected to be of type boolean or a type with a single falsy value`. Under `--truthiness typescript` it still rejects the value: `Full type 'number'` / `is not assignable to specific type '0'`; SKJS deliberately keeps the whole `number` on the falsy side ([skjs-rules.md](../skjs-rules.md))

### Loose equality narrows across primitive kinds that coercion makes equal

tsc narrows by `==` exactly as it narrows by `===`: in the true branch of `x == 0` with `x: string | number` it drops the `string` arm. But `==` applies ToNumber coercion, so `"" == 0`, `"0" == 0` and `" " == 0` are all true and a `string` value survives into the branch typed `number`. Symmetrically `x == ""` narrows to `string` and `x == true` on `boolean | number` narrows to `boolean`.

```ts
function asNumber(x: string | number): number {
  if (x == 0) {
    return x; // tsc: OK — "" == 0, so x can still be a string
  }
  return 0;
}
```

**Test:** no pin — verified directly against tsc 6.0.3 · **SKJS:** rejects at parse time — `error: Unexpected '=='; use '===' instead (SKJS forbids loose equality)`. This is a parser-level lint rule, not a soundness-argued rejection: SKJS never reaches the narrowing question ([skjs-rules.md](../skjs-rules.md), parser-level lint rules)

## Object literals, spread & excess properties

### Fields written before an object spread keep their precise type

In `{ a: "", ...obj }` tsc overlays only the keys the spread source's *declared* type names, so a field written before the spread survives with its pre-spread type when the source type does not declare it: with `obj: {}` the result is typed `{ a: string }`. Object types are open under width subtyping, so `obj` can carry an own `a` at runtime, which the spread copies over the literal's `a`. The result's `a` is the number `1` while typed `string`, and `r.a.length` is `undefined`.

```ts
function probe(): string {
  const obj: {} = { a: 1 };
  const r = { a: "", ...obj };
  return r.a; // tsc: OK — typed string, holds the number 1
}
```

**Test:** [tests/expect-error/objects.ts](../tests/expect-error/objects.ts), [tests/expect-error/spread-union-distribute.ts](../tests/expect-error/spread-union-distribute.ts), [tests/expect-error/spread-boolean-object.ts](../tests/expect-error/spread-boolean-object.ts), [tests/expect-error/spread-union-fields.ts](../tests/expect-error/spread-union-fields.ts) · **SKJS:** rejects — `Type 'unknown'` / `is not assignable to type 'string'`; SKJS clears every field accumulated before a spread and a spread contributes `[string]: unknown` / `[symbol]: unknown` excess indexes, so `r.a` is `unknown`

### Object spread keeps interface methods that live on the prototype

tsc's spread type keeps every property of the source type except class-declared methods and private members. A method declared on an *interface* is kept, so `{ ...g }` for `g: Greeter` is typed `{ greet(): string }`. Spread copies only own enumerable properties, and a class instance inhabiting `Greeter` carries `greet` on its prototype, so the spread result has no `greet` at all: `Object.keys({...new C()})` is `[]` and the call throws. For a class-*typed* source tsc correctly yields `{}` (TS2741), so the carve-out simply does not cover interfaces.

```ts
interface Greeter {
  greet(): string;
}
class C {
  greet(): string {
    return "hi";
  }
}
function probe(): string {
  const g: Greeter = new C();
  return { ...g }.greet(); // tsc: OK — TypeError at runtime; greet is on the prototype
}
```

**Test:** no pin for the prototype-method case — [tests/expect-error/spread-callable.ts](../tests/expect-error/spread-callable.ts) covers call/construct signatures being dropped by spread · **SKJS:** also accepts — SKJS shares the hole

## Index signatures

### Implicit index signature for anonymous and type-alias object types

tsc synthesizes an implicit index signature for object types that are not interfaces or classes (type-alias type literals, fresh object-literal types, spread results) whose declared member types fit, so `type Named = { a: string }` is assignable to `{ [k: string]: string }` — and `{ readonly a: number }` to the recursive `{ readonly [k: string]: Json }` shape every plain-object/JSON type uses. The identical assignment from an `interface` is rejected (TS2322, "Index signature for type 'string' is missing"), so the hole is specific to anonymous and aliased object types. The source type is open: the value may carry keys the type never named, of arbitrary type. Viewing it as indexed reads those keys at the index value type — `toIndexed(v)["extra"]` is typed `string` and holds `42`; in the `Json` form the extra key holds a function, which `Json` excludes. Written through, the index view also lets an unrelated key be assigned at the index value type, corrupting a field the original view reads at a different type.

```ts
type Named = { a: string };
function toIndexed(n: Named): { [k: string]: string } {
  return n; // tsc: OK — type-alias object types get an implicit index signature
}
function probe(): string {
  const v = { a: "x", extra: 42 };
  return toIndexed(v)["extra"]; // typed string, holds 42
}
```

**Test:** [tests/expect-error/index-signatures.ts](../tests/expect-error/index-signatures.ts), [tests/expect-error/obj-literal-indexes.ts](../tests/expect-error/obj-literal-indexes.ts), [tests/expect-error/numeric-field-number-index.ts](../tests/expect-error/numeric-field-number-index.ts), [tests/expect-error/json-named-object-type.ts](../tests/expect-error/json-named-object-type.ts), [tests/expect-error/closed-type.ts](../tests/expect-error/closed-type.ts), [examples/src/recursive-json-type.ts](../examples/src/recursive-json-type.ts) · **SKJS:** rejects — `Type '{ a: string; }'` / `is not assignable to type '{ [k: string]: string; }'` / `Missing index signature 'k' in source type`. Object-literal *values* are still accepted (every concrete field is checked against the index value type); the `Closed<T>` type constructor is the sound opt-in ([skjs-rules.md](../skjs-rules.md) rules 28 and 28b) · **Issue:** SkipLabs/skjs#660

### Index-signature reads never include `undefined`

Under plain `--strict`, `x["a"]` on `{ [k: string]: number }` is typed exactly `number`; the possibility that the key is absent is dropped. The same applies to array element reads, the numeric index on `String`, and `Record<K,V>`. `{}` inhabits `{ [k: string]: number }`, so the read evaluates to `undefined` while the static type says `number`, and dereferencing it throws. `--noUncheckedIndexedAccess` reports `TS2322: Type 'number | undefined' is not assignable to type 'number'` — tsc itself agrees the value can be `undefined`, it is just not surfaced under `--strict`.

```ts
function readMissingKey(x: { [k: string]: number }): number {
  return x["a"]; // tsc: OK — x = {} makes this undefined, statically number
}
```

**Test:** [tests/expect-error/index-signatures.ts](../tests/expect-error/index-signatures.ts) · **SKJS:** rejects — `Type 'undefined'` / `is not assignable to type 'number'`; SKJS types every index read as `valueType | undefined` unconditionally ([skjs-rules.md](../skjs-rules.md) rule 28, "Bracket access")

### A union branch's index signature supplies a named key with no `undefined`

For `{ a: number } | { [k: string]: number }`, tsc resolves `x["a"]` to `number`: the first branch has the declared field, and the index branch is silently assumed to have the key too. A value of the second branch (e.g. `{}`) has no `a`, so the read is `undefined` at type `number`. Distinct from the plain index read: `--noUncheckedIndexedAccess` does *not* recover the `| undefined` here, so no compiler flag closes it.

```ts
function f(x: { a: number } | { [k: string]: number }): number {
  return x["a"]; // tsc: OK — the indexed branch need not have key "a"
}
```

**Test:** [tests/expect-error/union-index-access.ts](../tests/expect-error/union-index-access.ts) · **SKJS:** rejects — `Type 'undefined'` / `is not assignable to type 'number'`; SKJS resolves the key per branch and the index branch contributes `| undefined`

### Mutable index signatures are compared covariantly in their value type

tsc checks index signatures covariantly regardless of the `readonly` modifier, so `{ [k: string]: number }` is assignable to `{ [k: string]: number | string }` even though both are writable. Through the widened alias any key can be stored with a `string`; every read through the original view then claims `number` for a string. This is the classic mutable-container covariance hole, exactly analogous to array covariance.

```ts
function bad(n: { [k: string]: number }): void {
  const w: { [k: string]: number | string } = n; // tsc: OK
  w["x"] = "oops"; // stores a string in a number-indexed object
}
```

**Test:** [tests/expect-error/index-signatures.ts](../tests/expect-error/index-signatures.ts), [tests/expect-error/index-signatures-ops.ts](../tests/expect-error/index-signatures-ops.ts) · **SKJS:** rejects — `Type 'string'` / `is not assignable to type 'number'` / `This would not be an error if this field were readonly`; SKJS gives indexes separate get/set types, so the setter direction is checked contravariantly ([skjs-rules.md](../skjs-rules.md) rule 28)

### `readonly` on an index signature is erased by assignment to a mutable index type

tsc rejects a direct write through a readonly index (TS2542, "Index signature ... only permits reading") but assigns `{ readonly [k: string]: number }` to `{ [k: string]: number }` freely, laundering the modifier away. Because arrays carry a number index, `readonly number[]` is likewise assignable to `{ [k: number]: number }` — so the one special case tsc does have (TS4104 for `readonly T[]` -> `T[]`) is bypassed by a single intermediate annotation, and the write mutates the caller's readonly array. Distinct from the covariance hole above: here the value types are identical and only the modifier changes.

```ts
function go(a: readonly number[]): void {
  const m: { [k: number]: number } = a; // tsc: OK — readonly erased
  m[0] = 5; // mutates a readonly array
}
```

**Test:** [tests/expect-error/object-type-readonly-fields.ts](../tests/expect-error/object-type-readonly-fields.ts), [tests/expect-error/index-signatures-ops.ts](../tests/expect-error/index-signatures-ops.ts) · **SKJS:** rejects — `Type 'number'` / `is not assignable to type 'never'` pointing at `ReadonlyArray`'s index in the stubs, plus `This would not be an error if this field were readonly`; a readonly index's setter is `never` ([skjs-rules.md](../skjs-rules.md) rule 28)

### Non-literal index writes ignore the declared fields the key could name

For `x[k] = v` with a non-literal `k`, tsc checks `v` only against the index signature's value type. The declared properties `k` could name at runtime — `readonly` ones, and ones typed narrower than the index value type — are not consulted, though tsc *does* reject the same write with a literal key (TS2540 / TS2322). `k` can be `"a"`, storing `"z"` into a property declared `1`, so the immediately following `x.a` read is typed `1` while holding a string; with a `readonly` field in range the write goes through a field the type declares unwritable, and every holder of that type can observe it change.

```ts
function bad(x: { a: 1; [k: string]: string | number }, k: string): 1 {
  x[k] = "z"; // tsc: OK — only the index signature is checked
  return x.a; // typed `1`, may hold "z" at runtime
}
```

**Test:** [tests/expect-error/index-signatures.ts](../tests/expect-error/index-signatures.ts) · **SKJS:** rejects — `error: Type is not assignable to the assignment target's type` / `Type 'string'` / `is not assignable to type '1'`. SKJS intersects the index setter with every reachable declared-field setter; a `readonly` field contributes a `never` setter, making the write unsatisfiable ([skjs-rules.md](../skjs-rules.md) rule 28)

### Writes through a union-typed receiver use the union, not the intersection, of the arms' setters

For an assignment target whose receiver is a union, tsc computes a single property/index type as the *union* of the per-arm types and checks the assigned value against it — the same type it uses for reads. Exactly one arm describes the runtime value, so if `x` is the `{ [k: number]: string }` arm the write stores `42` in a slot every reader of that type is promised holds a `string`, and a later `x[0].toUpperCase()` crashes. A sound write must satisfy the *intersection* of the arms' setters. Not array-specific: the named-property form `function f(x: { a: number } | { a: string }) { x.a = 42; }` is accepted too.

```ts
function f(x: number[] | { [k: number]: string }): void {
  x[0] = 42; // tsc: OK — if x is the index arm, a number lands in a string slot
}
```

**Test:** [tests/expect-error/array-object-union-operations.ts](../tests/expect-error/array-object-union-operations.ts), [tests/expect-error/index-signatures.ts](../tests/expect-error/index-signatures.ts) · **SKJS:** rejects — `Type 'number'` / `is not assignable to type 'number & string'` ([skjs-rules.md](../skjs-rules.md) rule 28, "Union: getter = union, setter = intersection")

### A read through a `never`-valued index signature is silently typed `never`

Intersecting two index signatures with incompatible value types produces an index whose value type is `never`. tsc still resolves a key through it and types the read `never`, with no diagnostic — and `never` is a subtype of every type, so the result satisfies any annotation. The intersection is inhabited (`{}` satisfies both arms, and tsc accepts `function mk(): A & B { return {}; }`), and no object can hold a key that is both a number and a string, so the read always yields `undefined`. That `undefined` is laundered into an arbitrary annotation with no cast and no error.

```ts
type A = { [k: string]: number };
type B = { [k: string]: string };
function mk(): A & B {
  return {};
}
function f(x: A & B): symbol {
  return x["key"]; // tsc: OK — typed `never`; at runtime it is undefined
}
```

**Test:** [tests/expect-error/index-signatures-ops.ts](../tests/expect-error/index-signatures-ops.ts) · **SKJS:** rejects — `error: Property 'key' does not exist on this type` / `The object type is closed: its unnamed keys are provably absent`; reading a provably-valueless key is an error rather than a silent `never` ([skjs-rules.md](../skjs-rules.md) rule 28b, "Never-index principle")

## Optional fields & definite assignment

### An optional field is satisfied by a source type that never mentions the key

tsc treats `{ a: number }` as assignable to `{ a: number; b?: string }`: the optional `b` is considered absent because the source type does not declare it, and later reads of `.b` are typed `string | undefined`. The source type is open, so the value may carry an own `b` of an unrelated type — excess properties survive assignment through a variable, which suppresses the freshness check. The optional-field view then reads that value at the wrong type: `string | undefined` holding `42`, so `.toUpperCase()` on the non-undefined branch throws. The intermediate widening is load-bearing: `const foo: { a: number; b?: string } = { a: 1, b: 42 }` directly is correctly rejected with TS2322.

```ts
function widen(x: { a: number }): { a: number; b?: string } {
  return x; // tsc: OK — an absent key satisfies the optional `b`
}
function probe(): string | undefined {
  const v = { a: 1, b: 42 };
  return widen(v).b; // typed string | undefined, holds 42
}
```

**Test:** [tests/expect-error/objects.ts](../tests/expect-error/objects.ts), [tests/expect-error/optional-field-omitted.ts](../tests/expect-error/optional-field-omitted.ts), [tests/expect-error/spread-union-fields.ts](../tests/expect-error/spread-union-fields.ts), [tests/expect-error/spread-union-distribute.ts](../tests/expect-error/spread-union-distribute.ts) · **SKJS:** rejects — `Type '{ a: number; }'` / `is not assignable to type '{ a: number; b?: string; }'` / `The field 'b' is missing`

### Optional properties are not exact: a present `undefined` flows through a spread into a required field

Without `--exactOptionalPropertyTypes` (not part of `--strict`), tsc conflates "key absent" with "key present holding `undefined`": `{ a: undefined }` is an accepted `{ a?: number }`. Object-spread typing then relies on the *exact* reading — `{ a: 1, ...x }` with `x: { a?: number }` is typed `{ a: number }` on the assumption that an absent `a` leaves the `1` in place. A present-but-undefined `a` is copied by the spread and overwrites it, so the result's `a` is `undefined` at a required `number` field. Adding `--exactOptionalPropertyTypes` closes this one (TS2379), which is exactly the evidence that plain `--strict` leaves it open.

```ts
function g(x: { a?: number }): { a: number } {
  return { a: 1, ...x };
}
export const r: { a: number } = g({ a: undefined }); // tsc: OK — r.a is undefined
```

**Test:** [tests/expect-error/optional-fields-exact.ts](../tests/expect-error/optional-fields-exact.ts) · **SKJS:** rejects — `Type 'undefined'` / `is not assignable to type 'number'`; SKJS applies the exact reading unconditionally ([skjs-rules.md](../skjs-rules.md) rule on optional fields)

### An index signature whose values include `undefined` satisfies an optional property

tsc accepts `{ [k: string]: T | undefined }` as a source for a target declaring `f?: T`, treating the index's `undefined` as if it could only mean absence. The index source can hold `f` as a *present* key whose value is `undefined` (tsc accepts `const src: { [k: string]: number | undefined } = { f: undefined }`), so spreading it into a required slot yields an object whose `f` is `undefined` while typed `number`. Unlike the literal case above, `--exactOptionalPropertyTypes` does *not* close this one.

```ts
function g(x: { f?: number }): { f: number } {
  return { f: 1, ...x };
}
export function go(): { f: number } {
  const src: { [k: string]: number | undefined } = { f: undefined };
  return g(src); // tsc: OK — the result's `f` is undefined, typed number
}
```

**Test:** [tests/expect-error/optional-fields-exact.ts](../tests/expect-error/optional-fields-exact.ts) · **SKJS:** rejects — `Type 'undefined'` / `is not assignable to type 'number'`

### `delete` through a required-to-optional widening removes a required property

tsc accepts `{ f: number }` as a subtype of `{ f?: number }`, and `delete a.f` is legal on that view. After the call the object still has static type `{ f: number }` but the key no longer exists, so `b.f` reads `undefined` at a position typed `number`. Accepted under `--strict` and under `--exactOptionalPropertyTypes`.

```ts
function del(a: { f?: number }): void {
  delete a.f; // legal: `f` is optional on this view
}
export function go(): number {
  const b: { f: number } = { f: 1 };
  del(b); // tsc: OK — { f: number } widens to { f?: number }
  return b.f; // typed number, undefined at runtime
}
```

**Test:** [tests/expect-error/obj-literal-var-field-growth.ts](../tests/expect-error/obj-literal-var-field-growth.ts) · **SKJS:** rejects only incidentally — `delete` is unimplemented, so it reports `error: Cannot find name` on the `delete a.f` line. The required-to-optional widening itself is accepted by SKJS, so this hole would open if `delete` were supported

### Definite-assignment analysis stops at function boundaries

tsc's TS2454 "used before being assigned" check applies only within the declaring execution scope. A read of an unassigned `let x: number` from inside a nested function or arrow body is not flagged at all — tsc types it as bare `number`, however early the closure is actually invoked. The arrow is called before `x = 1` runs, so `undefined` is returned from a `number`-typed slot.

```ts
export function f(): number {
  let x: number;
  const g = (): number => x; // tsc: OK — no TS2454; x is undefined at this read
  const n = g();
  x = 1;
  return n; // undefined, typed number
}
```

**Test:** no pin for the closure-boundary case — [tests/expect-error/definite-assignment-undefined-boundary.ts](../tests/expect-error/definite-assignment-undefined-boundary.ts) and [tests/expect-error/jump-edge-definite-assignment.ts](../tests/expect-error/jump-edge-definite-assignment.ts) pin the intra-function case, which tsc does flag · **SKJS:** rejects — `error: Variable 'x' is used before being assigned`, reported at the read inside the arrow body

## Functions, callability & this

### Method-syntax parameter bivariance

`strictFunctionTypes` makes parameters contravariant only in *function-type* positions; members written with method syntax (`m(x: T): R` in an interface, object type literal, or class) are still compared bivariantly. This is a documented, deliberate exemption. It has three consequences: an object whose method accepts `number` is accepted where a method accepting `number | string` is required; a subclass may narrow an inherited method's parameter and the instance stays assignable to the base type (the derived-class check TS2416 shares the exemption); and a type parameter occurring only in method parameter positions is measured bivariantly, so `Coll<string>` is assignable to `Coll<string | number>` and `c.get(42)` reaches a body written for a `string` key. Rewriting the same members with property/function-type syntax makes tsc reject all three with TS2322/TS2416, confirming bivariance is the sole cause.

```ts
declare const n: { handle(x: number): void };
const w: { handle(x: number | string): void } = n; // tsc: OK — method params are bivariant
function boom(): void {
  w.handle("s"); // handle's body sees a string where it declared number
}
```

**Test:** [tests/expect-error/function-subtyping.ts](../tests/expect-error/function-subtyping.ts), [tests/expect-error/json-generated-service.ts](../tests/expect-error/json-generated-service.ts), [tests/expect-error/mutable-class-overrides.ts](../tests/expect-error/mutable-class-overrides.ts) · **SKJS:** rejects — `Type 'string'` / `is not assignable to type 'number'`, with `Function parameter types are checked contravariantly: target parameter type 'number | string' must be assignable to source parameter type 'number'`. On the class-override form: `error: This class incorrectly extends its base class`, and SKJS also rejects the base-typed widening

### `this` parameters are compared bivariantly in method-syntax members

For a method-syntax member tsc relates the two `this` types in either direction, so `{ m(this: Derived): R }` is assignable to `{ m(this: Base): R }`. The same relation written with property syntax or as a bare function type is correctly rejected as contravariant (TS2322, "The 'this' types of each signature are incompatible"), so this is method-syntax-specific bivariance, not the no-`this` erasure rule below. The narrowed receiver requirement is laundered away: a plain `Base` is accepted as the receiver of a body that reads `this.extra`.

```ts
class Base {
  tag: string = "b";
}
class Derived extends Base {
  extra: number = 1;
}
const i = {
  m(this: Derived): number {
    return this.extra;
  },
};
const j: { m(this: Base): number } = i; // tsc: OK — method `this` is bivariant
const n: number = j.m.call(new Base()); // body reads this.extra; Base has none
```

**Test:** [tests/expect-error/this-parameter-subtyping.ts](../tests/expect-error/this-parameter-subtyping.ts) pins the contravariant rejection for a bare function type; the method-syntax bivariance itself has no dedicated pin · **SKJS:** rejects — `Their this parameters are not compatible` / `Type '{ tag: string; }'` / `is not assignable to type '{ extra: number; tag: string; }'` / `The field 'extra' is missing`

### A no-`this` target type is a free-call permit, and assignability skips the check

When the target signature declares no `this` parameter, tsc skips the `this`-compatibility comparison entirely, so a function that genuinely requires a receiver is assignable to `() => void` and the result is typed as freely callable. The operative factor is the target's *absence* of a `this` parameter, not its syntax: a bare function type, a property-syntax member and a method-syntax member all accept the same laundering. Free-calling the result runs the body with `this === undefined` (TypeError on the first field read). The erasure also survives *attachment*: laundering into a member slot and calling `s.m()` supplies the carrier object as `this`, which need not satisfy the erased requirement.

```ts
declare const fnBase: (this: { tag: string }) => void;
const b: () => void = fnBase; // tsc: OK — the target declares no `this`
b(); // body runs with this === undefined
```

**Test:** [tests/expect-error/this-parameter-subtyping.ts](../tests/expect-error/this-parameter-subtyping.ts), [tests/expect-error/this-parameter-void-receiver.ts](../tests/expect-error/this-parameter-void-receiver.ts), [tests/expect-error/this-parameter-shape-methods.ts](../tests/expect-error/this-parameter-shape-methods.ts) · **SKJS:** rejects — `Their this parameters are not compatible` / `Type 'unknown'` / `is not assignable to type '{ tag: string; }'` ([skjs-rules.md](../skjs-rules.md), "A no-`this` function type is a free-call permit") · **Issue:** SkipLabs/skjs#993

### A method's implicit receiver is absent from its type

For a method declared without an explicit `this` — a class method, an interface or shape method-syntax member, or a lib method — tsc records no receiver requirement in the method's type. `const g = c.m` is typed `() => number` and `g()` is accepted, as is passing `c.m` where a `() => number` callback is expected, and `c.m.call(x)` accepts any receiver because `ThisParameterType` resolves to `unknown`. The body reads the instance's fields off `this`, but a free call supplies `undefined`: `g()` throws `TypeError: Cannot read properties of undefined` although its type says it returns a `number`.

```ts
class C {
  v: number = 1;
  m(): number {
    return this.v;
  }
}
function f(c: C): number {
  const g = c.m; // tsc: OK — typed `() => number`, receiver requirement gone
  return g(); // runtime TypeError, this === undefined
}
```

**Test:** [tests/expect-error/this-parameter-implicit-class.ts](../tests/expect-error/this-parameter-implicit-class.ts), [tests/expect-error/this-parameter-lifted.ts](../tests/expect-error/this-parameter-lifted.ts), [tests/expect-error/this-parameter-shape-methods.ts](../tests/expect-error/this-parameter-shape-methods.ts), [tests/expect-error/this-parameter-bind-call-apply.ts](../tests/expect-error/this-parameter-bind-call-apply.ts) · **SKJS:** rejects — `error: The 'this' context is not assignable to method's 'this' type` / `Type 'void'` / `is not assignable to type 'C'`; for an object-shape method the message is `A shape method can only be called on the object it was accessed on` ([skjs-rules.md](../skjs-rules.md), "Detached method calls are rejected")

### A `this: undefined` body types `this` as `undefined` although the receiver can be anything

tsc treats `this: void` / `this: undefined` as receiver-less for assignability, so such a function is assignable to `() => R`, yet it still types `this` inside the body as `undefined`/`void`. Nothing then enforces the `undefined` receiver at the call site: once laundered, the value can be installed as an object member and called attached, which supplies the carrier as `this`. A body that returns `this` hands back an object through a slot typed `undefined`, so `u === undefined` is statically always-true and actually false. Not subsumed by the free-call-permit hole — such a function is legitimately receiver-independent as far as assignability goes.

```ts
function f(this: undefined): undefined {
  return this;
}
const g: () => undefined = f;
const o = { m: g };
const u: undefined = o.m(); // tsc: OK — `u` is the object `o` at runtime
```

**Test:** [tests/expect-error/this-parameter-void-receiver.ts](../tests/expect-error/this-parameter-void-receiver.ts) · **SKJS:** rejects at the body's `this` read — `error: 'this' is not available in this context`; SKJS keeps the receiver-less assignment legal and instead forbids observing `this` in such a body ([skjs-rules.md](../skjs-rules.md))

### Calling a `Function`-typed value yields an implicit `any`

`Function` proves callability without supplying a signature, yet tsc permits `f(...)` on a `Function`-typed value with arbitrary arguments and types the result `any` — silently, under `--strict`, which includes `noImplicitAny`. Neither the arguments nor the result are checked, so whatever the call returns is laundered into any annotation. The same `Function` type is what `typeof x === "function"` narrows `unknown` to, making the hole reachable from a guard alone. The program contains no `any`, `as` or `!`: the implicit `any` is injected by the built-in type itself.

```ts
function probe(f: Function): string {
  return f(); // tsc: OK — unchecked call, result typed implicit `any`
}
```

**Test:** [tests/expect-error/function-type.ts](../tests/expect-error/function-type.ts) · **SKJS:** rejects — `error: This expression is not callable` / `Type 'Function' is callable, but its signature is unknown` ([skjs-rules.md](../skjs-rules.md) rule 27d)

### Overload signatures are only loosely checked against the implementation signature

tsc relates each overload signature to the implementation signature with a deliberately relaxed rule: the implementation's return type need only be *comparable* to, not assignable to, the overload's return type. An implementation returning `number | string` is accepted under an overload declared to return `number`, and call sites resolve against the overload, so `f()` is typed `number` while the body returns `"oops"`.

```ts
function f(): number;
function f(): number | string {
  return "oops"; // tsc: OK — only "comparable" to the overload's return type
}
function boom(): void {
  const n: number = f(); // holds "oops" at runtime
}
```

**Test:** no pin for the tsc hole — [skjs-rules.md](../skjs-rules.md) rule 10 pins only that SKJS has no overload support · **SKJS:** rejects with `error: Duplicate identifier 'f'` — a feature gap (overloads are unsupported), not a soundness argument

## Generics & type parameters

### instanceof on a generic class binds the hidden type arguments to `any`

`x instanceof Box` for a generic `Box<T>` narrows `x` to `Box<any>` (and `x instanceof Array` to `any[]`): tsc erases the runtime object's unknown hidden type arguments rather than representing them. Every member typed `T` then reads at any type and accepts a write of any value, with no implicit-any error under `--strict`. But `instanceof` proves the object has *some* type argument, not which one, so the write stores a string in a `Box<number>` and every later read of `.v` at `number` is a false claim. The user writes no `any`, `as` or `!` — tsc synthesizes the `any` from the narrowing itself.

```ts
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}
function corrupt(x: unknown): void {
  if (x instanceof Box) x.v = "s"; // tsc: OK — x narrows to Box<any>
}
function go(b: Box<number>): number {
  corrupt(b);
  return b.v; // "s" at runtime
}
```

**Test:** [tests/expect-error/instanceof-generic-skolem-args.ts](../tests/expect-error/instanceof-generic-skolem-args.ts), [tests/expect-error/tparam-name-collision.ts](../tests/expect-error/tparam-name-collision.ts) · **SKJS:** rejects — `Type 'string'` / `is not assignable to type 'Box#T'`; each hidden argument is a fresh rigid witness ([skjs-rules.md](../skjs-rules.md))

### instanceof drops a union arm a value can inhabit, keeping the survivor's declared type arguments

For `o: { a: number } | Box<string>`, `o instanceof Box` filters the union by assignability to `Box<any>`; the object arm has no `v`, so it is discarded entirely rather than intersected, and `o` narrows to exactly `Box<string>` — keeping the surviving arm's *declared* type argument. Width subtyping lets a value satisfy the `{ a: number }` arm *and* be a `Box` at a different type argument, so `read(new Both(7))` returns the number `7` from a function typed to return `string`. Distinct from the `Box<any>` hole: here tsc commits to a specific *wrong* type argument.

```ts
class Box<T> {
  constructor(public v: T) {}
}
class Both extends Box<number> {
  a: number = 1;
}
function read(o: { a: number } | Box<string>): string {
  if (o instanceof Box) return o.v; // tsc: OK — { a: number } arm dropped
  return "";
}
function boom(): string {
  return read(new Both(7)); // the number 7, typed string
}
```

**Test:** [tests/expect-error/instanceof-generic-skolem-args.ts](../tests/expect-error/instanceof-generic-skolem-args.ts) · **SKJS:** rejects — `Type 'string | Box#T'` / `is not assignable to type 'string'`; SKJS keeps the object arm as `arm & Box<T#>`

### A tuple satisfies a mutable-array constraint, so the body can break the caller's arity

For `function grow<T extends number[]>(...args: T): T`, tsc infers `T` at the call site as a *tuple* — `grow(1,2,3)` gives `T = [number, number, number]`, so the result's `length` has the literal type `3` — while inside the body `args: T` gets the apparent type of its constraint `number[]`, which has `push`. The push mutates the very array handed back as a 3-tuple. Not caused by the rest parameter: `function f<T extends number[]>(a: T): T { a.push(9); return a; }` called as `f<[number, number]>([1, 2])` is equally clean. tsc lets a tuple satisfy a mutable-array constraint, so operations legal at the constraint break the instantiation's arity invariant.

```ts
function grow<T extends number[]>(...args: T): T {
  args.push(999); // legal at the constraint `number[]`
  return args;
}
function go(): 3 {
  return grow(1, 2, 3).length; // tsc: OK — T = [number, number, number]; 4 at runtime
}
```

**Test:** [tests/expect-error/generic-spread-params.ts](../tests/expect-error/generic-spread-params.ts) · **SKJS:** rejects the declaration — `error: A rest parameter's constraint must use ReadonlyArray (or 'readonly T[]'), since rest parameters are readonly` / `This constraint uses a mutable Array type`. On the non-rest variant it rejects the instantiation: `Type argument does not satisfy the constraint` / `It does not satisfy the constraint: 'number[]'`

### Type-argument constraint checking ignores `readonly`, then the body writes through the type parameter

tsc checks a type argument against its constraint with ordinary assignability, which discards `readonly`: `string` satisfies `T extends { length: number }` because `String.length` (declared `readonly`) is assignable to a mutable `length: number`. Inside the body a `T`-typed value's members are typed at the constraint, so `x.length = 0` is a legal write — executed on a primitive string whose `length` is non-writable, which throws `TypeError: Cannot assign to read only property 'length'` under the strict-mode semantics tsc emits for modules. The underlying rule is plain readonly-to-mutable property assignability (the same hole exists non-generically as `const h: { length: number } = "hello"; h.length = 0;`); the constraint check is the vehicle.

```ts
export {};
interface HasLength {
  length: number;
}
function shrink<T extends HasLength>(x: T): void {
  x.length = 0; // write at the constraint's mutable type
}
function go(): void {
  shrink("hello"); // tsc: OK — T = string, whose length is readonly
}
```

**Test:** [tests/expect-error/duplicate-constraint-add.ts](../tests/expect-error/duplicate-constraint-add.ts) · **SKJS:** rejects the call — `Type 'string'` / `is not assignable to type '{ length: number; }'`; the body's write is accepted, SKJS blocks the instantiation instead ([skjs-rules.md](../skjs-rules.md) rule 27)

## Classes, interfaces & declarations

### A base constructor can call an overridden method before derived fields are initialized

tsc type-checks the override's body against the declared field types and applies `strictPropertyInitialization` only at the declaration site; it models no ordering of effects. Derived field initializers run only after `super()` returns, so when `Base`'s constructor dispatches virtually to `Derived.init`, `this.x` does not exist yet: it is `undefined` while statically typed `number`, and `this.x.toFixed(2)` throws. Under `--target es2022` (`useDefineForClassFields` on by default) the field is not even an own property at that point.

```ts
class Base {
  constructor() {
    this.init();
  }
  init(): void {}
}
export class Derived extends Base {
  x: number = 1;
  init(): void {
    const s: string = this.x.toFixed(2); // tsc: OK — this.x is undefined here
  }
}
```

**Test:** no pin · **SKJS:** also accepts — SKJS shares this hole

### `new this()` in a static method ignores subclass constructor signatures

Inside a static method tsc types `this` as the class's static side and checks `new this()` against the *declaring* class's construct signature. A derived class's constructor is never required to be compatible with its base's, so `B.make()` type-checks even though `B`'s constructor demands an argument. tsc *does* reject the explicit spelling — `const f: typeof A = B` gives TS2322, "Target signature provides too few arguments" — so polymorphic static `this` is the channel that skips exactly that check. `A.make` runs with `this === B`, so `new B()` gets `n === undefined` and `tag()` throws.

```ts
class A {
  static make(): A {
    return new this(); // tsc: OK — checked against A's constructor
  }
  tag(): string {
    return "a";
  }
}
class B extends A {
  n: number;
  constructor(n: number) {
    super();
    this.n = n;
  }
  tag(): string {
    return this.n.toFixed(2);
  }
}
function go(): string {
  return B.make().tag(); // this.n is undefined
}
```

**Test:** [tests/expect-error/this-parameter-static.ts](../tests/expect-error/this-parameter-static.ts) · **SKJS:** rejects — `error: This expression is not constructable` / `'void' is not an object`; SKJS gives a static method no `this` at all, so `new this()` never type-checks. SKJS additionally closes the underlying hole by rule ([skjs-rules.md](../skjs-rules.md): child class constructors must have the same signature as the parent), but its rejection of this repro is the no-`this`-in-statics gap

### An interface merged into a class invents members with no runtime existence

Declaration merging lets an `interface C` in the same file add members to `class C`. tsc adds `b: string` to the instance type and never checks that anything assigns it — the merged member is exempt from `strictPropertyInitialization` (TS2564), the check that otherwise makes class fields sound under `--strict`. No `declare`, `any`, `as` or `!` appears anywhere, yet `c.b` is typed `string`, is `undefined` at runtime, and `c.b.length` throws.

```ts
class C {
  a: number = 1;
}
interface C {
  b: string; // tsc: OK — merged member, exempt from TS2564
}
function f(c: C): number {
  return c.b.length; // c.b is undefined at runtime
}
```

**Test:** [tests/expect-error/duplicate-def.ts](../tests/expect-error/duplicate-def.ts), [tests/expect-error/interface-as-value.ts](../tests/expect-error/interface-as-value.ts), [tests/expect-error/class-extends-interface.ts](../tests/expect-error/class-extends-interface.ts) · **SKJS:** rejects — `error: Duplicate identifier 'C'` / `Duplicate class declaration 'C'`; SKJS does not implement class/interface declaration merging, so its rejection is a feature gap rather than a deliberate soundness stance

## Enums

### `number` is assignable to a numeric enum type

tsc accepts an arbitrary non-literal `number` expression wherever a numeric enum type is expected — the whole enum type `E` and even a single-member type like `E.A`. This is a deliberate hole kept for the bit-flags idiom (`Flags.R | Flags.W` is typed `number`, as are `e++` and `e += 1`); only out-of-range *literals* have been rejected since TS 5.0. The annotated type is kept for the value, so a singleton literal type whose only inhabitant is `0` can hold `7`. Downstream code that trusts the value set then breaks: a `switch` over `E` covering every member is treated as exhaustive and needs no trailing return, so the function falls off the end and returns `undefined` from a `string`-typed slot.

```ts
enum E {
  A = 1,
  B = 2,
}
function toE(n: number): E {
  return n; // tsc: OK — deliberate hole kept for bit flags
}
function label(e: E): string {
  switch (e) {
    case E.A:
      return "a";
    case E.B:
      return "b";
  }
}
function caller(): string {
  return label(toE(7)); // undefined, typed string
}
```

**Test:** [tests/expect-error/enums.ts](../tests/expect-error/enums.ts) · **SKJS:** rejects — `Full type 'number'` / `is not assignable to specific type '1 | 2'` ([skjs-rules.md](../skjs-rules.md))

### Numeric enum reverse mapping is typed `string` for keys that have no entry

tsc gives the enum object (`typeof E`) a numeric index signature returning `string`, so `E[k]` type-checks as `string` for *any* numeric key — a literal that is not one of the enum's values, or a non-literal `number` variable. The same applies to `declare enum` and to enums with a computed member. The reverse-mapping property exists only for keys that are actually member values; every other numeric key reads `undefined` at runtime, so an expression typed `string` holds `undefined` and the next `.length` is a TypeError.

```ts
enum E {
  A = 1,
}
function nameOfZero(): string {
  return E[0]; // tsc: OK — E[0] is undefined at runtime
}
```

**Test:** [tests/expect-error/enums.ts](../tests/expect-error/enums.ts), [tests/expect-error/enums-computed.ts](../tests/expect-error/enums-computed.ts) · **SKJS:** rejects — `error: Property '0' does not exist on this type` (`Possible options are: 1, A`); with a non-literal key it reports `Cannot index this type with a non-literal key: it has no index signature`

## Standard library declarations

### Object.assign overwrites target properties with unchecked source values

`Object.assign<T extends object, U>(target: T, source: U): T & U` puts no constraint relating `U` to `T`, so tsc accepts merging a source whose property types contradict the target's — and the caller's variable keeps its original type `T`, since the intersection is only the *return* value, which may be discarded. The same signature ignores `readonly` modifiers on the target: `Object.assign(o, { a: 2 })` on `o: { readonly a: number }` is also clean. After the call `o.a` holds a string while typed `number`. A lib.es5 signature hole, with no `any`, `as` or `!` involved.

```ts
function boom(): number {
  const o = { a: 1 };
  Object.assign(o, { a: "not a number" }); // tsc: OK — U is unconstrained
  return o.a; // typed number, holds "not a number"
}
```

**Test:** no unsoundness pin — `Object.assign` appears in [tests/expect-error/callability.ts](../tests/expect-error/callability.ts) and [tests/expect-error/typeof.ts](../tests/expect-error/typeof.ts) only as a witness that a function can inhabit an object type · **SKJS:** also accepts — SKJS shares the hole; the builtin stub copies lib.es5's signature verbatim in [import-stubs/@types/skjs/index.d.ts](../import-stubs/@types/skjs/index.d.ts). SKJS deliberately omits the neighbouring merge/reflection primitives (`Object.create`, `defineProperty`, `freeze`, `getPrototypeOf`, `setPrototypeOf` are commented out as disallowed), so `assign` is the one merge primitive left open

### JSON.stringify is typed `string` but returns `undefined`

lib.es5 declares `stringify(value: any, ...): string` with no overload for the inputs on which the algorithm produces no text. `JSON.stringify(undefined)` — and the same for a function or a symbol — evaluates to `undefined`, not a string, so `s.length` on a value statically typed `string` is a TypeError. No assertion appears anywhere in the program, and TS 6.0.3's lib has added no narrowing overload.

```ts
function boom(): number {
  const s: string = JSON.stringify(undefined); // tsc: OK — s is undefined
  return s.length; // TypeError
}
```

**Test:** no pin · **SKJS:** also accepts — SKJS shares the hole; the stub in [import-stubs/@types/skjs/index.d.ts](../import-stubs/@types/skjs/index.d.ts) declares the same total `stringify<T>(value: T, replacer?, space?): string`

### A promise resolved with a thenable is typed Promise<Promise<T>>, a type nothing inhabits

The `Promise<T>` constructor's `resolve` parameter is `(value: T | PromiseLike<T>) => void`, so with `T = Promise<number>` tsc accepts resolving with a real promise and hands back `Promise<Promise<number>>`. The ECMAScript resolve function adopts thenables, so the outer promise fulfils with `1`: the `.then` callback parameter typed `Promise<number>` receives a number, and `v.then(...)` is a TypeError. No value of type `Promise<Promise<number>>` can ever exist at runtime, yet tsc mints one with no assertion. `Awaited<T>` closes the sibling routes — both `return Promise.resolve(p)` and the `async function` form annotated `Promise<Promise<number>>` are rejected with TS2322 — but the constructor route stays open.

```ts
function boom(p: Promise<number>): void {
  const pp = new Promise<Promise<number>>((res) => res(p)); // tsc: OK
  pp.then((v: Promise<number>) => v.then((n: number) => n)); // v is 1, not a promise
}
```

**Test:** no pin for the constructor route — [tests/expect-error/promise-object.ts](../tests/expect-error/promise-object.ts) covers the Promise stub generally · **SKJS:** rejects the construction — SKJS's Promise stub declares the executor's resolve as `(value: T) => void` with no `PromiseLike` arm, giving `Argument is not assignable to the parameter's type` with `Function parameter types are checked contravariantly: target parameter type 'Promise<number> | PromiseLike<Promise<...>>' must be assignable to source parameter type 'Promise<number>'`. Caveat: SKJS's `static resolve<T>(value: T): Promise<T>` has no `Awaited`, so the analogous `Promise.resolve(p)` program — which tsc rejects — is accepted by SKJS; the hole is closed on one route and open on the other ([skjs-rules.md](../skjs-rules.md), Promise rules)

## See also

- [skjs-rules.md](../skjs-rules.md) — the normative rules, including every "stricter than TypeScript" soundness rule referenced above.
- [docs/testing.md](testing.md) — how the pins in `tests/expect-error/` are written and run (`@skjs-expect-error` vs `@ts-expect-error`).
