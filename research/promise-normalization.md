<!-- Research note awaiting relocation: this content belongs in docs/typescript-soundness-holes.md. -->
# TypeScript's `Awaited` is unsound

TypeScript 7.0.2's `lib.es5.d.ts` defines:

```ts
type Awaited<T> =
  T extends null | undefined ? T :
  T extends object & { then(onfulfilled: infer F, ...args: infer _): any } ?
    F extends ((value: infer V, ...args: infer _) => any) ?
      Awaited<V> :
    never :
  T;
```

It distributes over unions and works from the declared type:

| Input | `Awaited` |
| --- | --- |
| `null`, `undefined` | itself |
| an object type declaring `then` whose first parameter is a function `(value: V, ...) => any` | `Awaited<V>` |
| an object type declaring `then` whose first parameter is not a function | `never` |
| every other type: primitives, object types with no declared `then` | itself |
| a type variable `T` | `Awaited<T>`, deferred until `T` is known |

TypeScript uses it in `Promise.resolve<T>(value: T): Promise<Awaited<T>>`, in `Promise.all`, and to type `await x`.

`Awaited` decides from the declared type; `await` decides from the runtime value. TypeScript object types are open: a value of type `{ n: number }` may carry a `then` its type does not mention. Both programs below are accepted by `tsc --strict` 7.0.2 and produce, under Node, a value outside the type TypeScript gives it:

```ts
// (a) The type hides a `then`.
function asRecord(x: { n: number }): { n: number } { return x; }
const t = { n: 1, then(resolve: (v: string) => void) { resolve("hi"); } };
const v = await asRecord(t);   // TS: { n: number }   Node: "hi"

// (b) An object acquires a `then` after a promise fulfills with it.
const obj = { value: 1 };
const p: Promise<{ value: number }> = Promise.resolve(obj);
Object.assign(obj, { then: (r: (x: number) => void) => r(42) });
const first = await p;          // TS: { value: number }   Node: obj
const second = await first;     // TS: { value: number }   Node: 42
```

In (a), passing `t` at `{ n: number }` is ordinary width subtyping, and `Awaited<{ n: number }>` is `{ n: number }`. In (b), TypeScript reads `Awaited<Awaited<T>>` as `Awaited<T>`, but resolving a value that resolution already produced returns something else: runtime resolution is not idempotent on objects.

Evidence: both programs were run with `tsc --strict` 7.0.2 and Node on 2026-10-07. Sources: TypeScript's `lib.es5.d.ts` and the [Awaited documentation](https://www.typescriptlang.org/docs/handbook/utility-types#awaitedtype); [ECMA-262 Promise Resolve Functions](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-promise-resolve-functions).
