/** `async`, `await`, `for...of` over an array and `for...in` as trusted
 * steps (PROGRAM-TYPING.md, "Async functions and await", "Loops over arrays" and
 * "Statement forms"). Each is a
 * call of an intrinsic, a value no source name can denote: the parser writes
 * the async ones, and Lean compiles a `for...of` to its calls. The declaration
 * reader lists the intrinsics among the client's values at these signatures,
 * some over the standard library's `Promise`. Nothing checks them: like an
 * imported value's declared type, each is an assumption a result is relative
 * to.
 *
 * - `await e` is `%Await%(e)`: a promise settles, if ever, to a value of its
 *   type argument, and awaiting it yields that value; awaiting a primitive,
 *   which is never a thenable, yields the primitive itself. Other jobs may
 *   run in between, as they may during any call.
 * - `return e` in an async function is `return %AsyncReturn%(e)`: the promise
 *   the call returned settles to `e` where `e` is a primitive, and adopts `e`
 *   where it is a promise of a primitive, settling to what `e` settles to.
 *   No other object is admitted, since JavaScript adopts a thenable object
 *   instead of settling to it.
 * - Completing an async function is `return %AsyncComplete%()`: its promise
 *   settles to `undefined`, which `Promise<void>` admits.
 * - `for (const x of xs)` over an array steps `%Iterate%(xs)`: the array's
 *   iterator, which yields `{ value }` for each element in turn, reading the
 *   array's current length at each step, and then `null`.
 * - `for (const k in o)` is `for (const k of %ForIn%(o))`: the keys the loop
 *   visits, each a string, of any value (none for null or undefined).
 *
 * The reviewed overlay of library globals (`library-globals.mts`) reads some
 * members as these: `Promise.resolve(v)` is `%AsyncReturn%(v)`, a promise
 * settled to `v`, `Promise.resolve()` is `%AsyncComplete%()`, and
 * `Promise.all(ps)` is `%PromiseAll%(ps)`: a promise of the array of what
 * the promises settle to, in order, settling once each has. The array is
 * fresh and owns no `then`, so it is not adopted. `Promise.reject(r)` is
 * `%PromiseReject%(r)`, a promise rejected with `r`, whose await throws, and
 * `new Promise(executor)` is `%NewPromise%(executor)`: the executor is
 * called at once with the promise's resolving functions, and resolving
 * settles the promise to a primitive, as `%AsyncReturn%` does. */
import type { TypeTerm } from "./declaration-types.mts";

export const intrinsicModule = "skjs/intrinsics";
export const awaitName = "%Await%";
export const asyncReturnName = "%AsyncReturn%";
export const asyncCompleteName = "%AsyncComplete%";
export const iterateName = "%Iterate%";
export const forInName = "%ForIn%";
export const promiseAllName = "%PromiseAll%";
export const promiseRejectName = "%PromiseReject%";
export const newPromiseName = "%NewPromise%";

type Signature = Extract<TypeTerm, { k: "function" }>;
type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];
const span: [number, number] = [0, 0];
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span });
const binder: TypeTerm = { k: "binder", name: "T", span };
/** A second binder, for the primitives a step passes through unchanged. */
const other: TypeTerm = { k: "binder", name: "U", span };
const either = (...parts: TypeTerm[]): TypeTerm => ({ k: "union", span, parts });
const fn = (params: TypeTerm[], result: TypeTerm): Signature =>
  ({ k: "function", receiver: null, params, rest: null, result, span });
/** The values no object is: a promise resolved with one settles to it. */
const primitives: AtomName[] = ["null", "undefined", "boolean", "number", "string", "bigint", "symbol"];
const primitive: TypeTerm = { k: "union", span, parts: primitives.map(atom) };
/** The types no thenable inhabits: primitives, arrays (whose prototype holds
 * no `then`, and to which no step adds one), and objects whose `then` reads
 * a primitive or nothing. A trusted generic signature is truthful about a
 * promise of its type parameter only where the parameter is instantiated at
 * one: a realm promise resolved with a thenable adopts it. */
export const nonThenable: TypeTerm = { k: "union", span, parts: [...primitives.map(atom),
  { k: "object", span, stringIndex: null, calls: [],
    fields: [{ name: "then", optional: true, readonly: true, type: primitive, span }] },
  { k: "array", readonly: true, element: atom("unknown"), span }] };

/** `() => { readonly value: T } | null`: an iterator step, `null` at the end. */
const step: Signature = fn([], { k: "union", span, parts: [
  { k: "object", span, stringIndex: null, calls: [],
    fields: [{ name: "value", optional: false, readonly: true, type: binder, span }] },
  atom("null")] });

/** The intrinsics' binders and signatures, given the standard library's
 * `Promise` applied to an argument. */
export function intrinsics(promise: (argument: TypeTerm) => TypeTerm):
  { name: string; typeParams: { name: string; bound: TypeTerm | null }[]; type: Signature }[] {
  return [
    // `await` of a promise of `T` or of a primitive `U`: what the promise
    // settles to, or the primitive itself.
    { name: awaitName, typeParams: [{ name: "T", bound: null }, { name: "U", bound: primitive }],
      type: fn([either(promise(binder), other)], either(binder, other)) },
    // Settling to a primitive `T`, or adopting a promise of a primitive `U`:
    // adoption calls its `then`, which passes a `U`, and settles to it.
    { name: asyncReturnName, typeParams: [{ name: "T", bound: primitive }, { name: "U", bound: primitive }],
      type: fn([either(binder, promise(other))], promise(either(binder, other))) },
    { name: asyncCompleteName, typeParams: [], type: fn([], promise(atom("void"))) },
    { name: iterateName, typeParams: [{ name: "T", bound: null }],
      type: fn([{ k: "array", readonly: true, element: binder, span }], step) },
    { name: promiseAllName, typeParams: [{ name: "T", bound: null }],
      type: fn([{ k: "array", readonly: true, element: promise(binder), span }],
        promise({ k: "array", readonly: false, element: binder, span })) },
    // A promise rejected with the reason: awaiting it throws, so it is a
    // promise of every type, never settling to a value.
    { name: promiseRejectName, typeParams: [{ name: "T", bound: null }],
      type: fn([atom("unknown")], promise(binder)) },
    // `new Promise(executor)`: the executor runs at once, given functions
    // that settle the promise to their argument, or reject it; a throw out
    // of the executor rejects it. The bound is `%AsyncReturn%`'s: resolving
    // with a thenable would adopt it instead of settling to it.
    { name: newPromiseName, typeParams: [{ name: "T", bound: primitive }],
      type: fn([fn([fn([binder], atom("void")), fn([atom("unknown")], atom("void"))], atom("void"))],
        promise(binder)) },
    { name: forInName, typeParams: [],
      type: fn([atom("unknown")], { k: "array", readonly: true, element: atom("string"), span }) },
  ];
}
