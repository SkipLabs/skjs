/** `async` and `await` as trusted steps (DESIGN.md, "Async functions and
 * await"). The parser writes each as a call of an intrinsic, a value no
 * source name can denote, and the declaration reader lists the intrinsics
 * among the client's values at these signatures over the standard library's
 * `Promise`. Nothing checks them: like an imported value's declared type,
 * each is an assumption a result is relative to.
 *
 * - `await e` is `%Await%(e)`: a promise settles, if ever, to a value of its
 *   type argument, and awaiting it yields that value. Other jobs may run in
 *   between, as they may during any call.
 * - `return e` in an async function is `return %AsyncReturn%(e)`: the promise
 *   the call returned settles to `e`. Only a primitive is admitted, since
 *   JavaScript adopts a thenable object instead of settling to it.
 * - Completing an async function is `return %AsyncComplete%()`: its promise
 *   settles to `undefined`, which `Promise<void>` admits. */
import type { TypeTerm } from "./declaration-types.mts";

export const intrinsicModule = "skjs/intrinsics";
export const awaitName = "%Await%";
export const asyncReturnName = "%AsyncReturn%";
export const asyncCompleteName = "%AsyncComplete%";

type Signature = Extract<TypeTerm, { k: "function" }>;
type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];
const span: [number, number] = [0, 0];
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span });
const binder: TypeTerm = { k: "binder", name: "T", span };
const fn = (params: TypeTerm[], result: TypeTerm): Signature =>
  ({ k: "function", receiver: null, params, rest: null, result, span });
/** The values no object is: a promise resolved with one settles to it. */
const primitives: AtomName[] = ["null", "undefined", "boolean", "number", "string", "bigint", "symbol"];
const primitive: TypeTerm = { k: "union", span, parts: primitives.map(atom) };

/** The intrinsics' binders and signatures, given the standard library's
 * `Promise` applied to an argument. */
export function asyncIntrinsics(promise: (argument: TypeTerm) => TypeTerm):
  { name: string; typeParams: { name: string; bound: TypeTerm | null }[]; type: Signature }[] {
  return [
    { name: awaitName, typeParams: [{ name: "T", bound: null }], type: fn([promise(binder)], binder) },
    { name: asyncReturnName, typeParams: [{ name: "T", bound: primitive }], type: fn([binder], promise(binder)) },
    { name: asyncCompleteName, typeParams: [], type: fn([], promise(atom("void"))) },
  ];
}
