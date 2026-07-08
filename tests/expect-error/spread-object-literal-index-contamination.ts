import type { Json } from "@skipruntime/core";

// Object literals carry synthetic string/symbol indexes as subtyping artifacts
// (so `{ count: 5 }` can satisfy `{ [k: string]: number }`). Spreading a closed
// object literal must NOT leak those synthetic indexes into the accumulated
// spread result: the synthetic index's getter is a shared, initially-unbound
// type variable, and routing it into the result couples otherwise-unrelated
// fields through that one variable, producing spurious "not assignable" errors.

// Multiple pre-existing siblings + a spread literal that omits them: the
// literal's synthetic string index must not couple `s` and `n` (which would
// wrongly report "number is not assignable to string"). The value
// `{ s, n, q }` is sound.
function siblings(): { s: string; n: number } {
  return { s: "a", n: 1, ...{ q: true } };
}

// A conditional spread into a target with a real string index: the `count`
// literal's synthetic index must not collide with the named `keyId: string`.
type Target = { readonly keyId: string; readonly count?: number } & {
  readonly [key: string]: Json | null;
};
function chained(keyId: string, count: number | undefined): Target {
  return { keyId, ...(count !== undefined && { count }) };
}

// Symbol path: the synthetic SYMBOL index of a spread literal (here an empty
// literal, whose only symbol-domain contribution IS its synthetic symbol
// index) must not leak onto the symbol-keyed field `[kId]: string`.
declare const kId: unique symbol;
function symbolPath(idv: string): { readonly [kId]: string } & {
  readonly [key: symbol]: number | string;
} {
  return { [kId]: idv, ...{} };
}

// A REAL (non-synthetic) index on the spread source must still accumulate into
// the result's index.
type StringIndexed = { readonly [key: string]: number };
function realIndex(source: StringIndexed): { x: number; y: number } & {
  readonly [key: string]: number;
} {
  return { x: 1, y: 2, ...source };
}
