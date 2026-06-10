// An explicit type argument to a generic function call is not checked against
// the type parameter's constraint: SKJS accepts the calls below without error,
// but TypeScript rejects them (TS2344).
//
// `pick<V extends string>(): V` instantiated with `number` violates
// `V extends string`. Because V occurs only in the (covariant) return position,
// the substituted return type collapses to `number & string` = `never`, which
// is assignable to anything, so the bad argument is absorbed silently. The same
// call being assignable to BOTH `number` and `string` — a value cannot be both
// — shows this is a soundness violation, not merely a divergence from tsc.
//
// Inference does not have this hole: an inferred type argument carries its
// constraint on the inference variable, so `const n: number = pick()` is
// correctly rejected. Only explicit arguments bypass the check.

declare function pick<V extends string>(): V;

// Unsound: a `number` result is produced from an out-of-constraint explicit
// type argument.
export function unsoundNumber(): number {
  return pick<number>();
}

// The same out-of-constraint call is also accepted as `string`, exposing the
// `never` collapse.
export function unsoundString(): string {
  return pick<number>();
}

// A constraint-satisfying explicit argument is accepted.
export function valid(): string {
  return pick<"hello">();
}
