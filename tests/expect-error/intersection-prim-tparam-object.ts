// Regression / pinning tests for SkipLabs/skjs#72:
// Intersecting a primitive type with a type parameter constrained to an object
// type (e.g. `string & T` where `T extends { readonly length: number }` or
// `number & T` where `T extends {}`) must NOT drop `T` and simplify to the
// bare primitive. Doing so over-approximates the intersection and then reuses
// that over-approximation in contravariant (target) positions, allowing a raw
// primitive to be returned as `string & T` and then coerced at call sites to
// any concrete subtype of the object constraint (runtime TypeError).

type Inter<A, B> = A & B;

// 1. Primitive on left, constrained type parameter on right (via alias and direct).
// BUG (#72): currently accepted because `Clauses::getObject()` ignores `clause.vars`
// and simplifies `string & T` to `string`, dropping `T`.
function primLeftAlias<T extends { readonly length: number }>(
  s: string,
): Inter<string, T> {
  return s;
}

function primLeftDirect<T extends { readonly length: number }>(
  s: string,
): string & T {
  return s;
}

// 2. Symmetric: constrained type parameter on left, primitive on right.
function primRightAlias<T extends { readonly length: number }>(
  s: string,
): Inter<T, string> {
  return s;
}

function primRightDirect<T extends { readonly length: number }>(
  s: string,
): T & string {
  return s;
}

// 3. Other primitives with `{}` constraint (number, boolean).
function numAndEmptyObj<T extends {}>(n: number): Inter<number, T> {
  return n;
}

function boolAndEmptyObj<T extends {}>(b: boolean): Inter<T, boolean> {
  return b;
}

// 4. Primitive literal & constrained type parameter.
function literalAndObjTParam<T extends { readonly length: number }>(
  s: "hello",
): Inter<"hello", T> {
  return s;
}

// 5. Type parameter constrained to primitive & type parameter constrained to object.
function tparamPrimAndObjTParam<
  S extends string,
  T extends { readonly length: number },
>(s: S): Inter<S, T> {
  return s;
}

// 6. Union of primitive literals / tparams intersected with constrained type parameter.
function unionPrimAndObjTParam<
  S extends string,
  T extends { readonly length: number },
>(x: S | "fallback"): Inter<S | "fallback", T> {
  return x;
}

// 7. End-to-end unsound coercion enabled by the bug: `primLeftAlias` accepts
// returning `"hello"` as `Inter<string, T>`, and instantiating `T` with an
// incompatible object type produces `never` at the call site, silently
// assigning `"hello"` to `{ readonly length: number; boom: () => void }`.
function crashViaPrimLeft(): void {
  const o: { readonly length: number; boom: () => void } = primLeftAlias<{
    readonly length: number;
    boom: () => void;
  }>("hello");
  o.boom();
}

// 8. Sound positive checks: a value of type `string & T` or `T & string` is
// assignable to `string`, exposes `length`, and round-trips to `string & T`.
function useInterLeft<T extends { readonly length: number }>(
  x: string & T,
): { s: string; len: number; same: T & string } {
  // BUG (#72): currently prints `string`, dropping `T`.
  __SKJS_show_expanded(x, "string");
  return { s: x, len: x.length, same: x };
}

function useInterRight<T extends { readonly length: number }>(
  x: T & string,
): { s: string; len: number; same: string & T } {
  // BUG (#72): currently prints `string`, dropping `T`.
  __SKJS_show_expanded(x, "string");
  return { s: x, len: x.length, same: x };
}

// 9. Narrowing path (`TTypeObservation::intersection_`):
// `t === s` (and `s === t`) with `t: T` (`T extends { readonly length: number }`)
// and `s: string` narrows `t` / `s` to `T & string`, preserving `T`.
function narrowLeftPreservesTParam<T extends { readonly length: number }>(
  t: T,
  s: string,
  fallback: T & string,
): T & string {
  if (t === s) {
    // BUG (#72): currently narrows to bare `string`, dropping `T`.
    __SKJS_show_expanded(t, "string");
    return t;
  }
  return fallback;
}

function narrowRightPreservesTParam<T extends { readonly length: number }>(
  t: T,
  s: string,
  fallback: string & T,
): string & T {
  if (s === t) {
    // BUG (#72): currently narrows to bare `string`, dropping `T`.
    __SKJS_show_expanded(s, "string");
    return s;
  }
  return fallback;
}

// 10. Concrete primitive & concrete object (no type parameters) MUST still
// simplify to the primitive when the primitive's boxed interface is a subtype
// of the object.
function concretePrimAndObj(s: string): string & { readonly length: number } {
  return s;
}

function concreteObjAndPrim(s: string): { readonly length: number } & string {
  return s;
}

function concreteTParamPrimAndObj<S extends string>(
  s: S,
): S & { readonly length: number } {
  return s;
}
