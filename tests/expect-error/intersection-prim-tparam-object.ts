// Regression tests for SkipLabs/skjs#72:
// Intersecting a primitive type with a type parameter constrained to an object
// type (e.g. `string & T` where `T extends { readonly length: number }` or
// `number & T` where `T extends {}`) must preserve `T` rather than dropping it
// and simplifying to the bare primitive. Dropping `T` over-approximates the
// intersection and reuses that over-approximation in contravariant (target)
// positions, allowing a raw primitive to be returned as `string & T` and then
// coerced at call sites to any concrete subtype of the object constraint.

type Inter<A, B> = A & B;

// 1. Primitive on left, constrained type parameter on right (via alias and direct).
function primLeftAlias<T extends { readonly length: number }>(
  s: string,
): Inter<string, T> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

function primLeftDirect<T extends { readonly length: number }>(
  s: string,
): string & T {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

// 2. Symmetric: constrained type parameter on left, primitive on right.
function primRightAlias<T extends { readonly length: number }>(
  s: string,
): Inter<T, string> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

function primRightDirect<T extends { readonly length: number }>(
  s: string,
): T & string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

// 3. Other primitives with `{}` constraint (number, boolean).
function numAndEmptyObj<T extends {}>(n: number): Inter<number, T> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return n;
}

function boolAndEmptyObj<T extends {}>(b: boolean): Inter<T, boolean> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return b;
}

// 4. Primitive literal & constrained type parameter.
function literalAndObjTParam<T extends { readonly length: number }>(
  s: "hello",
): Inter<"hello", T> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

// 5. Type parameter constrained to primitive & type parameter constrained to object.
function tparamPrimAndObjTParam<
  S extends string,
  T extends { readonly length: number },
>(s: S): Inter<S, T> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return s;
}

// 6. Union of primitive literals / tparams intersected with constrained type parameter.
function unionPrimAndObjTParam<
  S extends string,
  T extends { readonly length: number },
>(x: S | "fallback"): Inter<S | "fallback", T> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 7. Call site of `primLeftAlias` (whose unsound body is now rejected above).
function crashViaPrimLeft(): void {
  const o: { readonly length: number; boom: () => void } = primLeftAlias<{
    readonly length: number;
    boom: () => void;
  }>("hello");
  o.boom();
}

// 8. Sound positive checks: a value of type `string & T` or `T & string` is
// assignable to `string`, exposes `length`, and preserves `T` in its clauses.
function useInterLeft<T extends { readonly length: number }>(
  x: string & T,
): { s: string; len: number; same: T & string } {
  __SKJS_show_expanded(x, "T extends string");
  return { s: x, len: x.length, same: x };
}

function useInterRight<T extends { readonly length: number }>(
  x: T & string,
): { s: string; len: number; same: string & T } {
  __SKJS_show_expanded(x, "T extends string");
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
    __SKJS_show_expanded(t, "T extends string");
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
    __SKJS_show_expanded(s, "T extends string");
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
