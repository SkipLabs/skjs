// An optional-chaining method call `x?.m()` short-circuits on the RECEIVER: the
// `?.` guards `x`, not the member `m`.

interface Obj {
  f(): number;
}

// A required member through a nullable receiver is guarded; the result is
// `number | undefined`.
export function requiredMember(x: Obj | undefined): number | undefined {
  return x?.f();
}

// A class method through a nullable receiver, likewise.
class C {
  g(): number {
    return 1;
  }
}
export function classMethod(x: C | undefined): number | undefined {
  return x?.g();
}

// An OPTIONAL member is not guarded by `?.` on the receiver (TS requires
// `x?.m?.()`): the member may be undefined at the call, so it stays rejected.
export function optionalMember(
  x: { m?: () => number } | undefined,
): number | undefined {
  // @skjs-expect-error This expression is not callable
  return x?.m();
}

function skippedArgument(obj: { m(x: number): number } | undefined): number {
  let state: number | null = null;
  const result = obj?.m((state = 1));
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return state;
}

function possibleArgument(obj: { m(x: null): number } | undefined): number {
  let state: number | null = 1;
  const result = obj?.m((state = null));
  // A present receiver evaluates the argument and can invalidate state.
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return state;
}

function callResult(obj: { m(x: number): number } | undefined): number {
  let state: number | null = null;
  const result = obj?.m((state = 1));
  return result ?? 0;
}
