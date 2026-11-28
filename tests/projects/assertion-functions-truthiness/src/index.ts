// Bodied `asserts x` on `unknown` / `string` / `number` under
// `--truthiness typescript` (where `if (!x)` is permitted on non-boolean
// types) — issue #583.

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
export function assertTruthyUnknown(x: unknown): asserts x {
  if (!x) {
    throw new Error("falsy");
  }
}

export function useAssertTruthyUnknown(x: string | null | undefined): string {
  assertTruthyUnknown(x);
  return x;
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
export function assertTruthyString(x: string): asserts x {
  if (!x) {
    throw new Error("empty");
  }
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
export function assertTruthyNumber(x: number): asserts x {
  if (!x) {
    throw new Error("zero or NaN");
  }
}

// Early return inside `if (x)`.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
export function assertTruthyEarlyReturn(x: unknown): asserts x {
  if (x) {
    return;
  }
  throw new Error("falsy");
}

// Lying body on `unknown`: never checks truthiness.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
export function badAssertTruthyUnknown(x: unknown): asserts x {}

// Missing branch: `provenTruthy` is only established on one path.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
export function badAssertTruthyBranch(cond: boolean, x: unknown): asserts x {
  if (cond) {
    if (!x) {
      throw new Error("falsy");
    }
  }
}
