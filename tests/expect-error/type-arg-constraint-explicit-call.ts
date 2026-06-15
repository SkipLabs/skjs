// An explicit type argument to a generic function call is checked against the
// type parameter's constraint, matching TypeScript (TS2344). The check fires
// even when the type parameter occurs only in a covariant position (here the
// return type), where an unchecked substitution would collapse to
// `argument & constraint` and be silently absorbed. Inference enforces the same
// constraint via the inference variable; this covers the explicit-argument
// position, which the inference path does not reach.

declare function pick<V extends string>(): V;

export function rejectsBareViolation(): number {
  // @ts-expect-error Type argument does not satisfy the constraint
  return pick<number>();
}

// A constraint-satisfying explicit argument is accepted.
export function acceptsBareValid(): string {
  return pick<"hello">();
}

// A dependent constraint (B extends A) is checked against the corresponding
// argument: B = string does not satisfy A = number.
declare function dependent<A, B extends A>(): B;

export function rejectsDependentViolation(): number {
  // @ts-expect-error Type argument does not satisfy the constraint
  return dependent<number, string>();
}

// The dependent constraint is satisfied: B = 42 extends A = number.
export function acceptsDependentValid(): number {
  return dependent<number, 42>();
}
