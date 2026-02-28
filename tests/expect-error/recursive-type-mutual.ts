// Tests for mutually recursive type aliases.
// These exercise expansion paths where seenInstantiate prevents
// infinite unfolding: expanding A encounters B, expanding B
// encounters A (already in seenInstantiate), so A stays unexpanded.

type A<T> = null | { data: T; other: B<T> };
type B<T> = null | { data: T; other: A<T> };

// Positive: identity assignments
function mutualIdentity<T>(a: A<T>, b: B<T>): void {
  const x: A<T> = a;
  const y: B<T> = b;
}

// Positive: constructing mutually recursive values
function mutualConstruct<T>(val: T, a: A<T>, b: B<T>): void {
  const x: A<T> = { data: val, other: { data: val, other: a } };
  const y: B<T> = { data: val, other: { data: val, other: b } };
}

// Positive: null is valid for both
function mutualNull<T>(): void {
  const x: A<T> = null;
  const y: B<T> = null;
}

// Negative: A<number> vs B<string> — incompatible type parameter
function mutualMismatch(a: A<number>, b: B<string>): void {
  const x: A<number> = a;
  const y: B<string> = b;
}

// Positive: nested mutual construction
function mutualNested<T>(val: T): A<T> {
  // @skjs-expect-error Invalid return type
  return { data: val, other: { data: val, other: null } };
}
