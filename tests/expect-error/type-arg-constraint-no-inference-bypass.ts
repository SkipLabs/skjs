// Inferring a type argument cannot bypass a generic's constraint. A signature
// that would instantiate a constrained generic with an unconstrained type
// parameter is rejected outright, so no call can reach such a boundary — whether
// the variable is used bare, nested in a union, or nested in an object. When the
// boundary is itself valid, a violating call is rejected at the call site. Valid
// inference still narrows.

type Id<P extends string> = P;
type Tagged<P extends { tag: string }> = P;

// @ts-expect-error Constraint not satisfied
function bare<V>(x: Id<V>): void {}

// @ts-expect-error Constraint not satisfied
function union<V>(x: Id<V | "tag">): void {}

// @ts-expect-error Constraint not satisfied
function nested<V>(x: Tagged<{ tag: V }>): void {}

// A valid boundary is accepted; a violating call is rejected at the call site.
function constrained<V extends string>(x: Id<V>): V {
  return x;
}
export function violatingCall(): string {
  // @ts-expect-error Invalid call
  return constrained(42);
}

// Valid inference is unaffected: K narrows to string rather than widening to its
// constraint.
type StrOrNum = string | number;
type Mapper<K extends StrOrNum> = { map(): K };
interface Collection {
  map<K extends StrOrNum>(mapper: Mapper<K>): K;
}
export function stillNarrows(col: Collection): string {
  const m: Mapper<string> = { map: () => "x" };
  return col.map(m);
}
