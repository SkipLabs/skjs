// The constraint check applies to class type parameters and to constraints that
// reference an earlier parameter (dependent constraints), not only to standalone
// type aliases. A violating argument is rejected at its reference (TypeScript
// rejects it too); a satisfying argument is accepted.

class Box<T extends string> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

function classViolation(x: Box<number>): void {}

function classValid(x: Box<string>): void {}

type BoxAlias<P extends string> = { v: P };

// U's constraint references the earlier parameter T, so checking it requires T
// to be bound to its argument.
type Dep<T extends string, U extends BoxAlias<T>> = { t: T; u: U };

export type DependentViolation = Dep<string, BoxAlias<number>>;

export type DependentValid = Dep<string, BoxAlias<string>>;
