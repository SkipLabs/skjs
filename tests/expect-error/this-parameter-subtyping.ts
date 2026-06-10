// Test subtyping of function types with `this` parameters.
// Rules (sound; stricter than TS where noted):
//   - `thisParam` is contravariant between two declared this types.
//   - A missing `thisParam` on the subtype side is `this: unknown` (the
//     function ignores its receiver) — sound to accept.
//   - A missing `thisParam` on the SUPERTYPE side is a free-call permit, so a
//     this-declaring function is NOT assignable there (SkipLabs/skjs#960):
//     accepting it would let `const b: () => void = fnBase; b()` run the body
//     with no receiver. TS accepts this (unsoundly); SKJS rejects.
//
// Staged: the declared/declared contravariance rejection already holds
// upstream; the subtype-side relaxation and the supertype-side rejection land
// in the subtyping commit (annotations flip there).

class Base {
  tag: string = "base";
}
class Derived extends Base {
  extra: number = 1;
}
class Unrelated {
  other: number = 2;
}

type FnBase = (this: Base) => void;
type FnDerived = (this: Derived) => void;
type FnUnrelated = (this: Unrelated) => void;
type FnNoThis = () => void;

declare const fnBase: FnBase;
declare const fnDerived: FnDerived;
declare const fnUnrelated: FnUnrelated;
declare const fnNoThis: FnNoThis;

function contravariance(): void {
  // Accepts supertype this: (this: Base)=>void is assignable to (this: Derived)=>void.
  const x: FnDerived = fnBase;

  // Rejects: (this: Derived)=>void is NOT assignable to (this: Base)=>void.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: FnBase = fnDerived;

  // Unrelated this types are also not assignable.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: FnBase = fnUnrelated;
}

function asymmetricNoThis(): void {
  // TODO: once missing-this is treated as `this: unknown`, this type-checks.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: FnBase = fnNoThis;
  const b: FnNoThis = fnBase;
}
