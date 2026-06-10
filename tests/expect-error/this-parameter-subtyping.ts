// Test subtyping of function types with `this` parameters.
// Rules (matching TS):
//   - `thisParam` is contravariant.
//   - A signature without a `thisParam` is treated as `this: unknown` and is
//     compatible with any declared this type on either side.
//
// Staged: the contravariance rejection already holds; the asymmetric no-this
// case is rejected until the none/some relaxation lands (then it type-checks).

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
