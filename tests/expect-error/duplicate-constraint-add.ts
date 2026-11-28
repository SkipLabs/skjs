// Test: Duplicate constraint addition during type instantiation.
//
// When a function like `getLength<T extends HasLength>` is called with an
// explicit type argument `getLength<string>(s)`, the constraint `HasLength`
// may be added to T multiple times.

// Simple constraint type
interface HasLength {
  length: number;
}

// Function with constrained type parameter
function getLength<T extends HasLength>(x: T): number {
  return x.length;
}

function test(): void {
  // String has readonly `length`, so it does not satisfy mutable `HasLength`.
  const s: string = "hello";
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error Type argument does not satisfy the constraint
  const len: number = getLength<string>(s);
}
