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
  // String satisfies HasLength
  const s: string = "hello";
  const len: number = getLength<string>(s);
}
