/**
 * When T & U is computed where T and U have incompatible bounds, the
 * intersection should be empty (never), and arguments should be rejected.
 *
 * Currently the intersection is computed lazily, so incompatible calls
 * are accepted when the result is unused.
 */

function f<T>(x: T, y: T & number): T {
  return x;
}

// T = "hello", y: T & number = "hello" & number = never
// 42 is not assignable to never, so this should error at the call site
// Instead, the error is about the return type not being void
function incompleteRejection(): void {
  // @skjs-expect-error This expression was expected to be of type void or ignorable
  f("hello", 42);
}

// Same call errors when result is used as string
function usedAsString(): void {
  const result = f("hello", 42);
  // @skjs-expect-error Invalid annotation
  const x: "hello" = result;
}

// Same call errors when result is used as number
function usedAsNumber(): void {
  const result = f("hello", 42);
  // @skjs-expect-error Invalid annotation
  const x: number = result;
}

// With literal return type, the call is rejected
function explicitReturn(): "hello" {
  // @skjs-expect-error Invalid return type
  return f("hello", 42);
}
