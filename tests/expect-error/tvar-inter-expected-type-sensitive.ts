/**
 * The inferred type of f("hello", 42) depends on the expected type context.
 * This is due to bidirectional inference re-evaluating constraints.
 *
 * - When checked against "hello", result is inferred as 42
 * - When checked against 42, result is inferred as "hello"
 * - When checked against number, result is inferred as "hello"
 */

function f<T>(x: T, y: T & number): T {
  return x;
}

// When expected type is "hello", inferred type is 42
function expectHello(): void {
  const result = f("hello", 42);
  // @skjs-expect-error Invalid annotation
  const x: "hello" = result;
}

// When expected type is 42, inferred type is "hello"
function expect42(): void {
  const result = f("hello", 42);
  // @skjs-expect-error Invalid annotation
  const x: 42 = result;
}

// When expected type is number, inferred type is "hello"
function expectNumber(): void {
  const result = f("hello", 42);
  // @skjs-expect-error Invalid annotation
  const x: number = result;
}

// When expected type is string, inferred type is 42
function expectString(): void {
  const result = f("hello", 42);
  // @skjs-expect-error Invalid annotation
  const x: string = result;
}

// Direct return with "hello" return type - inferred as 42
function returnHello(): "hello" {
  // @skjs-expect-error Invalid return type
  return f("hello", 42);
}

// Direct return with 42 return type - inferred as "hello"
function return42(): 42 {
  // @skjs-expect-error Invalid return type
  return f("hello", 42);
}
