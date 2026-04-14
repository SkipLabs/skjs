// Test destructuring patterns in function parameters

// Simple parameter names work
function simpleParams(x: number, y: string): void {}

// Object destructuring in parameters
// @skjs-expect-error TODO: support for patterns in function parameters
function objectPattern({ x, y }: { x: number; y: string }): void {
  // TODO: variable usage (not reported due to earlier error)
  const a: number = x;
}

// Array destructuring in parameters
// @skjs-expect-error TODO: support for patterns in function parameters
function arrayPattern([a, b]: [number, string]): void {
  // TODO: variable usage (not reported due to earlier error)
  const x: number = a;
}

// Nested destructuring patterns
// @skjs-expect-error TODO: support for patterns in function parameters
function nestedPattern({ point: [x, y] }: { point: [number, number] }): void {
  // TODO: variable usage (not reported due to earlier error)
  const a: number = x;
}

// Object destructuring with defaults
// @skjs-expect-error TODO: support for patterns in function parameters
function objectDefaultPattern({ a = 0 }: { a?: number }): void {
  // TODO: variable usage (not reported due to earlier error)
  const x: number = a;
}

// Object destructuring with rest
// @skjs-expect-error TODO: support for patterns in function parameters
function objectRestPattern({
  a,
  ...rest
}: {
  a: number;
  b: string;
  c: boolean;
}): void {
  // TODO: variable usage (not reported due to earlier error)
  const x: number = a;
}

// Multiple destructured parameters
// @skjs-expect-error TODO: support for patterns in function parameters
function multiPattern({ a }: { a: number }, [b]: [string]): void {
  // TODO: variable usage (not reported due to earlier error)
  const x: number = a;
}

// Function type with pattern parameters (parsing only)
type FuncWithObjectParam = ({ x, y }: { x: number; y: number }) => void;
type FuncWithArrayParam = ([a, b]: [number, string]) => void;
