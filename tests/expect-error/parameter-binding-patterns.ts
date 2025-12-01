// Test that parameter names are binding patterns

// Simple parameter names work
function simpleParams(x: number, y: string): void {}

// Array destructuring in parameters (parses but not fully supported yet)
// @skjs-expect-error TODO: support for patterns in function parameters
function arrayPattern([a, b]: [number, string]): void {
  // TODO: Variable usage (not reported due to earlier error in function)
  const sum: number = a;
}

// Object destructuring in parameters (parses but not fully supported yet)
// @skjs-expect-error TODO: support for patterns in function parameters
function objectPattern({ x, y }: { x: number; y: number }): void {
  // TODO: Variable usage (not reported due to earlier error in function)
  const sum: number = x;
}

// Nested destructuring patterns
// @skjs-expect-error TODO: support for patterns in function parameters
function nestedPattern({ point: [x, y] }: { point: [number, number] }): void {
  // TODO: Variable usage (not reported due to earlier error in function)
  const sum: number = x;
}

// Function type with array pattern parameters
type FuncWithArrayParam = ([a, b]: [number, string]) => void;

// Function type with object pattern parameters
type FuncWithObjectParam = ({ x, y }: { x: number; y: number }) => void;

// Function type with simple parameters
type FuncWithSimpleParams = (x: number, y: string) => boolean;

// Using function types with pattern parameters
function takesArrayFunc(f: ([a, b]: [number, string]) => void): void {
  f([1, "hello"]);
}

function takesObjectFunc(f: ({ x }: { x: number }) => void): void {
  f({ x: 42 });
}
