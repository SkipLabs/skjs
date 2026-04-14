// Test destructuring patterns in function parameters

// Simple parameter names work
function simpleParams(x: number, y: string): void {}

// Object destructuring in parameters
function objectPattern({ x, y }: { x: number; y: string }): void {
  const a: number = x;
  const b: string = y;
}

// Array destructuring in parameters
function arrayPattern([a, b]: [number, string]): void {
  const x: number = a;
  const y: string = b;
}

// Nested destructuring patterns
function nestedPattern({ point: [x, y] }: { point: [number, number] }): void {
  const a: number = x;
  const b: number = y;
}

// Object destructuring with defaults
function objectDefaultPattern({ a = 0 }: { a?: number }): void {
  const x: number = a;
}

// Object destructuring with rest
function objectRestPattern({
  a,
  ...rest
}: {
  a: number;
  b: string;
  c: boolean;
}): void {
  const x: number = a;
  const y: string = rest.b;
  const z: boolean = rest.c;
}

// Multiple destructured parameters
function multiPattern({ a }: { a: number }, [b]: [string]): void {
  const x: number = a;
  const y: string = b;
}

// Function type with pattern parameters (parsing only)
type FuncWithObjectParam = ({ x, y }: { x: number; y: number }) => void;
type FuncWithArrayParam = ([a, b]: [number, string]) => void;
