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

// === Arrow functions with destructuring ===

// Arrow with array destructuring
function testArrowArrayPattern(): void {
  const f = ([a, b]: [number, string]): string => {
    return b;
  };
}

// Arrow with object destructuring
function testArrowObjectPattern(): void {
  const f = ({ x, y }: { x: number; y: string }): number => {
    return x;
  };
}

// Arrow with nested destructuring
function testArrowNested(): void {
  const f = ({ point: [x, y] }: { point: [number, number] }): number => {
    return x + y;
  };
}

// Arrow with object default in param
function testArrowObjectDefault(): void {
  const f = ({ x = 0 }: { x?: number }): number => {
    return x;
  };
}

// Arrow with array rest in param
function testArrowArrayRest(): void {
  const f = ([a, ...rest]: [number, string, boolean]): void => {
    const x: number = a;
    const y: [string, boolean] = rest;
  };
}

// Arrow with object rest in param
function testArrowObjectRest(): void {
  const f = ({ a, ...rest }: { a: number; b: string; c: boolean }): void => {
    const x: number = a;
    const y: string = rest.b;
  };
}

// Arrow with multiple destructured params
function testArrowMultiParam(): void {
  const f = ([a]: [number], { b }: { b: string }): void => {
    const x: number = a;
    const y: string = b;
  };
}

// Arrow expression body with destructuring
function testArrowExprBody(): void {
  const f = ([a, b]: [number, number]): number => a + b;
}

// Arrow without type annotation
function testArrowNoAnnotation(): void {
  const arr: [number, string][] = [];
  // @skjs-expect-error Missing type annotation
  arr.map(([a, b]) => a);
}

// === Optional, rest, and default parameters in arrows ===

// Arrow with optional parameter
function testArrowOptional(): void {
  const f = (x?: number): number => x ?? 0;
  void f;
}

// Arrow with default value
function testArrowDefaultValue(): void {
  const f = (x: number = 0): number => x;
  void f;
}

// Arrow with rest parameter
function testArrowRest(): void {
  const f = (...rest: number[]): number => rest.length;
  void f;
}

// Arrow with default value, wrong type
function testArrowDefaultWrongType(): void {
  // @skjs-expect-error Default value doesn't have the expected type
  const f = (x: number = "hello"): number => x;
  void f;
}

// Arrow with both optional and default
function testArrowOptionalAndDefault(): void {
  // @skjs-expect-error A parameter cannot both be optional and have a default value
  const f = (x?: number = 0): void => {
    void x;
  };
  void f;
}

// Required parameter cannot follow optional
// @skjs-expect-error This parameter is not optional
function requiredAfterOptional(x?: number, y: string): void {
  void x;
  void y;
}

// Required parameter cannot follow optional (in arrow)
function testArrowRequiredAfterOptional(): void {
  // @skjs-expect-error This parameter is not optional
  const f = (x?: number, y: string): void => {
    void x;
    void y;
  };
  void f;
}

// Function type with pattern parameters (parsing only)
type FuncWithObjectParam = ({ x, y }: { x: number; y: number }) => void;
type FuncWithArrayParam = ([a, b]: [number, string]) => void;
