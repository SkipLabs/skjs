// Test this parameter rules

// this parameter in regular function definition (not supported yet)
// @skjs-expect-error TODO: support this parameter
function withThisParam(this: string, x: number): void {}

// this parameter in function type
type FuncWithThis = (this: string, x: number) => void;

// this parameter forbidden in arrow function (TypeScript error)
function testArrowFunction(): void {
  // @ts-expect-error Parameter this forbidden in anonymous functions
  const f = (this: string, x: number): void => {};
}

// Function type with this parameter can be used
function takesCallback(f: (this: string, x: number) => void): void {
  // TODO: Use f when .call() is supported
}

// this parameter must be first in methods
class MethodWithThisOrder {
  // @skjs-expect-error Parameter named this must be the first one
  method(x: number, this: string): void {}
}

// this parameter can be first in methods (but not yet supported)
class MethodWithThisFirst {
  // @skjs-expect-error TODO: support this parameter
  method(this: string, x: number): void {}
}
