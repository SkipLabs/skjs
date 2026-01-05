// Test TypeScript's this parameter feature

type MyContext = { value: number };

// this parameter must be first parameter
class TestFirstParameter {
  // @skjs-expect-error Parameter named this must be the first one
  // @skjs-expect-error TODO: support this parameter
  method(x: number, this: MyContext): void {}
}

// this parameter as first parameter
class TestThisFirst {
  // @skjs-expect-error TODO: support this parameter
  method(this: MyContext, x: number): void {}
}

// this parameter forbidden in arrow functions
class TestArrowFunctions {
  method(): void {
    // @ts-expect-error Parameter this forbidden in anonymous functions
    const f = (this: MyContext): void => {};
  }
}

// this parameter in function types
type FuncWithThis = (this: MyContext, x: number) => number;

// Function type with this parameter can be used
function takesCallback(f: (this: MyContext, x: number) => number): void {}

// this parameter in regular function definition (not supported yet)
// @skjs-expect-error TODO: support this parameter
function withThisParam(this: MyContext, x: number): void {}
