// Test TypeScript's this parameter feature

type MyContext = { value: number };

// this parameter must be first parameter
class TestFirstParameter {
  // @skjs-expect-error 'this' is not allowed in this binding position
  // @skjs-expect-error A 'this' parameter must be the first parameter
  method(x: number, this: MyContext): void {}
}

// this parameter as first parameter
class TestThisFirst {
  // @skjs-expect-error 'this' parameters are not yet supported by SKJS
  method(this: MyContext, x: number): void {}
}

// this parameter forbidden in arrow functions
class TestArrowFunctions {
  method(): void {
    // @skjs-expect-error 'this' is not allowed in this binding position
    const f = (this: MyContext): void => {};
  }
}

// this parameter in function types
type FuncWithThis = (this: MyContext, x: number) => number;

// Function type with this parameter can be used
function takesCallback(f: (this: MyContext, x: number) => number): void {}

// this parameter in regular function definition (not supported yet)
// @skjs-expect-error 'this' parameters are not yet supported by SKJS
function withThisParam(this: MyContext, x: number): void {}
