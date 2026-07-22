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

// this parameter in regular function definition
function withThisParam(this: MyContext, x: number): void {}

// a constructor cannot declare an explicit this parameter (TS2681)
class TestConstructorThis {
  x: number = 0;
  // @skjs-expect-error A constructor cannot have a 'this' parameter
  constructor(this: TestConstructorThis, n: number) {
    this.x = n;
  }
}
// The rejected `this` parameter must not cascade to construction sites: the
// user wrote `new TestConstructorThis(5)` correctly.
export function makeTestConstructorThis(): TestConstructorThis {
  return new TestConstructorThis(5);
}
