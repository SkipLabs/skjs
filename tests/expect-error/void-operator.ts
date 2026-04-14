// Valid: void always returns undefined
function testVoid(): undefined {
  return void 0;
}
function testVoidExpr(x: number): undefined {
  return void x;
}
function testVoidString(): undefined {
  return void "hello";
}

// Valid: void in expression context
const a: undefined = void 0;
const b: undefined = void (1 + 2);

// Valid: void used to ignore an unused parameter
function callback(event: string): undefined {
  return void event;
}

// Error: void result is undefined, not assignable to number
// @skjs-expect-error Invalid definition: value type is not compatible with type annotation
const c: number = void 0;

// Error: void result is undefined, not assignable to string
// @skjs-expect-error Invalid definition: value type is not compatible with type annotation
const d: string = void "hello";
