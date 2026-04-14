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
function callback(event: string): void {
  void event;
}

// Valid: void to ignore a function's return value
function getNumber(): number {
  return 42;
}
function ignoreReturn(): void {
  void getNumber();
}

// Valid: void applied to a void-typed expression
function returnsVoid(): void {}
function voidOnVoid(): void {
  void returnsVoid();
}

// Valid: void in arrow function body
function testArrow(): () => undefined {
  return () => void getNumber();
}

// Valid: nested void
function testNested(): undefined {
  return void void 0;
}

// Valid: void with async (fire-and-forget)
async function asyncFunc(): Promise<number> {
  return 1;
}
function fireAndForget(): void {
  void asyncFunc();
}

// Precedence: void 0 + 1 parses as (void 0) + 1
function testPrecedence(): number {
  // @skjs-expect-error Invalid + operation
  return void 0 + 1;
}

// Error: void result is undefined, not assignable to number
// @skjs-expect-error Invalid definition: value type is not compatible with type annotation
const c: number = void 0;

// Error: void result is undefined, not assignable to string
// @skjs-expect-error Invalid definition: value type is not compatible with type annotation
const d: string = void "hello";
