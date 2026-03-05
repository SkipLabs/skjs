// Tests that subtyping errors involving setter checks suggest making
// the field readonly, in various subtyping positions.

function test(): void {}

// Return type position
function testReturn(x: { x: number }): { x: number | string } {
  // @skjs-expect-error Invalid return type
  return x;
}

// Parameter position
function testParam(x: { x: number | string }): void {}
function testParamCall(x: { x: number }): void {
  // @skjs-expect-error Invalid call
  testParam(x);
}

// Variable assignment position
function testAssign(x: { x: number }): void {
  // @skjs-expect-error Invalid annotation
  const y: { x: number | string } = x;
}

// Generic context
interface Box<T> {
  value: T;
}
function testGeneric(x: Box<number>): Box<number | string> {
  // @skjs-expect-error Invalid return type
  return x;
}

// Index signature
function testIndex(x: { [k: string]: number }): {
  [k: string]: number | string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}
