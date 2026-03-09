type tIndex = { [f: string]: number };

function expectsIndexedObject(_x: tIndex): void {}

function correctIndexReturnTypeGet(x: tIndex): number | undefined {
  return x["a"];
}

function correctIndexReturnTypeDot(x: tIndex): number | undefined {
  return x.a;
}

function incorrectIndexReturnTypeGet(x: tIndex): number {
  // @skjs-expect-error Invalid return type
  return x["a"];
}

function incorrectIndexReturnTypeDot(x: tIndex): number {
  // @skjs-expect-error Invalid return type
  return x.a;
}

// Test accessing non-existent property on regular object
function testRegularObjectAccess(): void {
  const regularObj = { x: 10, y: 20 };
  // @ts-expect-error Unbound field: z
  const invalid = regularObj.z;
}

type tIndex2 = { name: string; [k: number]: boolean };

function testMixedObjectNormalFieldCorrectDot(obj: tIndex2): string {
  return obj.name;
}

function testMixedObjectNormalFieldCorrectGet(obj: tIndex2): string {
  return obj["name"];
}

function testMixedObjectNormalFieldCorrectIndexing(
  obj: tIndex2,
): boolean | undefined {
  return obj[0];
}

function testMixedObjectNormalFieldIncorrectIndexing(obj: tIndex2): boolean {
  // @skjs-expect-error Invalid return type
  return obj[0];
}

function testMixedObjectNormalFieldIncorrectIndexingType(
  obj: tIndex2,
): boolean | string | undefined {
  // @ts-expect-error Invalid index key
  return obj.missing;
}

function canAccessFieldConstructor(
  obj: object,
  f: "constructor" | "banana",
): void {
  // @skjs-expect-error Unbound field: banana | constructor
  const whatever = obj[f];
}

function canUseConstructorAsFieldName(): object {
  return { constructor: 1 };
}

function canUseConstructorAsMethodName(): object {
  // @skjs-expect-error Missing return type annotation
  return { constructor() {} };
}

function canUseConstructorAsMethodName2(): object {
  return { constructor(): void {} };
}

function canHaveConstructorField(x: { constructor: string }): void {}

function canHaveConstructorMethod(x: { constructor(): void }): void {}

// @skjs-expect-error Missing return type annotation
function canHaveConstructorMethod2(x: { constructor() }): void {}

function constructor(): void {}

function numberIsAValidFieldNameInType(x: { 0: number }): number {
  return x[0];
}

function numberIsAValidFieldNameInValue(): { 0: number } {
  return { 0: 1 };
}

function shorthandFromConst(): void {
  const a = 1;
  const x: { a: number } = { a };
}

function extendWithSpread(x: { f1: number; f2: string }): {
  f0: boolean;
  f1: number;
  f2: number;
  f3: string;
} {
  // @skjs-expect-error Invalid return type
  return { f0: true, ...x, f2: 0, f3: "a" };
}

// Spread soundness: fields after the last spread are safe
function spreadFieldsAfterSpread(): { a: string } {
  const obj: {} = { a: 1 };
  return { ...obj, a: "" };
}

// Spread soundness: spread with no fields before it
function spreadNoFieldsBefore(): { a: number; b: string } {
  const obj: { a: number } = { a: 1 };
  return { ...obj, b: "hello" };
}

// Spread soundness: fields before spread are forgotten
function spreadFieldsBeforeSpread(): { a: string } {
  const obj: {} = { a: 1 };
  // @skjs-expect-error Invalid return type
  return { a: "", ...obj };
}

// Spread soundness: multiple spreads, only last spread + trailing fields safe
function spreadMultipleSpreads(): {
  a: number;
  b: number;
  c: number;
  d: number;
} {
  const obj1: { b: number } = { b: 1 };
  const obj2: { c: number } = { c: 2 };
  // @skjs-expect-error Invalid return type
  return { a: 0, ...obj1, ...obj2, d: 0 };
}

// Spread soundness: fields before spread with typed spread are forgotten
function spreadFieldsBeforeTypedSpread(x: { f1: number; f2: string }): {
  f0: boolean;
  f1: number;
  f2: number;
  f3: string;
} {
  // @skjs-expect-error Invalid return type
  return { f0: true, ...x, f2: 0, f3: "a" };
}
