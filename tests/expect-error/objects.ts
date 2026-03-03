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
  // @ts-expect-error Invalid index key: expected number, got string
  return obj.missing;
}

function canAccessFieldConstructor(
  obj: object,
  f: "constructor" | "banana",
): void {
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
  return { f0: true, ...x, f2: 0, f3: "a" };
}
