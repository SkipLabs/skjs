type tIndex = { [f: string]: number };

function expectsIndexedObject(_x: tIndex): void {}

function correctIndexReturnTypeGet(x: tIndex): number | undefined {
  return x["a"];
}

function correctIndexReturnTypeDot(x: tIndex): number | undefined {
  return x.a;
}

function incorrectIndexReturnTypeGet(x: tIndex): number {
  // @ts-expect-error Invalid return type
  return x["a"];
}

function incorrectIndexReturnTypeDot(x: tIndex): number {
  // @ts-expect-error Invalid return type
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
  // TODO: fix this
  // @ts-expect-error Invalid call
  return obj["name"];
}

function testMixedObjectNormalFieldCorrectIndexing(
  obj: tIndex2,
): boolean | undefined {
  return obj[0];
}

function testMixedObjectNormalFieldIncorrectIndexing(obj: tIndex2): boolean {
  // @ts-expect-error Invalid return type
  return obj[0];
}

function testMixedObjectNormalFieldIncorrectIndexingType(
  obj: tIndex2,
): boolean | string | undefined {
  // TODO: should be missing field
  // @ts-expect-error Invalid call
  return obj.missing;
}
