type tIndex = { [f: string]: number };

function expectsIndexedObject(_x: tIndex): void {}

function correctIndexReturnTypeGet(x: tIndex): number | undefined {
  return x["a"];
}

function correctIndexReturnTypeDot(x: tIndex): number | undefined {
  return x.a;
}

function incorrectIndexReturnTypeGet(x: tIndex): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x["a"];
}

function incorrectIndexReturnTypeDot(x: tIndex): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
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
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return obj[0];
}

function testMixedObjectNormalFieldIncorrectIndexingType(
  obj: tIndex2,
): boolean | string | undefined {
  // @skjs-expect-error This index key is not assignable to the index signature: expected number, got string
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
  // @skjs-expect-error Function 'constructor' must have an explicit return type annotation
  return { constructor() {} };
}

function canUseConstructorAsMethodName2(): object {
  return { constructor(): void {} };
}

function canHaveConstructorField(x: { constructor: string }): void {}

function canHaveConstructorMethod(x: { constructor(): void }): void {}

// @skjs-expect-error Function 'constructor' must have an explicit return type annotation
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
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
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
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
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
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: 0, ...obj1, ...obj2, d: 0 };
}

// Spread soundness: fields before spread with typed spread are forgotten
function spreadFieldsBeforeTypedSpread(x: { f1: number; f2: string }): {
  f0: boolean;
  f1: number;
  f2: number;
  f3: string;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { f0: true, ...x, f2: 0, f3: "a" };
}

// Spread with optional field overlap → union types, non-optional
function spreadOptionalOverlap(): { a: string | number } {
  const obj: { a?: number } = {};
  return { a: "", ...obj };
}

// Spread with optional field, assigned to narrow type → error
function spreadOptionalOverlapNarrow(): { a: string } {
  const obj: { a?: number } = {};
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: "", ...obj };
}

// Spread with index signature → union types
function spreadIndexOverlap(): { a: string | number } {
  const obj: { [k: string]: number } = {};
  return { a: "", ...obj };
}

// Spread with index signature, assigned to narrow type → error
function spreadIndexOverlapNarrow(): { a: string } {
  const obj: { [k: string]: number } = {};
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { a: "", ...obj };
}

// Spread with required field → spread wins completely
function spreadRequiredOverwrites(): { a: number } {
  const obj: { a: number } = { a: 1 };
  return { a: 0, ...obj };
}

// Both spreads have optional field → result stays optional
function spreadOptionalThenOptional(): { a?: string | number } {
  const obj1: { a?: string } = {};
  const obj2: { a?: number } = {};
  return { ...obj1, ...obj2 };
}

// Optional field spread + index signature spread → result stays optional
function spreadOptionalThenIndex(): { a?: string | number } {
  const obj1: { a?: string } = {};
  const obj2: { [k: string]: number } = {};
  return { ...obj1, ...obj2 };
}

function spreadIndexThenOptional(): { a?: string | number } {
  const obj1: { [k: string]: number } = {};
  const obj2: { a?: string } = {};
  return { ...obj1, ...obj2 };
}

// Spread with no matching field or index → union with Top (structural subtyping)
function spreadUnrelatedFieldUnionTop(): void {
  const obj: { b: number } = { b: 1 };
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const result: { a: string } = { a: "hello", ...obj };
}

// Spread forgets set type — readonly fields become mutable
function spreadReadonlyBecomesMutable(): void {
  const obj: { readonly a: number } = { a: 1 };
  const result = { ...obj };
  result.a = 42;
}

// Stricter optional field subtyping: sub without the optional field (and no
// index) must not satisfy super's optional field. Otherwise:
//   const obj = { x: 1, a: 2 };
//   const obj2 = missingOptional(obj); // obj2: { x: number, a?: string }
//   obj2.a  // typed string | undefined, actually number — unsound
function missingOptional(x: { x: number }): { x: number; a?: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function spreadIndexThenIndex(): { [k: string]: string | number } {
  const obj1: { [k: string]: number } = {};
  const obj2: { [k: string]: string } = {};
  return { ...obj1, ...obj2 };
}
