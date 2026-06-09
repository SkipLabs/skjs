// Readonly-to-mutable field assignment soundness tests.
//
// TypeScript allows assigning readonly fields where mutable fields are
// expected (structural typing is unsound for readonly). SKJS correctly
// rejects these cases: fields have separate get/set types, and the
// contravariant set check (f2.set <: f1.set) fails because readonly
// fields have set=bottom.

// ============================================================
// Case 1: Readonly to mutable — bypassing readonly protection
// ============================================================

interface ReadonlyPet {
  readonly name: string;
}
interface MutablePet {
  name: string;
}

function mutatePet(p: MutablePet): void {
  p.name = "changed";
}

function testReadonlyToMutable(): void {
  const r: ReadonlyPet = { name: "original" };
  // Correctly rejected — readonly field passed where mutable field expected
  // @skjs-expect-error Invalid call
  mutatePet(r);
}

// ============================================================
// Case 2: Readonly field in generic context
// ============================================================

interface MutableBox<T> {
  value: T;
}

interface ReadonlyBox<T> {
  readonly value: T;
}

function setBoxValue<T>(box: MutableBox<T>, val: T): void {
  box.value = val;
}

function testReadonlyBoxToMutableBox(): void {
  const rb: ReadonlyBox<string> = { value: "immutable" };
  // Correctly rejected — readonly value passed where mutable value expected
  // (error includes: "This would not be an error if this field were readonly")
  // @skjs-expect-error Invalid call
  // @skjs-expect-error-line2 This would not be an error if this field were readonly
  setBoxValue(rb, "mutated");
}

// ============================================================
// Case 3: Readonly literal tag widened through mutable alias
// ============================================================

interface NarrowObj {
  readonly tag: "a";
  data: string;
}

interface WideObj {
  tag: string;
  data: string;
}

function changeTag(obj: WideObj): void {
  obj.tag = "b";
}

function testNarrowToWide(): void {
  const narrow: NarrowObj = { tag: "a", data: "hello" };
  // Correctly rejected — readonly "a" tag passed where mutable string expected
  // @skjs-expect-error Invalid call
  changeTag(narrow);
}

// ============================================================
// Case 4: Discriminated union broken by mutable alias
// ============================================================

type Shape =
  | { readonly type_: "circle"; radius: number }
  | { readonly type_: "square"; side: number };

interface MutableType {
  type_: string;
}

function breakDiscriminant(s: MutableType): void {
  s.type_ = "triangle";
}

function testBrokenDiscriminant(s: Shape): void {
  // Correctly rejected — readonly discriminant passed where mutable field expected
  // Prevents corrupting the discriminant used for union narrowing
  // @skjs-expect-error Invalid call
  breakDiscriminant(s);
}

// ============================================================
// Case 5: Readonly tuple field to mutable
// Note: errors here are from per-field TVar inference, not the set check
// ============================================================

function testReadonlyTupleField(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const obj: { readonly pair: [string, number] } = { pair: ["a", 1] };
  // Rejected — readonly pair assigned to mutable pair (via per-field TVar inference)
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const mutable_alias: { pair: [string, number] } = obj;
  mutable_alias.pair = ["b", 2];
}

// ============================================================
// Case 6: Readonly callback field to mutable
// ============================================================

interface ReadonlyCallback {
  readonly handler: (x: string) => void;
}

interface MutableCallback {
  handler: (x: string) => void;
}

function replaceHandler(obj: MutableCallback): void {
  obj.handler = (_x: string) => {};
}

function testReadonlyCallbackToMutable(): void {
  const rc: ReadonlyCallback = { handler: (x: string) => console.log(x) };
  // Correctly rejected — readonly handler passed where mutable handler expected
  // @skjs-expect-error Invalid call
  replaceHandler(rc);
}
