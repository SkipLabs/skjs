// Readonly-to-mutable field assignment soundness tests.
//
// TypeScript allows assigning readonly fields where mutable fields are
// expected (structural typing is unsound for readonly). SKJS currently
// matches this behavior, but once fields have separate get/set types,
// these should be rejected: the contravariant set check (f2.set <: f1.set)
// would fail because readonly fields have set=bottom.

// ============================================================
// Case 1: Readonly to mutable — bypassing readonly protection
// TODO: reject once set type is enforced
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
  // TODO: should be rejected — readonly field passed where mutable field expected
  // @skjs-expect-error Invalid call
  mutatePet(r);
}

// ============================================================
// Case 2: Readonly field in generic context
// TODO: reject once set type is enforced
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
  // TODO: should be rejected — readonly value passed where mutable value expected
  // @skjs-expect-error Invalid call
  setBoxValue(rb, "mutated");
}

// ============================================================
// Case 3: Readonly literal tag widened through mutable alias
// TODO: reject once set type is enforced
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
  // TODO: should be rejected — readonly "a" tag passed where mutable string expected
  // @skjs-expect-error Invalid call
  changeTag(narrow);
}

// ============================================================
// Case 4: Discriminated union broken by mutable alias
// TODO: reject once set type is enforced
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
  // TODO: should be rejected — readonly discriminant passed where mutable field expected
  // Allows corrupting the discriminant used for union narrowing
  // @skjs-expect-error Invalid call
  breakDiscriminant(s);
}

// ============================================================
// Case 5: Readonly tuple field to mutable
// TODO: reject once set type is enforced
// ============================================================

function testReadonlyTupleField(): void {
  // @skjs-expect-error Invalid annotation
  const obj: { readonly pair: [string, number] } = { pair: ["a", 1] };
  // TODO: should be rejected — readonly pair assigned to mutable pair
  // @skjs-expect-error Invalid annotation
  const mutable_alias: { pair: [string, number] } = obj;
  mutable_alias.pair = ["b", 2];
}

// ============================================================
// Case 6: Readonly callback field to mutable
// TODO: reject once set type is enforced
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
  // TODO: should be rejected — readonly handler passed where mutable handler expected
  // @skjs-expect-error Invalid call
  replaceHandler(rc);
}
