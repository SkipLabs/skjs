// Unsoundness from deferred set check (PR #437 commit 4).
//
// On getter-setters branch: readonly fields have set=bottom, writable have set=type.
// The set check (f2.set <: f1.set) was removed, allowing readonly fields to be
// passed where writable fields are expected. All cases below pass TS (which is
// unsound for readonly fields) and SKJS (with deferred set check).
//
// Before the deferred set check, SKJS correctly rejected cases 1,2,3,4,5,6
// with "Invalid call" or "Invalid annotation" errors.
//
// FIXME: Restore set check to catch these once TField::inter is fixed.

// ============================================================
// Case 1: Readonly to mutable — bypassing readonly protection
// FIXME: Should be rejected (set: string <: bottom fails)
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
  // FIXME: readonly name (set=bottom) passed where mutable name (set=string) expected
  mutatePet(r);
}

// ============================================================
// Case 2: Readonly field in generic context
// FIXME: Should be rejected (set: string <: bottom fails)
// ============================================================

interface Box<T> {
  value: T;
}

interface ReadonlyBox<T> {
  readonly value: T;
}

function setBoxValue<T>(box: Box<T>, val: T): void {
  box.value = val;
}

function testReadonlyBoxToMutableBox(): void {
  const rb: ReadonlyBox<string> = { value: "immutable" };
  // FIXME: ReadonlyBox.value (set=bottom) passed where Box.value (set=string) expected
  setBoxValue(rb, "mutated");
}

// ============================================================
// Case 3: Readonly literal tag widened through mutable alias
// FIXME: Should be rejected (set: string <: bottom fails)
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
  // FIXME: readonly "a" tag (set=bottom) passed where mutable string tag expected
  changeTag(narrow);
}

// ============================================================
// Case 4: Discriminated union broken by mutable alias
// FIXME: Should be rejected (set: string <: bottom fails)
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
  // FIXME: readonly discriminant (set=bottom) passed where mutable field expected
  // This allows corrupting the discriminant used for union narrowing
  breakDiscriminant(s);
}

// ============================================================
// Case 5: Readonly tuple field to mutable
// FIXME: Should be rejected (set: [string,number] <: bottom fails)
// ============================================================

function testReadonlyTupleField(): void {
  const obj: { readonly pair: [string, number] } = { pair: ["a", 1] };
  // FIXME: readonly pair (set=bottom) assigned to mutable pair (set=[string,number])
  const mutable_alias: { pair: [string, number] } = obj;
  mutable_alias.pair = ["b", 2];
}

// ============================================================
// Case 6: Readonly callback field to mutable
// FIXME: Should be rejected (set: (string)=>void <: bottom fails)
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
  // FIXME: readonly handler (set=bottom) passed where mutable handler expected
  replaceHandler(rc);
}
