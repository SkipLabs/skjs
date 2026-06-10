// Edge cases for type intersection and recursive type inference.

// ============================================================
// 1. Self-referential types through function fields
//    Recursive types where the self-reference goes through function
//    parameter or return types rather than plain object fields.
// ============================================================

type FnNode = null | { apply: (x: FnNode) => FnNode };

function testFnNodeIntersection(): void {
  let x: FnNode = null;
  x = { apply: (n: FnNode) => n };
  const y: FnNode = x;
}

function buildFnNode<T extends FnNode>(initial: T): FnNode {
  let result: FnNode = initial;
  result = { apply: (_n: FnNode) => result };
  return result;
}

// Self-referential purely through function types (no non-function fields)
interface PureFnSelfRef {
  apply(f: PureFnSelfRef): PureFnSelfRef;
}

function testPureFnSelfRefGeneric<T extends PureFnSelfRef>(
  x: T,
): PureFnSelfRef {
  return x;
}

function testPureFnSelfRefLocal(): PureFnSelfRef {
  let x: PureFnSelfRef = { apply: (f: PureFnSelfRef) => f };
  while (true) {
    x = { apply: (f: PureFnSelfRef) => x };
    break;
  }
  return x;
}

// Self-referential interface with method
interface SelfHandler {
  handle(input: SelfHandler): SelfHandler;
}

function testSelfHandler<T extends SelfHandler>(x: T): SelfHandler {
  return x;
}

// ============================================================
// 2. Mutable field covariance
//    Object fields are covariant in structural subtyping: {pet: Dog}
//    is assignable to {pet: Animal}. This is unsound (a write through
//    the wider type could violate the narrower type) but matches TS.
//    TODO: reject once fields have separate get/set types.
// ============================================================

interface Animal {
  name: string;
}
interface Dog extends Animal {
  breed: string;
}

function fixRex(arg: { name: "Rex"; breed: "Lab" }): void {}

function testMutableFieldCovariance(): void {
  const obj = { pet: { name: "Rex", breed: "Lab" } };
  fixRex(obj.pet);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const dogBox: { pet: Dog } = obj;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const animalBox: { pet: Animal } = dogBox;
}

// Nested mutable field covariance
function testNestedMutableCovariance(): void {
  const obj = { value: { name: "Rex", breed: "Lab" } };
  fixRex(obj.value);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const inner: { value: Dog } = obj;
  const outer: { box: { value: Dog } } = { box: inner };
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const widened: { box: { value: Animal } } = outer;
}

// ============================================================
// 3. Recursive type patterns
//    Types with recursive references through arrays and index signatures.
// ============================================================

type TreeNode437 = {
  value: number;
  children: Array<TreeNode437>;
};

function testTreeNode437(): TreeNode437 {
  const leaf: TreeNode437 = { value: 1, children: [] };
  const branch: TreeNode437 = { value: 0, children: [leaf] };
  return branch;
}

type JsonValue437 =
  | string
  | number
  | boolean
  | null
  | JsonObject437
  | JsonArray437;
type JsonObject437 = { [key: string]: JsonValue437 };
type JsonArray437 = Array<JsonValue437>;

function processJson437<T extends JsonValue437>(x: T): JsonValue437 {
  return x;
}

function testJsonGeneric437(): void {
  const result: JsonValue437 = processJson437({
    name: "test",
    nested: { value: 42 },
  });
}

// ============================================================
// 4. Nested generic constraint intersection
//    When a type variable has a nested constraint (Wrapper<StrOrNum>)
//    and is instantiated with a narrower type (Wrapper<string>),
//    the constraint intersection must preserve field types correctly.
// ============================================================

interface Box437<T> {
  v: T;
}
type StrOrNum437 = string | number;

interface Wrapper437<T> {
  inner: Box437<T>;
}

function idWrapped437<T extends Wrapper437<StrOrNum437>>(x: T): T {
  return x;
}

function fixHello(arg: { v: "hello" }): void {}

function testNestedConstraintIntersection437(): void {
  const obj = { inner: { v: "hello" } };
  fixHello(obj.inner);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const w: Wrapper437<string> = obj;
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = idWrapped437(w);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const s: string = r.inner.v;
}
