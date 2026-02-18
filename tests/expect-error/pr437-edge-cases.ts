// Edge cases for PR #437: type inference bugs in inter_ and field subtyping
// All cases pass both TypeScript (npx tsc --strict --noEmit) and SKJS.

// ============================================================
// 1. Self-referential TVar through function types
//    referencesTVarId doesn't traverse TFun params/returns,
//    but these pass because the self-reference pattern that triggers
//    infinite recursion occurs through object field types, not function types.
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
// 2. Deferred set check — mutable field covariance
//    With the set check removed, object fields are covariant (matching TS).
//    Array<T> remains invariant because Array has mutable methods.
// ============================================================

interface Animal {
  name: string;
}
interface Dog extends Animal {
  breed: string;
}

// TS allows mutable field covariance (structural typing unsoundness)
function testMutableFieldCovariance(): void {
  const dogBox: { pet: Dog } = { pet: { name: "Rex", breed: "Lab" } };
  const animalBox: { pet: Animal } = dogBox;
}

// Nested mutable field covariance
function testNestedMutableCovariance(): void {
  const inner: { value: Dog } = { value: { name: "Rex", breed: "Lab" } };
  const outer: { box: { value: Dog } } = { box: inner };
  const widened: { box: { value: Animal } } = outer;
}

// ============================================================
// 3. Recursive type patterns (inter_ recursion fix)
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
// 4. Constraint intersection — nested generic constraint
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

function testNestedConstraintIntersection437(): void {
  const w: Wrapper437<string> = { inner: { v: "hello" } };
  const r = idWrapped437(w);
  const s: string = r.inner.v;
}
