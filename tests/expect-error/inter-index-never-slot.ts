// Regression tests for issue #800: intersecting incompatible index or
// named/index slots must not produce a self-inconsistent slot (get = never,
// live set) that still satisfies mutable views or accepts writes.
//
// In SKJS, `NeverIdx & NumIdx` and `NumIdx & StrIdx` intersect getters to
// `never`. Because `Closed<T>` uses never-valued string/symbol indexes and
// subtyping consults raw `index.set`, a live setter on a bottom-getter slot
// would allow laundering the intersection into a mutable `{ [k: string]: number }`
// view and mutating it.

type NeverIdx = { [k: string]: never };
type NumIdx = { [k: string]: number };
type StrIdx = { [k: string]: string };
type Inter = NeverIdx & NumIdx;

// ============================================================================
// Mutable views of incompatible index intersections (pinned pre-fix #800)
// ============================================================================

function testNeverAndNumIndexMutableView(x: Inter): void {
  // Pre-fix (#800): accepted because interIndex leaves set = number on a
  // get = never slot.
  const m: { [k: string]: number } = x;
  m.b = 1;
}

function testNumAndStrIndexMutableView(x: NumIdx & StrIdx): void {
  // Pre-fix (#800): accepted because interIndex leaves set = number | string
  // on a get = never slot.
  const m: { [k: string]: number } = x;
  m.b = 1;
}

function testClosedAndNumIndexMutableView(
  x: Closed<{ a: number }> & NumIdx,
): void {
  // Pre-fix (#800): accepted because Closed's never index meets NumIdx with
  // get = never, set = number.
  const m: { [k: string]: number } = x;
  m.b = 1;
}

// ============================================================================
// Named field meeting an incompatible index signature (pinned pre-fix #800)
// ============================================================================

function testNamedFieldWithNeverIndexWrite(
  x: { a: number } & { [k: string]: never },
): void {
  // Pre-fix (#800): accepted because interIndex leaves set = number on `a`.
  x.a = 1;
}

function testNamedFieldWithNeverIndexMutableView(
  x: { a: number } & { [k: string]: never },
): void {
  // Pre-fix (#800): accepted because `a` keeps set = number while get = never.
  const m: { a: number } = x;
  m.a = 1;
}

function testNamedFieldWithDisjointIndexWrite(
  x: { a: number } & { [k: string]: string },
): void {
  // Pre-fix (#800): accepted because interIndex leaves set = number | string
  // on `a` while get = never.
  x.a = 1;
}

// ============================================================================
// Direct access on never-get index stays rejected (never-index access rule)
// ============================================================================

function testDirectWriteAndReadOnInterRejected(x: Inter): void {
  // @ts-expect-error Property 'b' does not exist on this type
  x.b = 1;
}

function testDirectReadOnInterRejected(x: Inter): void {
  // @skjs-expect-error Property 'b' does not exist on this type
  const r = x.b;
}

// ============================================================================
// Valid uses that must keep working
// ============================================================================

function testInterIntoReadonlyViewAccepted(x: Inter): void {
  const r: { readonly [k: string]: number } = x;
}

function testDisjointIndexIntoReadonlyViewAccepted(x: NumIdx & StrIdx): void {
  const r: { readonly [k: string]: number } = x;
}

function testWritableArrayIntersectedWithReadonlyStaysMutable(
  x: number[] & ReadonlyArray<unknown>,
): void {
  x.push(1);
}

function testCompatibleIndexIntersectionStaysWritable(
  x: { [k: string]: number } & { readonly [k: string]: unknown },
): void {
  const m: { [k: string]: number } = x;
  m.b = 1;
}
