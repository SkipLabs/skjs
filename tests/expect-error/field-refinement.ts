// Tests for type refinement on object field access patterns:
// obj.field === literal, obj.field === null, obj.field === undefined

// ============================================================
// 1. Baseline: local variable refinement works
// ============================================================

function testLocalNullRefinement(x: string | null): string {
  if (x === null) {
    const n: null = x;
    return "null";
  }
  return x;
}

function testLocalUndefinedRefinement(x: string | undefined): string {
  if (x === undefined) {
    const u: undefined = x;
    return "undef";
  }
  return x;
}

// ============================================================
// 2. obj.field === null / undefined (no refinement, no error)
// ============================================================

function testFieldNullComparison(obj: { val: string | null }): string {
  if (obj.val === null) {
    return "null";
  }
  return "not null";
}

function testFieldUndefinedComparison(obj: {
  val: string | undefined;
}): string {
  if (obj.val === undefined) {
    return "undef";
  }
  return "not undef";
}

function testFieldNullReversed(obj: { val: number | null }): number {
  if (null === obj.val) {
    return 0;
  }
  return 1;
}

// ============================================================
// 3. Discriminated union with "kind" field (works today)
// ============================================================

type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };

function testKindRefinement(s: Shape): number {
  if (s.kind === "circle") {
    return s.radius;
  }
  return s.side;
}

function testKindElimination(s: Shape): number {
  if (s.kind !== "circle") {
    return s.side;
  }
  return s.radius;
}

// ============================================================
// 4. Discriminated union with non-"kind" field (now refines)
// ============================================================

type Event =
  | { type: "click"; x: number; y: number }
  | { type: "key"; key: string };

function testNonKindFieldRefinement(e: Event): void {
  if (e.type === "click") {
    // Refinement now works on any discriminant field
    const c: { type: "click"; x: number; y: number } = e;
  }
}

function testNonKindFieldElimination(e: Event): void {
  if (e.type !== "click") {
    // Elimination works too
    const k: { type: "key"; key: string } = e;
  }
}

// ============================================================
// 5. Number literal discriminant
// ============================================================

type Result = { code: 0; data: string } | { code: 1; error: string };

function testNumberDiscriminant(r: Result): void {
  if (r.code === 0) {
    // Refinement now works on number literal fields
    const ok: { code: 0; data: string } = r;
  }
}

// ============================================================
// 6. Field with union of literals
// ============================================================

type TrafficLight =
  | { color: "red"; timer: number }
  | { color: "yellow"; timer: number }
  | { color: "green"; duration: number };

function testUnionLiteralFieldPositive(t: TrafficLight): void {
  if (t.color === "red") {
    // Refinement now works on any discriminant field
    const r: { color: "red"; timer: number } = t;
  }
}

function testUnionLiteralFieldElimination(t: TrafficLight): void {
  if (t.color !== "green") {
    // No elimination refinement either
    // @skjs-expect-error Invalid annotation
    const notGreen: { color: "red"; timer: number } = t;
  }
}

// ============================================================
// 7. "kind" field works, field access on narrowed type
// ============================================================

type Animal = { kind: "dog"; bark: boolean } | { kind: "cat"; purr: boolean };

function testKindRefinementFieldAccess(a: Animal): boolean {
  if (a.kind === "dog") {
    return a.bark;
  }
  return a.purr;
}

// ============================================================
// 8. Multiple branches, progressive elimination with "kind"
// ============================================================

type ABC =
  | { kind: "a"; va: number }
  | { kind: "b"; vb: string }
  | { kind: "c"; vc: boolean };

function testProgressiveElimination(x: ABC): void {
  if (x.kind === "a") {
    const v: number = x.va;
  } else if (x.kind === "b") {
    const v: string = x.vb;
  } else {
    const v: boolean = x.vc;
  }
}

// ============================================================
// 9. Null/undefined as field discriminant
// ============================================================

type NullableTag = { tag: "a"; va: number } | { tag: null; vn: string };

function testFieldNullRefinement(x: NullableTag): void {
  if (x.tag === null) {
    const n: { tag: null; vn: string } = x;
  }
}

function testFieldNullElimination(x: NullableTag): void {
  if (x.tag !== null) {
    const n: { tag: "a"; va: number } = x;
  }
}

type UndefTag = { tag: "b"; vb: number } | { tag: undefined; vu: string };

function testFieldUndefinedRefinement(x: UndefTag): void {
  if (x.tag === undefined) {
    const n: { tag: undefined; vu: string } = x;
  }
}

function testFieldUndefinedElimination(x: UndefTag): void {
  if (x.tag !== undefined) {
    const n: { tag: "b"; vb: number } = x;
  }
}

// ============================================================
// 10. Non-singleton comparison type refinement
// ============================================================

// --- Positive tests (refinement filters branches) ---

// P1: Basic — filter branch with no overlap
type Tagged10 = { tag: 0 | 1; a: string } | { tag: 2; b: number };

function testBasicNonSingletonFilter(obj: Tagged10, x: 0 | 1): void {
  if (obj.tag === x) {
    // { tag: 2 } filtered, .a accessible
    const a: string = obj.a;
  }
}

// P2: Partial overlap — kept branch field stays wide
type Wide10 = { field: 0 | 1 | 2 } | { field: 3 };

function testFieldStaysWide(obj: Wide10, x: 0 | 1): void {
  if (obj.field === x) {
    // { field: 3 } filtered, but field NOT narrowed to 0|1
    const f: 0 | 1 | 2 = obj.field;
  }
}

// P3: Three branches, x covers two singleton branches
type Tri10 =
  | { tag: 0; a: string }
  | { tag: 1; b: number }
  | { tag: 2; c: boolean };

function testThreeBranchFilter(obj: Tri10, x: 0 | 1): void {
  if (obj.tag === x) {
    // { tag: 2 } filtered; result is { tag:0; a } | { tag:1; b }
    // @skjs-expect-error Unbound field: a
    const a: string = obj.a;
  }
}

// P4: String union discriminant
type Str10 = { kind: "a" | "b"; x: number } | { kind: "c"; y: string };

function testStringNonSingletonFilter(obj: Str10, x: "a" | "b"): void {
  if (obj.kind === x) {
    // { kind: "c" } filtered
    const n: number = obj.x;
  }
}

// --- Negative tests (should error) ---

// N1: Cannot narrow field type to comparison type
function testCannotNarrowField(obj: Wide10, x: 0 | 1): void {
  if (obj.field === x) {
    // @skjs-expect-error Invalid annotation
    const narrow: 0 | 1 = obj.field;
  }
}

// N2: All branches overlap — no filtering, union stays full
type AllOverlap10 = { field: 0 | 1 } | { field: 1 | 2 };

function testAllBranchesOverlap(obj: AllOverlap10, x: 0 | 1): void {
  if (obj.field === x) {
    // Both branches overlap with 0|1
    // @skjs-expect-error Invalid annotation
    const b1: { field: 0 | 1 } = obj;
  }
}

// N3: Accessing filtered-branch-only field — should error
function testFilteredBranchAccess(obj: Tagged10, x: 0 | 1): void {
  if (obj.tag === x) {
    // @skjs-expect-error Unbound field: b
    const b: number = obj.b;
  }
}

// N4: !== with non-singleton — NO refinement
function testNotEqualsNoRefine(obj: Tagged10, x: 0 | 1): void {
  if (obj.tag !== x) {
    // @skjs-expect-error Invalid annotation
    const only2: { tag: 2; b: number } = obj;
  }
}

// N5: All branches match — cannot narrow to specific branch
type T10 = { field: 0 } | { field: 1 };

function testBothBranchesKept(obj: T10, x: 0 | 1): void {
  if (obj.field === x) {
    // @skjs-expect-error Invalid annotation
    const only0: { field: 0 } = obj;
  }
}

// --- Edge cases ---

// E1: RHS is full `number` type — overlaps everything, no filtering
type E10 = { tag: 0; a: string } | { tag: 1; b: number };

function testRhsFullNumber(obj: E10, x: number): void {
  if (obj.tag === x) {
    // number overlaps all branches — no filtering
    // @skjs-expect-error Invalid annotation
    const only0: { tag: 0; a: string } = obj;
  }
}

// E2: Else branch of === not erroneously narrowed
function testElseBranchNotNarrowed(obj: Tagged10, x: 0 | 1): void {
  if (obj.tag === x) {
    const a: string = obj.a;
  } else {
    // Else of === with non-singleton: no safe narrowing
    const full: Tagged10 = obj;
  }
}

// E3: && chain propagates non-singleton refinement
function testAndChain(obj: Tagged10, x: 0 | 1, cond: boolean): void {
  if (cond && obj.tag === x) {
    const a: string = obj.a;
  }
}
