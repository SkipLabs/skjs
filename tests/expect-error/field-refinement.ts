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
// 5. Number literal discriminant (now refines)
// ============================================================

type Result = { code: 0; data: string } | { code: 1; error: string };

function testNumberDiscriminant(r: Result): void {
  if (r.code === 0) {
    // No refinement on number literal field yet (only strings)
    // @skjs-expect-error Invalid annotation
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
    // @skjs-expect-error Invalid annotation
    const n: { tag: null; vn: string } = x;
  }
}

function testFieldNullElimination(x: NullableTag): void {
  if (x.tag !== null) {
    // @skjs-expect-error Invalid annotation
    const n: { tag: "a"; va: number } = x;
  }
}

type UndefTag = { tag: "b"; vb: number } | { tag: undefined; vu: string };

function testFieldUndefinedRefinement(x: UndefTag): void {
  if (x.tag === undefined) {
    // @skjs-expect-error Invalid annotation
    const n: { tag: undefined; vu: string } = x;
  }
}

function testFieldUndefinedElimination(x: UndefTag): void {
  if (x.tag !== undefined) {
    // @skjs-expect-error Invalid annotation
    const n: { tag: "b"; vb: number } = x;
  }
}
