// Per-field TVar isolation: each nested-object/primitive field gets its own
// TVar ('N). These TVars are independent — constraining one field's TVar
// does not affect another field's TVar.

// ============================================================
// 1. Two nested object fields — each independently prevents widening
// ============================================================

// Constraining functions that force literal types
function fixA(arg: { x: 1 }): void {}
function fixB(arg: { y: "hello" }): void {}

function testFieldAWidening(): void {
  const obj = { a: { x: 1 }, b: { y: "hello" } };
  fixA(obj.a);
  fixB(obj.b);
  // @skjs-expect-error Invalid annotation
  const t1: { a: { x: number } } = obj;
}

function testFieldBWidening(): void {
  const obj = { a: { x: 1 }, b: { y: "hello" } };
  fixA(obj.a);
  fixB(obj.b);
  // @skjs-expect-error Invalid annotation
  const t2: { b: { y: string } } = obj;
}

// ============================================================
// 2. Constraining one field does not pollute sibling
// ============================================================

function fixName(arg: { name: "Rex" }): void {}

function testNoPollution(): void {
  const obj = { first: { name: "Rex" }, second: { value: 42 } };
  // Constrain only `first` to have literal type
  fixName(obj.first);
  // `second` was NOT constrained — widening succeeds
  const t2: { second: { value: number } } = obj;
}

function testConstrainedFieldRejectsWidening(): void {
  const obj = { first: { name: "Rex" }, second: { value: 42 } };
  fixName(obj.first);
  // `first` is now locked to literal type — widening rejected
  // @skjs-expect-error Invalid annotation
  const t1: { first: { name: string } } = obj;
}

// ============================================================
// 3. Non-wrapped fields are unaffected
// ============================================================

function identity(x: string): string {
  return x;
}

function testNonWrappedField(): void {
  const obj = {
    nested: { x: 1 },
    computed: identity("a"),
  };
  // computed is not wrapped in per-field TVar (function call result)
  const s: string = obj.computed;
  // nested is wrapped — without constraining, widening still works
  const t: { nested: { x: number } } = obj;
}
