// Error-detail rendering shapes for subtype failures (issue #672).

// Both sides are pure type parameters (no insts), so no frame renders a
// clause pair; the fall-back prints the type pair, anchored at the type
// parameters' declarations.
function id2<T, U>(x: T): U {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type 'T'
  // @skjs-expect-error-line3 is not assignable to type 'U'
  return x;
}

// A literal matching a tuple constraint checks, so it renders no pair at all
// (#914; behaviour pinned in tuple-constraint-literal.ts).
declare function g2<K extends [0, 1]>(x: K): K;
function tupleConstraint(): void {
  const r = g2([0, 1]);
}

// A genuinely mismatched operand gets the readable pair, and K's expanded
// constraint renders as the tuple it denotes rather than the object form
// listing every array method.
declare function fk<K extends [0, 1]>(x: K): K;
function nonTupleOperand(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '5'
  // @skjs-expect-error-line3 is not assignable to type '[0, 1]'
  const r = fk(5);
}

// Primitive literals render as TypeScript source syntax: the numeric literal
// type bare (`1`), the string literal type double-quoted (`"1"`), keeping the
// two sides of the mismatch distinguishable.
function indistinguishableLiteralKinds(x: 1): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '1'
  // @skjs-expect-error-line3 is not assignable to type '"1"'
  const y: "1" = x;
}

// An intersection with an extra member: the object form shows `foo` -- the
// member the failure is actually about -- and must keep doing so.
declare function hx<K extends [0, 1] & { foo: string }>(x: K): K;
function extraMemberShown(): void {
  const arg: [0, 1] = [0, 1];
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[0, 1]'
  // @skjs-expect-error-line3 is not assignable to type {
  const r = hx(arg);
}

// A readonly tuple expansion renders as the readonly tuple it is.
declare function gr<K extends readonly [0, 1]>(x: K): K;
function readonlyTupleConstraint(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[0, 2]'
  // @skjs-expect-error-line3 is not assignable to type 'readonly [0, 1]'
  const r = gr([0, 2]);
}

// A direct tuple annotation checks element-by-element, and the error names
// the element that was actually rejected — not the union the failed check
// grew the element's commitment variable into (issue #935).
function directTupleElementMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '2'
  // @skjs-expect-error-line3 is not assignable to type '1'
  const x: [0, 1] = [0, 2];
}

// The #935 fix is not literal-kind-specific: same-kind string and boolean
// literal elements name the rejected element too (tsc agrees).
function directTupleStringMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '"c"'
  // @skjs-expect-error-line3 is not assignable to type '"b"'
  const x: ["a", "b"] = ["a", "c"];
}

function directTupleBoolMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'true'
  // @skjs-expect-error-line3 is not assignable to type 'false'
  const x: [true, false] = [true, true];
}

// A union target element is named as the union, and the rejected literal as
// the source (tsc agrees).
function directTupleUnionTargetMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '2'
  // @skjs-expect-error-line3 is not assignable to type '0 | 1'
  const x: [0 | 1] = [2];
}

// A genuine union source is NOT set-subtracted against the target: `1 | 2`
// really is the source element, and tsc reports the whole union here too.
function directTupleUnionSource(decl: 1 | 2): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '1 | 2'
  // @skjs-expect-error-line3 is not assignable to type '1'
  const x: [1] = [decl];
}

// ...but the grown-state contamination is deeper than the top-level element:
// inside an object element, the failing field check grows the field's
// commitment variable, and the nested error still renders the union `0 | 1`
// where tsc reports `1` (#935 family, not fixed at depth).
function directTupleObjectFieldMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '0 | 1'
  // @skjs-expect-error-line3 is not assignable to type '0'
  const x: [{ a: 0 }, number] = [{ a: 1 }, 0];
}

// Same at a nested tuple element: tsc reports `1`, SKJS still renders the
// grown `0 | 1` (#935 family).
function directTupleNestedMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '0 | 1'
  // @skjs-expect-error-line3 is not assignable to type '0'
  const x: [[0], number] = [[1], 0];
}
