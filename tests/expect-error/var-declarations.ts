// `var` declarations in function bodies: hoisting, pre-initialization
// soundness, redeclaration, shadowing/collisions, loops, closures, and
// destructuring (SkipLabs/skjs#841).

// === 1. Function-scoped hoisting ===

export function hoistedFromIf(cond: boolean): number {
  if (cond) {
    var x = 1;
  } else {
    var x = 2;
  }
  return x;
}

export function hoistedFromBlock(): number {
  {
    var x = 1;
  }
  return x;
}

export function hoistedFromFor(): number {
  for (var i = 0; i < 3; i++) {}
  return i;
}

export function hoistedFromSwitch(k: 1 | 2): number {
  switch (k) {
    case 1:
      var y = 10;
      break;
    case 2:
      var y = 20;
      break;
  }
  return y;
}

export function hoistedFromTryCatch(): number {
  try {
    var x = 1;
  } catch {
    var x = 2;
  }
  return x;
}

export function hoistedFromTryFinally(): number {
  try {
    var x = 1;
  } finally {
    var y = 2;
  }
  return x + y;
}

export function hoistedDoesNotEscapeArrow(): void {
  const f = (): number => {
    var inner = 1;
    return inner;
  };
  // @skjs-expect-error This expression was expected to be of type 'void' or ignorable
  f();
  // @skjs-expect-error Cannot find name
  const bad = inner;
}

// === 2. Pre-initialization soundness ===

export function readBeforeInitError(): number {
  // @skjs-expect-error Variable 'x' is used before being assigned
  const a = x;
  var x: number = 1;
  return a;
}

export function readBeforeInitInferredError(): number {
  // @skjs-expect-error Variable 'x' is used before being assigned
  const a = x;
  var x = 1;
  return a;
}

export function readBeforeInitUndefinedAllowed(): number | undefined {
  const a = x;
  var x: number | undefined = 1;
  return a;
}

export function readBeforeInitUndefinedNotNumber(): number {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: number = x;
  var x: number | undefined = 1;
  return a;
}

export function conditionalHoistUnassignedError(cond: boolean): number {
  if (cond) {
    var x = 1;
  }
  // @skjs-expect-error Variable 'x' is used before being assigned
  return x;
}

export function conditionalHoistUndefinedAllowed(
  cond: boolean,
): number | undefined {
  if (cond) {
    var x: number | undefined = 1;
  }
  return x;
}

export function selfReferencingInitError(): number {
  // @skjs-expect-error Variable 'x' is used before being assigned
  var x: number = x;
  return x;
}

export function writeBeforeDeclThenRead(): number {
  x = 1;
  var x: number;
  return x;
}

export function writeWrongTypeBeforeDecl(): void {
  // @skjs-expect-error Type is not assignable to the variable's type
  x = "bad";
  var x: number = 1;
}

// === 3. Closures capturing hoisted `var` ===

// Soundness: tsc accepts reading an unassigned `var` inside a closure before
// initialization; SKJS rejects it (TS2454).
export function closureCapturesUninitVar(): number {
  // @skjs-expect-error Variable 'x' is used before being assigned
  const get = (): number => x;
  const r = get();
  var x: number = 1;
  return r;
}

export function closureCapturesUninitUndefinedVar(): number | undefined {
  const get = (): number | undefined => x;
  var x: number | undefined = 1;
  return get();
}

export function closureCapturesInitializedVar(): number {
  var x: number = 1;
  const get = (): number => x;
  return get();
}

// === 4. Same-scope redeclaration & TS2403 ===

export function redeclareSameAnnotatedType(): number {
  var x: number = 1;
  var x: number = 2;
  return x;
}

export function redeclareSameInferredType(): number {
  var x = 1;
  var x = 2;
  return x;
}

export function redeclareInferredThenAnnotated(): number {
  var x = 1;
  var x: number = 2;
  return x;
}

export function redeclareNoInitPreservesNarrowing(cond: boolean): number {
  var x: number | string = 1;
  if (cond) {
    var x: number | string;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

export function redeclareNoInitKeepsNarrowedFlow(cond: boolean): number {
  var x: number | string = 1;
  if (typeof x === "number") {
    if (cond) {
      var x: number | string;
    }
    return x;
  }
  return 0;
}

export function redeclareMismatchedAnnotatedType(): void {
  var x: number = 1;
  // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'x' must be of type 'number', but here has type 'string'
  var x: string = "a";
}

export function redeclareMismatchedInferredType(): void {
  var x = 1;
  // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'x' must be of type 'number', but here has type 'string'
  var x = "a";
}

export function redeclareMismatchedAcrossBranches(cond: boolean): void {
  if (cond) {
    var x = 1;
  } else {
    // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'x' must be of type 'number', but here has type 'string'
    var x = "a";
  }
}

export function hoistedVarPostMergeWriteChecked(cond: boolean): void {
  if (cond) {
    var x = 1;
  } else {
    var x = 2;
  }
  // @skjs-expect-error Type is not assignable to the variable's type
  x = "bad";
}

export function redeclareUnionThenNarrow(): void {
  var x: number | string = 1;
  // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'x' must be of type 'number | string', but here has type 'number'
  var x: number = 2;
}

export function redeclareNarrowThenUnion(): void {
  var x: number = 1;
  // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'x' must be of type 'number', but here has type 'number | string'
  var x: number | string = 2;
}

export function redeclareParamSameType(p: number): number {
  var p: number = 2;
  return p;
}

export function redeclareParamNoInit(p: number): number {
  var p: number;
  return p;
}

export function redeclareParamMismatchedType(p: number): void {
  // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'p' must be of type 'number', but here has type 'string'
  var p: string = "a";
}

// === 5. Collisions with let / const & legal shadowing ===

export function varShadowedByInnerLet(): number {
  var x = 1;
  {
    let x = "hello";
    const s: string = x;
  }
  return x;
}

export function hoistedVarShadowedBySiblingConst(): number {
  {
    var x = 1;
  }
  {
    const x = "hello";
    const s: string = x;
  }
  return x;
}

export function letThenVarSameScopeError(): void {
  let x = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  var x = 2;
}

export function varThenLetSameScopeError(): void {
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  var x = 1;
  let x = 2;
}

export function outerLetInnerVarError(): void {
  let x = 1;
  {
    // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
    var x = 2;
  }
}

export function enclosingBlockConstInnerVarError(): void {
  {
    const x = "a";
    {
      // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
      var x = 1;
    }
  }
}

export function catchParamCollidesWithVar(): void {
  try {
    throw new Error("boom");
  } catch (e) {
    // @skjs-expect-error Cannot redeclare block-scoped variable 'e'
    var e = 1;
  }
}

// === 6. Loops & loop-closure capture soundness ===

export function loopClosureSharedVar(): Array<() => number> {
  const fns: Array<() => number> = [];
  for (var i = 0; i < 3; i++) {
    fns.push(() => i);
  }
  return fns;
}

export function loopClosureVarNarrowedWidens(): Array<() => number> {
  const fns: Array<() => number> = [];
  for (var i = 0; i < 3; i++) {
    var v: number | string = i;
    if (typeof v === "number") {
      // @skjs-expect-error Argument is not assignable to the parameter's type
      fns.push(() => v);
    }
    v = "s";
  }
  return fns;
}

export function forOfVarUnassignedAfterLoop(xs: number[]): number {
  for (var x of xs) {
    const n: number = x;
  }
  // @skjs-expect-error Variable 'x' is used before being assigned
  return x;
}

export function forOfVarInitializedBeforeLoop(xs: number[]): number {
  var x: number = 0;
  for (var x of xs) {
    const n: number = x;
  }
  return x;
}

export function forOfVarTypeMismatch(xs: number[]): void {
  var x: string = "";
  // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'x' must be of type 'string', but here has type 'number'
  for (var x of xs) {
    const _ = x;
  }
}

export function forInVarUnassignedAfterLoop(o: { a: number }): string {
  for (var k in o) {
    const s: string = k;
  }
  // @skjs-expect-error Variable 'k' is used before being assigned
  return k;
}

export function forInVarInitializedBeforeLoop(o: { a: number }): string {
  var k: string = "";
  for (var k in o) {
    const s: string = k;
  }
  return k;
}

// === 7. Destructuring `var` ===

export function destructuringVarHoisted(
  cond: boolean,
  p: { a: number; b: string },
): number {
  if (cond) {
    var { a, b } = p;
  } else {
    var { a, b } = { a: 0, b: "" };
  }
  return a;
}

export function destructuringVarUnassignedError(
  cond: boolean,
  p: { a: number; b: string },
): number {
  if (cond) {
    var { a, b } = p;
  }
  // @skjs-expect-error Variable 'a' is used before being assigned
  return a;
}

export function destructuringVarArrayHoisted(cond: boolean): number {
  if (cond) {
    var [a, b]: [number, string] = [1, "x"];
  } else {
    var [a, b]: [number, string] = [2, "y"];
  }
  return a;
}

export function destructuringVarRedeclareMismatch(): void {
  var a: number = 1;
  // @skjs-expect-error Subsequent variable declarations must have the same type. Variable 'a' must be of type 'number', but here has type 'string'
  var { a } = { a: "bad" };
}
