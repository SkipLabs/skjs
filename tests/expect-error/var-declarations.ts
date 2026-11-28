// `var` declarations in function bodies: hoisting, pre-initialization
// soundness, redeclaration, shadowing/collisions, loops, closures, and
// destructuring (SkipLabs/skjs#841).

// === 1. Function-scoped hoisting ===

export function hoistedFromIf(cond: boolean): number {
  if (cond) {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 1;
  } else {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 2;
  }
  // @skjs-expect-error Cannot find name
  return x;
}

export function hoistedFromBlock(): number {
  {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 1;
  }
  // @skjs-expect-error Cannot find name
  return x;
}

export function hoistedFromFor(): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  for (var i = 0; i < 3; i++) {}
  // @skjs-expect-error Cannot find name
  return i;
}

export function hoistedFromSwitch(k: 1 | 2): number {
  switch (k) {
    case 1:
      // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
      var y = 10;
      break;
    case 2:
      // @skjs-expect-error Cannot redeclare block-scoped variable 'y'
      // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
      var y = 20;
      break;
  }
  // @skjs-expect-error Cannot find name
  return y;
}

export function hoistedFromTryCatch(): number {
  try {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 1;
  } catch {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 2;
  }
  // @skjs-expect-error Cannot find name
  return x;
}

export function hoistedFromTryFinally(): number {
  try {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 1;
  } finally {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var y = 2;
  }
  // @skjs-expect-error Cannot find name
  return x + y;
}

export function hoistedDoesNotEscapeArrow(): void {
  const f = (): number => {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
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
  // @skjs-expect-error Variable 'x' is used before being assigned
  const a = x;
  var x: number | undefined = 1;
  return a;
}

export function readBeforeInitUndefinedNotNumber(): number {
  // @skjs-expect-error Variable 'x' is used before being assigned
  const a: number = x;
  var x: number | undefined = 1;
  return a;
}

export function conditionalHoistUnassignedError(cond: boolean): number {
  if (cond) {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 1;
  }
  // @skjs-expect-error Cannot find name
  return x;
}

export function conditionalHoistUndefinedAllowed(
  cond: boolean,
): number | undefined {
  if (cond) {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x: number | undefined = 1;
  }
  // @skjs-expect-error Cannot find name
  return x;
}

export function selfReferencingInitError(): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  // @skjs-expect-error Variable 'x' is used before being assigned
  var x: number = x;
  return x;
}

export function writeBeforeDeclThenRead(): number {
  // @skjs-expect-error Variable 'x' is used before being assigned
  x = 1;
  var x: number;
  return x;
}

export function writeWrongTypeBeforeDecl(): void {
  // @skjs-expect-error Variable 'x' is used before being assigned
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
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 1;
  return r;
}

export function closureCapturesUninitUndefinedVar(): number | undefined {
  // @skjs-expect-error Variable 'x' is used before being assigned
  const get = (): number | undefined => x;
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number | undefined = 1;
  return get();
}

export function closureCapturesInitializedVar(): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 1;
  const get = (): number => x;
  return get();
}

// === 4. Same-scope redeclaration & TS2403 ===

export function redeclareSameAnnotatedType(): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 2;
  return x;
}

export function redeclareSameInferredType(): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 2;
  return x;
}

export function redeclareInferredThenAnnotated(): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 2;
  return x;
}

export function redeclareNoInitPreservesNarrowing(cond: boolean): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number | string = 1;
  if (cond) {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x: number | string;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

export function redeclareMismatchedAnnotatedType(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: string = "a";
}

export function redeclareMismatchedInferredType(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = "a";
}

export function redeclareUnionThenNarrow(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number | string = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 2;
}

export function redeclareNarrowThenUnion(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number | string = 2;
}

export function redeclareParamSameType(p: number): number {
  // @skjs-expect-error Cannot redeclare block-scoped variable 'p'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var p: number = 2;
  return p;
}

export function redeclareParamNoInit(p: number): number {
  // @skjs-expect-error Cannot redeclare block-scoped variable 'p'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var p: number;
  // @skjs-expect-error Variable 'p' is used before being assigned
  return p;
}

export function redeclareParamMismatchedType(p: number): void {
  // @skjs-expect-error Cannot redeclare block-scoped variable 'p'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var p: string = "a";
}

// === 5. Collisions with let / const & legal shadowing ===

export function varShadowedByInnerLet(): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 1;
  {
    let x = "hello";
    const s: string = x;
  }
  return x;
}

export function hoistedVarShadowedBySiblingConst(): number {
  {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 1;
  }
  {
    const x = "hello";
    const s: string = x;
  }
  // @skjs-expect-error Cannot find name
  return x;
}

export function letThenVarSameScopeError(): void {
  let x = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 2;
}

export function varThenLetSameScopeError(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  let x = 2;
}

export function outerLetInnerVarError(): void {
  let x = 1;
  {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var x = 2;
  }
}

export function enclosingBlockConstInnerVarError(): void {
  {
    const x = "a";
    {
      // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
      var x = 1;
    }
  }
}

// === 6. Loops & loop-closure capture soundness ===

export function loopClosureSharedVar(): Array<() => number> {
  const fns: Array<() => number> = [];
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  for (var i = 0; i < 3; i++) {
    fns.push(() => i);
  }
  return fns;
}

export function loopClosureVarNarrowedWidens(): Array<() => number> {
  const fns: Array<() => number> = [];
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  for (var i = 0; i < 3; i++) {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
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
  // @skjs-expect-error Cannot find name
  return x;
}

export function forOfVarInitializedBeforeLoop(xs: number[]): number {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x: number = 0;
  for (var x of xs) {
    const n: number = x;
  }
  return x;
}

export function forInVarUnassignedAfterLoop(o: { a: number }): string {
  for (var k in o) {
    const s: string = k;
  }
  // @skjs-expect-error Cannot find name
  return k;
}

export function forInVarInitializedBeforeLoop(o: { a: number }): string {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
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
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var { a, b } = p;
  } else {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var { a, b } = { a: 0, b: "" };
  }
  // @skjs-expect-error Cannot find name
  return a;
}

export function destructuringVarUnassignedError(
  cond: boolean,
  p: { a: number; b: string },
): number {
  if (cond) {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var { a, b } = p;
  }
  // @skjs-expect-error Cannot find name
  return a;
}

export function destructuringVarArrayHoisted(cond: boolean): number {
  if (cond) {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var [a, b]: [number, string] = [1, "x"];
  } else {
    // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
    var [a, b]: [number, string] = [2, "y"];
  }
  // @skjs-expect-error Cannot find name
  return a;
}

export function destructuringVarRedeclareMismatch(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var a: number = 1;
  // @skjs-expect-error Cannot redeclare block-scoped variable 'a'
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var { a } = { a: "bad" };
}
