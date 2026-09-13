// Mutation refinement regressions. Visible property writes invalidate known
// object refinements; effects hidden behind calls remain open.

declare function sideEffect(): void;

// 1. #597 — Field refined, then a side-effecting call happens between
// the test and the use. In a multithreaded context (or via a synchronous
// setter called inside `sideEffect`), `x.f` could have been reassigned.
function testFieldRefineThenSideEffect(x: { f: number | null }): void {
  if (x.f !== null) {
    sideEffect();
    const n: number = x.f;
  }
}

// 2. #598 — Field is reassigned to a wider value inside the refined
// branch. The setter typechecks (the field still accepts
// `number | null`), so the getter must lose its earlier narrowing.
function testFieldReassignInBranch(x: { f: number | null }): void {
  if (x.f !== null) {
    x.f = null;
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const n: number = x.f;
  }
}

// 3. #599 — Local is captured by a lambda that reassigns it. The lambda
// is invoked inside the refined branch, so the narrowed type is stale
// when we use `x` afterwards.
function testLocalCapturedAndMutated(): void {
  let x: string | null = "hello";
  if (x !== null) {
    const reset = () => {
      x = null;
    };
    reset();
    const s: string = x;
  }
}

// Writes through an alias invalidate the source read fact; tsc accepts it.
function aliasBeforeNarrow(x: { f: number | null }): number {
  const y = x;
  if (x.f !== null) {
    y.f = null;
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x.f;
  }
  return 0;
}
// Readonly prohibits writes through this view, not other views; tsc accepts it.
function readonlyView(x: { f: number | null }): number {
  const y: { readonly f: number | null } = x;
  if (y.f !== null) {
    x.f = null;
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return y.f;
  }
  return 0;
}
// Property writes preserve scalar snapshots and non-null reference facts;
// checking the field after the write establishes a fresh read fact.
function checkedAfterWrite(
  x: { f: number | null } | null,
  seed: number | null,
): number {
  if (x !== null && seed !== null) {
    const y = x;
    y.f = null;
    if (x.f !== null) return x.f;
    return seed;
  }
  return 0;
}
// Destructuring invalidates the same facts as plain writes.
function destructuredWrite(x: { f: number | null }): number {
  if (x.f !== null) {
    [x.f] = [null];
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return x.f;
  }
  return 0;
}

// A field check cannot establish a lasting alias contract while the original
// view can still write null.
function annotatedNarrowAlias(x: { f: number | null }): number {
  if (x.f !== null) {
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const y: { f: number } = x;
    x.f = null;
    return y.f;
  }
  return 0;
}

// Readonly restricts writes through y, not writes through x.
function annotatedReadonlyAlias(x: { f: number | null }): number {
  if (x.f !== null) {
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const y: { readonly f: number } = x;
    x.f = null;
    return y.f;
  }
  return 0;
}

// Stable contents and reference narrowing suffice for a lasting alias;
// the field value copied into a scalar also retains its current refinement.
function stableAnnotatedAlias(x: { f: number } | null): number {
  if (x !== null) {
    const y: { readonly f: number } = x;
    if (x.f === 1) {
      const snapshot: 1 = x.f;
      x.f = 2;
      return snapshot;
    }
    return y.f;
  }
  return 0;
}
