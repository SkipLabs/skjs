// Known-unsound refinements that SKJS currently accepts.
// Each function would be soundly rejected once SKJS models the relevant
// aliasing / mutation. Today they all compile without error.

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
// `number | null`), but the getter's narrowed type is not re-widened by
// SKJS. TypeScript catches this; SKJS currently doesn't.
function testFieldReassignInBranch(x: { f: number | null }): void {
  if (x.f !== null) {
    x.f = null;
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

// FIXME: writes through an alias must invalidate an earlier source read fact.
// tsc also accepts this stale read.
function aliasBeforeNarrow(x: { f: number | null }): number {
  const y = x;
  if (x.f !== null) {
    y.f = null;
    return x.f;
  }
  return 0;
}
// FIXME: readonly prohibits writes through this view, not through other views.
// tsc also accepts this stale read.
function readonlyView(x: { f: number | null }): number {
  const y: { readonly f: number | null } = x;
  if (y.f !== null) {
    x.f = null;
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
// FIXME: destructuring writes must invalidate the same facts as plain writes.
// tsc rejects the stale return here.
function destructuredWrite(x: { f: number | null }): number {
  if (x.f !== null) {
    [x.f] = [null];
    return x.f;
  }
  return 0;
}
