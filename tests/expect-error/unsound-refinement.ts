// Known-unsound refinements that SKJS currently accepts.
// Each function would be soundly rejected once SKJS models the relevant
// aliasing / mutation. Today they all compile without error.

declare function sideEffect(): void;

// 1. Field refined, then a side-effecting call happens between the test
// and the use. In a multithreaded context (or via a synchronous setter
// called inside `sideEffect`), `x.f` could have been reassigned.
function testFieldRefineThenSideEffect(x: { f: number | null }): void {
  if (x.f !== null) {
    sideEffect();
    const n: number = x.f;
  }
}

// 2. Field is reassigned to a wider value inside the refined branch. The
// setter typechecks (the field still accepts `number | null`), but the
// getter's narrowed type is not re-widened by SKJS. TypeScript catches
// this; SKJS currently doesn't.
function testFieldReassignInBranch(x: { f: number | null }): void {
  if (x.f !== null) {
    x.f = null;
    const n: number = x.f;
  }
}

// 3. Local is captured by a lambda that reassigns it. The lambda is
// invoked inside the refined branch, so the narrowed type is stale when
// we use `x` afterwards.
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
