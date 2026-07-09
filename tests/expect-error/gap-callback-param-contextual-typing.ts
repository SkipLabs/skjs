// Contextual typing of un-annotated callback parameters against a non-generic
// callee's expected parameter type (#763). The comparator params `x`/`y` are
// typed `number` from `Array<number>.sort`'s signature — no annotation needed,
// matching tsc. The body is still checked against the contextual type, so a
// misuse (e.g. `x.length`) is reported.
export function contextualSortParams(a: number[]): number[] {
  return a.slice().sort((x, y) => x - y);
}

// forEach / filter (also non-generic) likewise type their callback params.
export function contextualForEach(a: string[]): void {
  a.forEach((s, i) => {
    const _s: string = s;
    const _i: number = i;
  });
}

// A user-declared callback parameter is contextually typed too.
declare function withCallback(cb: (n: number) => number): void;
export function contextualUserCallback(): void {
  withCallback((n) => n + 1);
}
