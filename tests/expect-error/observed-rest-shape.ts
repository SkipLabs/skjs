// Native integration controls for observed rest-shape resolution.
// Added for the uncompiled handoff: run through SKJS and verify diagnostics.
// The direct Subst state tests are in tests/TypeReadObservation.sk.

declare function observedPair(...args: [number, string]): string;
declare function observedSingle<T>(...args: [T]): T;
declare function observedArray(...args: number[]): void;

type ObservedPairAlias<A, B> = [A, B];

declare function observedAliasPair<A, B>(...args: ObservedPairAlias<A, B>): B;

function observedPairPositive(): string {
  return observedPair(1, "ok");
}

function observedAliasWithSymbolicElements<A, B>(a: A, b: B): B {
  return observedAliasPair<A, B>(a, b);
}

function observedArrayFallbackPositive(): void {
  observedArray(1, 2, 3);
}

function observedElementInferencePositive(seed: number): number {
  return observedSingle(seed);
}

function observedPairMissingArgument(): string {
  // @ts-expect-error Too many arguments for this call
  return observedPair(1);
}

function observedPairWrongElement(): string {
  // @ts-expect-error Argument is not assignable to the parameter's type
  return observedPair(1, 2);
}

declare function takesPair(f: (...a: readonly [number, string]) => void): void;
declare function makeSymbolicRest<T extends readonly unknown[]>(): (
  ...a: T
) => void;

// The rest shape cannot be established here without solving T, so the read is
// blocked rather than unavailable. Falling back to an array rest would forget
// the exact arity, so the call is refused instead.
function observedBlockedRestShape(): void {
  // @skjs-expect-error A fixed rest-parameter shape could not be established without changing inference; add an explicit tuple or rest-parameter type annotation
  takesPair(makeSymbolicRest());
}
