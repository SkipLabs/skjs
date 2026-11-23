// A `never`-annotated function whose body can complete normally should be
// rejected (tsc TS2355): falling off the end would return `undefined` at
// runtime while every use of the call is typed `never`, which is unsound.
// No diagnostics are expected yet: the error annotations are added by the
// commit that introduces the TS2355 check.

// @ts-expect-error A function returning 'never' cannot have a reachable end point
function neverFallsThrough(b: boolean): never {
  if (b) {
    throw new Error("boom");
  }
}

// @ts-expect-error A function returning 'never' cannot have a reachable end point
function neverEmptyBody(): never {}

type NeverAlias = never;

// An alias to `never` is rejected the same way.
// @ts-expect-error A function returning 'never' cannot have a reachable end point
function neverAliasFallsThrough(): NeverAlias {}

// Positive: every path throws, so the body never completes normally.
function neverAlwaysThrows(b: boolean): never {
  if (b) {
    throw new Error("boom");
  }
  throw new Error("bam");
}

// Positive: returning a `never`-typed value is a valid never exit.
function neverReturnsNever(): never {
  return neverAlwaysThrows(true);
}

// Positive: an infinite loop never completes normally.
function neverInfiniteLoop(): never {
  while (true) {}
}
