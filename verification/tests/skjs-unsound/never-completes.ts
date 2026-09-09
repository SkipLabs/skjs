/**
 * Unsoundness witness: SKJS accepts a function declared `never` whose body
 * completes, so a caller may use the result at any type while it returns
 * undefined. The check that would catch this exists and is general, and is
 * skipped exactly when the result type is `never` -- taking the annotation as
 * the reason the end is unreachable, which is what it asserts. TypeScript
 * rejects it. The verifier states the obligation the producer skips:
 * completing produces undefined, which must establish the declared result.
 */
function nope(): never {}
