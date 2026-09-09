/**
 * Producer precision gap: a body that completes returns undefined, which is
 * what this declares, and TypeScript accepts it. SKJS rejects it with "Not all
 * code paths return a value, and the return type does not include 'undefined'"
 * -- of a return type that is undefined. The verifier states the obligation the
 * annotation makes and discharges it: the exit carries undefined, and undefined
 * establishes undefined. Compare skjs-unsound/never-completes.ts, the same
 * check skipped rather than too strict.
 */
function completes(): undefined {}
