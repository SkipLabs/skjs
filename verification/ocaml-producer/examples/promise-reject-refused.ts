// `Promise.reject` makes a promise that rejects: awaiting it throws, which
// the calculus does not yet admit as an outcome, so it is not in the
// reviewed overlay.
function failed(): Promise<never> {
  return Promise.reject("boom");
}
