/**
 * Unsoundness witness, and the smallest one in this corpus: SKJS accepts a
 * function whose declared result is `never` and whose body completes. `never`
 * is a claim that the function does not return, so the caller may use the
 * result at any type; `go` returns undefined against a `boolean` annotation.
 *
 * SKJS does check that the end of a body is unreachable, and that check is
 * general: an empty body is rejected against `boolean`, against `null`, and
 * against `never | boolean`, with "Not all code paths return a value". Its
 * reachability analysis is real too, so `while (true) {}` is accepted against
 * any result. Every explicit return is checked as well, including `return;`
 * and `return undefined;`, which produce exactly the value an implicit
 * completion produces.
 *
 * The check is skipped only when the resolved result type is `never`. It
 * survives an alias and holds for non-empty and branching bodies, so it keys on
 * the type rather than on the shape of the body. That makes it a circularity
 * rather than an omission: the declared `never` is taken as the reason the end
 * is unreachable, which is what the annotation asserts and what needed proving.
 * TypeScript rejects the declaration outright: "A function returning 'never'
 * cannot have a reachable end point."
 *
 * An intersection of arrows with disjoint domains reaches the same bug without
 * naming `never`: SKJS computes `((x: true) => null) & ((x: false) => null)` as
 * `never`, so a function declared to return it may also complete. That type is
 * inhabited — `(x: boolean) => null` is a member — so the collapse is wrong on
 * its own terms. See ../../SUBTYPING.md.
 *
 * The source fragment gates the `never` keyword, so nothing here reaches a
 * proof obligation. This is a producer counterexample, not a repair exercise.
 */
function nope(): never {}

function go(): boolean {
  const b: boolean = nope();
  return b;
}
