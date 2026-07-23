// Soundness pins for the #765 used-before-assigned exemption (bindType,
// TypeCheckExpr.sk): mbouaziz's review on #908 asked whether
// isSub(undefined, ty) could trivially succeed when `ty` is a type
// variable -- growTVars widening it to admit undefined regardless of what
// it actually denotes, rather than genuinely checking membership -- and
// self-resolved that a written annotation's `ty` can't be one. Tried to
// construct that case; it doesn't materialize. These pin the two closest
// candidates.

// A generic function's own type parameter, referenced as the annotation, is
// a rigid (skolem) type variable, not a growable one -- it must still be
// flagged, both unconstrained and with a constraint that excludes undefined.
function unconstrainedTypeParamStillFlagged<T>(): T {
  let x: T;
  // @skjs-expect-error Variable 'x' is used before being assigned
  return x;
}

function constrainedTypeParamStillFlagged<T extends string>(): T {
  let y: T;
  // @skjs-expect-error Variable 'y' is used before being assigned
  return y;
}

// `typeof` on a fully unconstrained generic call's result *is* exempted --
// but because skjs defaults an uninferable type parameter to `unknown`
// (matching tsc), and `unknown` genuinely does accept `undefined`, not
// because of a trivially-growable TVar. The exemption is correct here, and
// downstream misuse is still caught by the usual type checks.
declare function make<T>(): T;

function typeofUnconstrainedCallExempted(): void {
  let a = make();
  let x: typeof a;
  return x; // no used-before-assigned error -- typeof a is unknown, which admits undefined
}

function typeofUnconstrainedCallStillCaughtDownstream(): number {
  let a = make();
  let x: typeof a;
  // @skjs-expect-error Operator '+' cannot be applied to these types
  return x + 1;
}
