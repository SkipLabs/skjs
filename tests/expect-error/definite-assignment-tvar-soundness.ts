// An initialization exemption must check whether an annotation admits
// undefined, without solving its inference variables to make that true.
// Written annotations can contain growable variables through typeof.

function typeofInferredFieldNeedsAssignment(seed: number): number {
  const box = { value: seed };
  let result: typeof box.value;
  // @ts-expect-error Variable 'result' is used before being assigned
  return result;
}

function typeofInferredFieldAfterAssignment(seed: number): number {
  const box = { value: seed };
  let result: typeof box.value;
  result = seed;
  return result;
}

function typeofUndefinedFieldAdmitsInitialValue(
  seed: number | undefined,
): number | undefined {
  const box = { value: seed };
  let result: typeof box.value;
  return result;
}

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
  // No used-before-assigned error: unknown admits undefined, but is not void.
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function typeofUnconstrainedCallStillCaughtDownstream(): number {
  let a = make();
  let x: typeof a;
  // @skjs-expect-error Operator '+' cannot be applied to these types
  return x + 1;
}
