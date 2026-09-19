// Source-function rest elements are checked contravariantly. The outer array
// projection is observed; this does not turn readonly arrays into writable ones.
function observedRestContravariance(
  f: (...args: readonly (number | string)[]) => number,
): (...args: readonly number[]) => number {
  return f;
}

function observedRestContravarianceRejects(
  f: (...args: readonly number[]) => number,
): (...args: readonly (number | string)[]) => number {
  // @ts-expect-error
  return f;
}

// The target-side array element is consumed after positional/optional checks.
// Keep that order: those checks can determine shared element candidates.
function observedOptionalSourceForArrayRest(
  f: (first?: number) => number,
): (...args: readonly number[]) => number {
  return f;
}

function observedOptionalSourceRejectsArrayElement(
  f: (first?: number) => number,
): (...args: readonly string[]) => number {
  // @ts-expect-error
  return f;
}

// A required prefix and a homogeneous tail exercise both positional checking
// and the two observed array projections within one function comparison.
function observedPrefixedArrayRest(
  f: (head: boolean, ...args: readonly (number | string)[]) => number,
): (head: boolean, ...args: readonly number[]) => number {
  return f;
}

type ObservedRestAlias<E> = readonly E[];

function observedRigidAliasRest<T>(
  f: (...args: ObservedRestAlias<T>) => T,
): (...args: readonly T[]) => T {
  return f;
}

function observedRigidRestArgumentsStayDistinct<T, U>(
  f: (...args: ObservedRestAlias<T>) => void,
): (...args: ObservedRestAlias<U>) => void {
  // @ts-expect-error
  return f;
}

// Inference of E must remain possible after the outer layout is established.
// This is a positive precision control, not permission to solve E in scratch.
declare function inferObservedRestElement<E>(
  callback: (seed: E, ...args: readonly E[]) => E,
): E;

function observedPositionalRestInference(
  callback: (seed: number, ...args: readonly number[]) => number,
): number {
  return inferObservedRestElement(callback);
}

// A tuple layout is still flattened; it is not approximated by an array whose
// element is the union of all tuple positions.
type ObservedSubtypePair<A, B> = readonly [A, B];

function observedAliasedTupleLayout(
  f: (...args: ObservedSubtypePair<number, string>) => string,
): (a: number, b: string) => string {
  return f;
}

function observedTuplePositionsRemainDistinct(
  f: (...args: ObservedSubtypePair<number, string>) => void,
): (...args: readonly [number, number]) => void {
  // @ts-expect-error
  return f;
}
