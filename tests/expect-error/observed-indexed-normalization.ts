// Shape-sensitive alias expansion must retain the symbolic source that licensed
// an indexed-access result. Element candidates may remain symbolic: only the
// outer shape needs to be established to return the element type.
type ObservedReadonlyArray<E> = readonly E[];
type ObservedIndexed<E> = ObservedReadonlyArray<E>[number];
type ObservedNestedIndexed<E> = ObservedIndexed<ObservedReadonlyArray<E>>;

declare function observedIndexed<E>(
  xs: ObservedReadonlyArray<E>,
): ObservedIndexed<E>;

declare function observedNestedIndexed<E>(
  xs: readonly ObservedReadonlyArray<E>[],
): ObservedNestedIndexed<E>;

function observedIndexedNumber(xs: readonly number[]): number {
  return observedIndexed(xs);
}

function observedIndexedString(xs: readonly string[]): string {
  return observedIndexed(xs);
}

function observedNestedIndexedNumber(
  xs: readonly (readonly number[])[],
): readonly number[] {
  return observedNestedIndexed(xs);
}

function observedIndexedRejectsWrongResult(xs: readonly number[]): string {
  // @ts-expect-error
  return observedIndexed(xs);
}
