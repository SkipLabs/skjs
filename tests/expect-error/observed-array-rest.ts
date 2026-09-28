// Array-rest projection shares the committed-read boundary with exact tuples.
// These are intended native regression expectations; run them before changing
// the annotations. In particular, symbolic elements must remain inferable.

declare function observedNumbers(...args: number[]): void;
declare function observedFirst<T>(...args: readonly T[]): T;
type ObservedArrayArgs<T> = readonly T[];
declare function observedArrayAlias<T>(...args: ObservedArrayArgs<T>): void;
declare function observedArrayFactory<T extends readonly unknown[]>(
  seed: T,
): (...args: T) => void;

function observedEmptyArrayRest(): void {
  observedNumbers();
}

function observedArraySpread(values: number[]): void {
  observedNumbers(...values);
}

function observedArrayElementInference(seed: number): number {
  return observedFirst(seed, seed);
}

function observedRigidArrayElement<T>(values: readonly T[]): void {
  observedArrayAlias<T>(...values);
}

function observedInferredOuterArray(values: readonly number[]): void {
  const call = observedArrayFactory(values);
  call(1, 2, 3);
  call();
}

function observedWrongArrayElement(): void {
  // @ts-expect-error Argument is not assignable to the parameter's type
  observedNumbers("wrong");
}

function observedWrongAliasedArrayElement(): void {
  // @ts-expect-error Argument is not assignable to the parameter's type
  observedArrayAlias<number>("wrong");
}

function observedWrongInferredOuterArray(values: readonly number[]): void {
  const call = observedArrayFactory(values);
  // @ts-expect-error Argument is not assignable to the parameter's type
  call("wrong");
}
