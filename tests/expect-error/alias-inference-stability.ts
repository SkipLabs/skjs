class InferenceBox<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
  get(): T {
    return this.value;
  }
  set(value: T): void {
    this.value = value;
  }
}

function inferenceBox<T>(value: T): InferenceBox<T> {
  return new InferenceBox(value);
}

function laterGrowthMustPreserveAlias(value: number): number {
  const box = inferenceBox(value);
  const alias: InferenceBox<number> = box;
  // Accepting the alias seals the candidate it reads as number.
  // @ts-expect-error Argument is not assignable to the parameter's type
  box.set("changed");
  return alias.get();
}

function compatibleWritePreservesAlias(value: number): number {
  const box = inferenceBox(value);
  const alias: InferenceBox<number> = box;
  box.set(2);
  return alias.get();
}

// No value argument or result use can independently establish this bound.
declare function requireNumberField<
  T extends { readonly value: number },
>(): void;

function explicitConstraintMustRemainValid(seed: number): void {
  const box = { value: seed };
  requireNumberField<typeof box>();
  // @ts-expect-error Type is not assignable to the field's type
  box.value = "changed";
  requireNumberField<typeof box>();
}

function compatibleWritePreservesExplicitConstraint(seed: number): void {
  const box = { value: seed };
  requireNumberField<typeof box>();
  box.value = 2;
  requireNumberField<typeof box>();
}

// The alias erases T, so expanding its body cannot enforce T's bound.
type NumberMarker<T extends { readonly value: number }> = null;
// No constructor call can independently enforce this class's type arguments.
class NumberMarkerClass<T extends { readonly value: number }> {}

function aliasConstraintMustRemainValid(seed: number): void {
  const box = { value: seed };
  const first: NumberMarker<typeof box> = null;
  // @ts-expect-error Type is not assignable to the field's type
  box.value = "changed";
  const second: NumberMarker<typeof box> = null;
}

function classConstraintWithoutConstructor(seed: number): void {
  const box = { value: seed };
  const first = new NumberMarkerClass<typeof box>();
  // @ts-expect-error Type is not assignable to the field's type
  box.value = "changed";
  const second = new NumberMarkerClass<typeof box>();
}

function compatibleAliasAndClassConstraints(seed: number): void {
  const box = { value: seed };
  const marker: NumberMarker<typeof box> = null;
  const instance = new NumberMarkerClass<typeof box>();
  box.value = 2;
  const repeated: NumberMarker<typeof box> = null;
  const another = new NumberMarkerClass<typeof box>();
}

// A sealed argument is a validation target, even when the new source is an
// uncommitted array literal. Proposing growth of a sealed candidate does nothing.
function arrayLiteralAfterSealedArgument(seed: number[]): number {
  const box = inferenceBox(seed);
  const established: number[] = box.value;
  // @ts-expect-error Argument is not assignable to the parameter's type
  box.set(["changed"]);
  return box.value[0] ?? 0;
}

function compatibleArrayLiteralAfterSealedArgument(seed: number[]): number {
  const box = inferenceBox(seed);
  const established: number[] = box.value;
  box.set([2]);
  return box.value[0] ?? 0;
}
