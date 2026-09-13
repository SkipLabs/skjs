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
