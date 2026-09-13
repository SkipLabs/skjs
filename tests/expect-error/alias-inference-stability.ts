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
  // FIXME: This write invalidates the successful explicit-argument check.
  box.value = "changed";
  // @skjs-expect-error Type argument does not satisfy the constraint
  requireNumberField<typeof box>();
}

function compatibleWritePreservesExplicitConstraint(seed: number): void {
  const box = { value: seed };
  requireNumberField<typeof box>();
  box.value = 2;
  requireNumberField<typeof box>();
}
