// Normalization must read and establish shape in the owning substitution.
class OwnerBox<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
  set(value: T): void {
    this.value = value;
  }
}
function projectedElement(seed: number[]): number {
  const box = new OwnerBox(seed);
  // @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
  const item: (typeof box.value)[number] = 1;
  return item;
}
function projectedKeys(seed: { good: number }): "good" {
  const box = new OwnerBox(seed);
  const key: keyof typeof box.value = "good";
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return key;
}
function projectedElementGrowth(seed: number[]): void {
  const box = new OwnerBox(seed);
  // @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
  const item: (typeof box.value)[number] = 1;
  // TODO: Once projection succeeds, the incompatible growth must reject.
  box.set(["wrong"]);
}

function compatibleProjectionGrowth(seed: number[]): void {
  const box = new OwnerBox(seed);
  // @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
  const item: (typeof box.value)[number] = 1;
  box.set([item]);
}
