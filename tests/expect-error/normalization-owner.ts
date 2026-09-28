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
  const item: (typeof box.value)[number] = 1;
  return item;
}
function projectedKeys(seed: { good: number }): "good" {
  const box = new OwnerBox(seed);
  const key: keyof typeof box.value = "good";
  return key;
}
function projectedElementGrowth(seed: number[]): void {
  const box = new OwnerBox(seed);
  const item: (typeof box.value)[number] = 1;
  // Projection now succeeds, so the incompatible growth rejects: the element
  // type established for the projection is the one box.set must respect.
  // @ts-expect-error Argument is not assignable to the parameter's type
  box.set(["wrong"]);
}

function compatibleProjectionGrowth(seed: number[]): void {
  const box = new OwnerBox(seed);
  const item: (typeof box.value)[number] = 1;
  box.set([item]);
}
