// Bounds refer to this instantiation's parameters, including when an
// instanceof check reveals only their hidden identities.
// @skjs-expect-error Cannot find type 'T'
class DependentBox<T, U extends T> {
  first: T;
  second: U;
  constructor(first: T, second: U) {
    this.first = first;
    this.second = second;
  }
}

function sameWitness(x: unknown): void {
  if (x instanceof DependentBox) x.first = x.second;
}

function reverseBound(x: unknown): void {
  if (x instanceof DependentBox) x.second = x.first;
}

function crossWitness(x: unknown, y: unknown): void {
  if (x instanceof DependentBox && y instanceof DependentBox) {
    x.first = y.second;
  }
}

function inferredBound(n: number): number {
  const box = new DependentBox(n, n);
  return box.second;
}

function incompatibleBound(n: number): void {
  const box = new DependentBox(n, "wrong");
}
