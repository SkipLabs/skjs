// Test: Generic class constraints with type variable expansion.
// Exercises intersection type creation when type variables may expand to bottom.

class Box<T> {
  value: T;
  constructor(v: T) {
    this.value = v;
  }
  get(): T {
    return this.value;
  }
  set(x: T): void {
    this.value = x;
  }
}

function takeBox<T extends Box<string>>(b: T): void {}

function test(): void {
  const box: Box<"foo"> = new Box("foo");
  // @skjs-expect-error Invalid call
  takeBox(box);
}
