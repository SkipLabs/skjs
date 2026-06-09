class WithReadonlyField {
  readonly x: number;
  constructor() {
    this.x = 1;
  }
}

class WithReadonlyOutsideConstructor {
  readonly x: number;
  constructor() {
    this.x = 1;
  }
  mutate(): void {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    this.x = 2;
  }
}
