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
    // @skjs-expect-error Invalid assignment
    this.x = 2;
  }
}
