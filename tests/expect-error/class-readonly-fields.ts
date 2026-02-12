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
    // FIXME: SKJS should reject this (readonly field write outside constructor)
    this.x = 2;
  }
}
