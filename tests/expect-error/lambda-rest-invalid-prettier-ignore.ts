// prettier-ignore
// Rest parameters with optional, default, or not-last in arrow functions

function testArrowRestOptional(): void {
  // @skjs-expect-error A rest parameter cannot be optional
  const f = (...rest?: number[]): void => { void rest; };
  void f;
}

function testArrowRestDefault(): void {
  // @skjs-expect-error A rest parameter cannot have an initializer
  const f = (...rest: number[] = []): void => { void rest; };
  void f;
}

function testArrowRestNotLast(): void {
  // @skjs-expect-error A rest parameter must be last in a parameter list
  const f = (...rest: number[], x: number): void => { void rest; void x; };
  void f;
}
