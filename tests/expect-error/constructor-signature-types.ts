// Test cases for constructor signature types (`new`) support

class A<T> {
  constructor(value: T) {}
}

class B<T, U> {
  constructor(first: T, second: U) {}
}

class C {
  constructor(name: string) {}
}

class D {
  constructor() {}
}

class E {
  constructor(value: number) {}
  static staticMethod(): void {}
}

class F {
  constructor(x: number) {}
}

function testConstructorSignatureTypes(): void {
  // Should allow assigning class to constructor signature type
  const x: new <T>(value: T) => A<T> = A;

  // Generic class with multiple type parameters
  const y: new <T, U>(first: T, second: U) => B<T, U> = B;

  // Non-generic class
  const z: new (name: string) => C = C;

  // Class with no constructor parameters
  const w: new () => D = D;

  // Class with static methods should still work
  const e: new (value: number) => E = E;

  // Test accessing constructor from static class object
  const FStatic = F;
  const constructorFromStatic: new (x: number) => F = FStatic;
}

function testConstructorSignatureErrors(): void {
  // @skjs-expect-error Invalid annotation
  const badParams: new (num: number) => C = C;
}

type newInObjectType = { new (): D };

function useNewInObjectType(c: newInObjectType): D {
  return new c();
}
