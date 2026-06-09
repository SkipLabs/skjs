// Test that this cannot appear in destructuring patterns or as rest parameter

// Cannot destructure into parameter named this (array destructuring)
class MethodWithThisArrayDestructure {
  // @skjs-expect-error 'this' is not allowed in this binding position
  method([this]: [string]): void {}
}

// Cannot destructure into parameter named this (object destructuring)
class MethodWithThisObjectDestructure {
  // @skjs-expect-error 'this' is not allowed in this binding position
  method({ this }: { this: string }): void {}
}

// Cannot use this in nested destructuring patterns
class MethodWithThisNested {
  // @skjs-expect-error 'this' is not allowed in this binding position
  method({ x: [this] }: { x: [string] }): void {}
}

// Rest parameter cannot be named this
class TestSpreadParameter1 {
  // @skjs-expect-error 'this' parameters are not yet supported by SKJS
  // @skjs-expect-error A 'this' parameter cannot be a rest parameter
  method(...this: number[]): void {}
}

class TestSpreadParameter2 {
  // @skjs-expect-error 'this' is not allowed in this binding position
  // @skjs-expect-error A 'this' parameter must be the first parameter
  method(x: number, ...this: string[]): void {}
}
