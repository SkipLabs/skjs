// Test that this cannot appear in destructuring patterns or as rest parameter

// Cannot destructure into parameter named this (array destructuring)
class MethodWithThisArrayDestructure {
  // @skjs-expect-error this forbidden here
  method([this]: [string]): void {}
}

// Cannot destructure into parameter named this (object destructuring)
class MethodWithThisObjectDestructure {
  // @skjs-expect-error this forbidden here
  method({ this }: { this: string }): void {}
}

// Cannot use this in nested destructuring patterns
class MethodWithThisNested {
  // @skjs-expect-error this forbidden here
  method({ x: [this] }: { x: [string] }): void {}
}

// Rest parameter cannot be named this
class TestSpreadParameter1 {
  // @skjs-expect-error TODO: support this parameter
  // @skjs-expect-error this cannot be a rest parameter
  method(...this: number[]): void {}
}

class TestSpreadParameter2 {
  // @skjs-expect-error Parameter named this must be the first one
  // @skjs-expect-error this forbidden here
  method(x: number, ...this: string[]): void {}
}
