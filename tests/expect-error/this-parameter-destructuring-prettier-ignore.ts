// Test that this cannot appear in destructuring patterns

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
