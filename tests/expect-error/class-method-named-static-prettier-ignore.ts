// prettier-ignore
// FIXME: TypeScript allows "static" as a method name but SKJS rejects it
class MyClass {
  // @skjs-expect-error Expected token a variable name or a number or - or ' or "
  static() { return 1; } }
