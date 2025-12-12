// prettier-ignore
// FIXME: TypeScript allows "protected" as a method name but SKJS rejects it
class MyClass {
  // @skjs-expect-error Expected token a variable name or a number or - or ' or "
  protected() { return 1; } }
