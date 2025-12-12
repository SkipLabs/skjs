// prettier-ignore
// FIXME: TypeScript allows "static" as a field name but SKJS rejects it
class MyClass {
  // @skjs-expect-error Expected token a variable name or a number or - or ' or "
  static: number = 1; }
