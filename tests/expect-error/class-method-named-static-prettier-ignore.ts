// prettier-ignore
// FIXME: TypeScript allows "static" as a method name but SKJS rejects it
class MyClass {
  // @skjs-expect-error 'a variable name' or 'a number' or '-' or ''' or '"' expected
  static() { return 1; } }
