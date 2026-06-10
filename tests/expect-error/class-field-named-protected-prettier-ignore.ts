// prettier-ignore
// FIXME: TypeScript allows "protected" as a field name but SKJS rejects it
class MyClass {
  // @skjs-expect-error 'a variable name' or 'a number' or '-' or ''' or '"' expected
  protected: number = 1; }
