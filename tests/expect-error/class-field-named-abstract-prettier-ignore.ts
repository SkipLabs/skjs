// prettier-ignore
// FIXME: TypeScript allows "abstract" as a field name but SKJS rejects it
class MyClass {
  // @skjs-expect-error Expected token a variable name or a number or - or ' or "
  abstract: number = 1; }
