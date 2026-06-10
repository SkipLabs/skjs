// prettier-ignore
// Regression test: Setters must be function definitions, not normal fields with type annotations
class SetterTypeAnnotation {
  // @skjs-expect-error Expected a getter or setter definition
  set bar: string; }