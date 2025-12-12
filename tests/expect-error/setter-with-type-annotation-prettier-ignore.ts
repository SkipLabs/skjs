// prettier-ignore
// Regression test: Setters must be function definitions, not normal fields with type annotations
class SetterTypeAnnotation {
  // @ts-expect-error Expected accessor definition
  set bar: string; }