// prettier-ignore
// FIXME: Should accept method named "readonly", not treat as modifier
type Foo = {
  // @skjs-expect-error Expected token a variable name or a number or - or ' or "
  readonly (): string; };