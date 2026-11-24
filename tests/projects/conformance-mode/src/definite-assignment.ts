// Conformance mode (`"conformance": true`): the `foo!: T` definite assignment
// assertion on a class field is accepted and the field counts as definitely
// assigned — no "has no initializer" error, matching tsc.
class C {
  foo!: string;
  bar: number = 1;
}

function f(): void {
  const c = new C();
  const s: string = c.foo;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const t: string = c.bar;
}
