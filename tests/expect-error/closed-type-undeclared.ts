// Closed<T> used without any LOCAL declaration: the identity alias shipped in
// the SKJS stubs (import-stubs/@types/skjs) resolves it, so the operator works
// out of the box. (tsc also accepts when configured to see the same stubs; a
// local `type Closed<T> = T` as in closed-type.ts works too.)

function testUndeclaredClosedAnnotation(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
}

function testUndeclaredClosedSecondUse(): void {
  const y: Closed<{ b: string }> = { b: "s" };
}
