// Closed<T> resolution surface: Closed is declared in the SKJS stubs
// (import-stubs/@types/skjs) as an alias of the reserved SKJS_Closed, so it
// works with no local declaration; the reserved name also works directly.
// (tsc needs a tsc-only stub `type SKJS_Closed<T> = T` to read this file.)

function testStubResolvedClosedAnnotation(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
}

function testStubResolvedClosedSecondUse(): void {
  const y: Closed<{ b: string }> = { b: "s" };
}

// The reserved name is usable directly and means the same operator.
function testDirectSkjsClosed(): void {
  const x: SKJS_Closed<{ readonly a: number }> = { a: 1 };
  // @skjs-expect-error Property 'b' does not exist on this type
  const v = x.b;
}
