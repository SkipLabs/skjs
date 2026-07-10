// Closed<T> used WITHOUT the tsc-compat identity alias: the builtin works with
// no declaration at all. (tsc rejects this whole file with TS2304 "Cannot find
// name 'Closed'" — this is the SKJS-only surface; declare `type Closed<T> = T`
// for tsc compatibility, as closed-type.ts does.)

function testUndeclaredClosedAnnotation(): void {
  const x: Closed<{ readonly a: number }> = { a: 1 };
}

function testUndeclaredClosedSecondUse(): void {
  const y: Closed<{ b: string }> = { b: "s" };
}
