// From the TypeScript test suite (tests/cases/conformance/types/never/neverInference.ts).
// @lib: es2015
// @strict: true
// @target: es2015

declare function f1<T>(x: T[]): T;

function neverInference(): void {
  const neverArray: never[] = [];
  const a1 = f1([]); // never
  const a2 = f1(neverArray); // never
}
