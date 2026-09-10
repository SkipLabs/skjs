/**
 * Unsoundness witness: the same collapse taken as an assumption. SKJS types the
 * parameter as `never`, so anything follows from it: assigning it to an arrow
 * returning boolean is accepted without a diagnostic, where TypeScript rejects
 * the assignment. `useBoth((x) => null)` returns null against the declared
 * boolean result. The verifier assumes the parameter at its annotation, the
 * two-signature arrow, and refuses the producer's claim that it is empty: the
 * claim differs from the annotation, before any obligation is tried. The
 * inhabitant SKJS turns away is in skjs-incomplete/arrow-intersection.ts.
 */
function useBoth(a: ((x: true) => null) & ((x: false) => null)): boolean {
  const b: (x: boolean) => boolean = a;
  return b(true);
}
