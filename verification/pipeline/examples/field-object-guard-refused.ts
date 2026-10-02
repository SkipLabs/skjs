// A guard finding an object where a field holds one beside `null`: what a
// field is known to hold is a union of primitives, so the test leaves the
// field at its type and the read through it is refused by that reason.
export function childB(x: { child: { b: number } | null }): number {
  if (x.child !== null) {
    return x.child.b;
  }
  return 0;
}
