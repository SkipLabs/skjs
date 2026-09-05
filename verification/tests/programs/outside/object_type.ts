// Outside the fragment: the gate must reject an object type.
function field(o: { a: string }): string {
  return o.a;
}
