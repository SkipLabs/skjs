// An object rest copies every remaining own enumerable key of its source,
// which a record contract does not bound; an object's keys are fixed where it
// is allocated, so a copy of the named fields would not be the rest.
export function objectRest(x: { a: string; b: number }): { b: number } {
  const { a, ...rest } = x;
  return rest;
}
