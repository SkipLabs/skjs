// Regression tests for #750: FieldNameString must not conflate
// numerically-equal but textually-distinct field names.
//
// "01" and "1" parse to the same integer but are distinct own properties at
// runtime (`{ "01": …, "1": … }` has two), and tsc keeps them distinct.

// A spread must not conflate "01" with "1": at runtime the merged object has
// both own properties, so o["01"] is the number 5, not y's boolean. tsc
// rejects with TS2322.
// FIXME(#750): SKJS currently accepts this unsoundly — the two names collide
// in the field map, so o["01"] resolves to y's boolean.
function spreadKeepsNamesDistinct(y: { "1": boolean }): boolean {
  const o = { "01": 5, ...y };
  const b: boolean = o["01"];
  return b;
}
