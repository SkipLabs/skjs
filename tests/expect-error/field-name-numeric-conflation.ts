// Regression tests for #750: FieldNameString must not conflate
// numerically-equal but textually-distinct field names.
//
// "01" and "1", or "0" and "-0", parse to the same integer but are distinct
// own properties at runtime (`{ "01": …, "1": … }` has two), and tsc keeps
// them distinct. Ordering such names as equal used to (a) crash the checker
// building the field map (which requires strictly-increasing keys) and
// (b) unsoundly merge their types across a spread.

// Object type with two such names: previously crashed; now accepted, and each
// name keeps its own type.
function objectTypeKeepsNamesDistinct(x: { "01": number; "1": boolean }): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const c: boolean = x["01"];
}

// Interface members exercise a separate field-map construction path.
interface NegativeZeroPair {
  "0": number;
  "-0": boolean;
}
function interfaceKeepsNamesDistinct(i: NegativeZeroPair): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const c: boolean = i["0"];
}

// A spread must not conflate "01" with "1": at runtime the merged object has
// both own properties, so o["01"] is the number 5, not y's boolean. SKJS used
// to accept this (unsound); tsc rejects with TS2322.
function spreadKeepsNamesDistinct(y: { "1": boolean }): boolean {
  const o = { "01": 5, ...y };
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const b: boolean = o["01"];
  return b;
}
