// `T[number]` also reaches named fields whose name a number key can produce
// (e.g. `{0: string}[number]`), and falls back to the string index when
// there is no number index (JS coerces a number key to a string for
// property lookup).

type NumericNamedFields = { 0: string; 1: boolean };
type NumericNamedFieldsElem = NumericNamedFields[number];

type StringIndexOnly = { [key: string]: number };
type StringIndexOnlyElem = StringIndexOnly[number];
