// `T[number]` should also reach named fields whose name a number key can
// produce (e.g. `{0: string}[number]`), and fall back to the string index
// when there is no number index (JS coerces a number key to a string for
// property lookup). Neither case is supported yet.

type NumericNamedFields = { 0: string; 1: boolean };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type NumericNamedFieldsElem = NumericNamedFields[number];

type StringIndexOnly = { [key: string]: number };
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type StringIndexOnlyElem = StringIndexOnly[number];
