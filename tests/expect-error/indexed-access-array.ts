// Indexed access on a concrete array type with a number key should yield the
// element type (e.g. `string[][number]` = `string[]`, `string[number]` = `string`).
//
// Currently rejected; will be supported once TAGet handles the T[number] case.

type StringArray = string[];
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type StringElem = StringArray[number];
