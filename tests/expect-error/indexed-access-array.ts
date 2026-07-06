// Indexed access on a concrete array type with a number key should yield the
// element type (e.g. `string[][number]` = `string[]`, `string[number]` = `string`).

type StringArray = string[];
type StringElem = StringArray[number];
