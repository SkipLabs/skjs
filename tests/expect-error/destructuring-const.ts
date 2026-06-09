declare const tuple: [number, string];
// @skjs-expect-error Construction not supported: top-level const declarations cannot destructure
// @skjs-expect-error Exporting a destructuring binding is not yet supported by SKJS
const [first, second]: [number, string] = tuple;

declare const person: { name: string; age?: number };
// @skjs-expect-error Construction not supported: top-level const declarations cannot destructure
// @skjs-expect-error Exporting a destructuring binding is not yet supported by SKJS
const { name: name2, age = 42 }: { name: string; age?: number } = person;
