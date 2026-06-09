declare const tuple: [number, string];
// @skjs-expect-error Exporting a destructuring binding is not yet supported by SKJS
// @skjs-expect-error Top-level const declarations cannot use destructuring in SKJS
const [first, second]: [number, string] = tuple;

declare const person: { name: string; age?: number };
// @skjs-expect-error Exporting a destructuring binding is not yet supported by SKJS
// @skjs-expect-error Top-level const declarations cannot use destructuring in SKJS
const { name: name2, age = 42 }: { name: string; age?: number } = person;
