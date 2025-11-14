declare const tuple: [number, string];
// @ts-expect-error Construction not supported: top-level const declarations cannot destructure
const [first, second]: [number, string] = tuple;

declare const person: { name: string; age?: number };
// @ts-expect-error Invalid type for constant, only primitive types (not objects) are allowed
const { name: name2, age = 42 }: { name: string; age?: number } = person;
