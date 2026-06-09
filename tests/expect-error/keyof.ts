// Test keyof functionality

interface Person {
  name: string;
  age: number;
  email: string;
}

// Basic keyof usage
type PersonKeys = keyof Person;

// Valid assignments
const validKey1: PersonKeys = "name";
const validKey2: PersonKeys = "age";
const validKey3: PersonKeys = "email";

// Invalid assignment should produce error
// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const invalidKey: PersonKeys = "invalid";

// keyof with empty object
type EmptyKeys = keyof {};

// keyof with object type literal
type ObjKeys = keyof { x: number; y: string };
const objKey: ObjKeys = "x";

const koKind: keyof { kind: "a" } = "kind";

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const invalidObjKey: ObjKeys = "z";

const koTup0: keyof [number] = 0;
// Tuples (via the TupleN stubs) inherit `[n: number]: T` from ReadonlyArray,
// so `keyof` includes all numeric keys, not only positional literals.
const koTup1: keyof [number] = 1;
const koTup0s: keyof [number] = "0";
// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const koTup1s: keyof [number] = "1";

const koIdx: keyof { [x: number]: string } = 42;
// TODO: convert numbers to strings
// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const koIdxs: keyof { [x: number]: string } = "42";

const koStrIdx: keyof "a" = 99;
const koStrFld: keyof string = "charAt";
// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const koStrInvalid: keyof string = "notAFieldOfString";
