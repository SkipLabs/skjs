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
// @ts-expect-error
const invalidKey: PersonKeys = "invalid";

// keyof with empty object
type EmptyKeys = keyof {};

// keyof with object type literal
type ObjKeys = keyof { x: number; y: string };
const objKey: ObjKeys = "x";

// @ts-expect-error
const invalidObjKey: ObjKeys = "z";

const koTup0: keyof [number] = 0;
// @ts-expect-error Invalid definition
const koTup1: keyof [number] = 1;
const koTup0s: keyof [number] = "0";
// @ts-expect-error Invalid definition
const koTup1s: keyof [number] = "1";

const koIdx: keyof { [x: number]: string } = 42;
// TODO: convert numbers to strings
// @ts-expect-error Invalid definition
const koIdxs: keyof { [x: number]: string } = "42";

const koStrIdx: keyof "a" = 99;
const koStrFld: keyof string = "charAt";
// @ts-expect-error Invalid definition
const koStrInvalid: keyof string = "notAFieldOfString";

