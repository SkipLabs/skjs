// Same-space duplicates (should error)

const x: number = 1;
// @skjs-expect-error Duplicate identifier 'x'
const x: number = 2;

type T = number;
// @skjs-expect-error Duplicate identifier 'T'
type T = string;

// @skjs-expect-error Duplicate class declaration 'A'
class A {}
// @skjs-expect-error Duplicate class declaration 'A'
// @skjs-expect-error Duplicate identifier 'A'
class A {}

function f(): void {}
// @skjs-expect-error Duplicate identifier 'f'
function f(): void {}

// Interfaces with the same name do NOT collide: they merge their members,
// like tsc — see interface-declaration-merging.ts.
interface I {
  a: number;
}
interface I {
  b: string;
}

// interface + class: tsc merges the two as well, but SKJS does not support
// class/interface merging yet, so the collision is still reported.
// @skjs-expect-error Duplicate class declaration 'Ic2'
interface Ic2 {
  a: number;
}
// @skjs-expect-error Duplicate class declaration 'Ic2'
// @skjs-expect-error Duplicate identifier 'Ic2'
class Ic2 {
  b: number = 1;
}

enum E {
  X,
}
// @skjs-expect-error Duplicate identifier 'E'
enum E {
  Y,
}

function g(): void {}
// @skjs-expect-error Duplicate identifier 'g'
const g: number = 1;

type U = number;
// @skjs-expect-error Duplicate identifier 'U'
interface U {
  a: number;
}

// Cross-space definitions (should NOT error)

type Tf = number;
function Tf(): void {}

type Tc = number;
const Tc: number = 1;

interface If {
  a: number;
}
function If(): void {}

// interface + const: different spaces
interface Ic {
  a: number;
}
const Ic: number = 1;

// Cross-space with class/enum (should error, they occupy both spaces)

type Ct = number;
// @skjs-expect-error Duplicate identifier 'Ct'
class Ct {}

function Cf(): void {}
// @skjs-expect-error Duplicate identifier 'Cf'
class Cf {}

type Et = number;
// @skjs-expect-error Duplicate identifier 'Et'
enum Et {
  X,
}

function Ef(): void {}
// @skjs-expect-error Duplicate identifier 'Ef'
enum Ef {
  X,
}

const Ec: number = 1;
// @skjs-expect-error Duplicate identifier 'Ec'
enum Ec {
  X,
}

// A declaration colliding with a lib/stub type is a duplicate identifier too
// (tsc TS2300, issue #887): the stub's definition is what resolves, so the
// collision is reported at the declaration — the use below still fails
// downstream because the stub's alias is what `NonNullable` denotes.
// @skjs-expect-error Duplicate identifier 'NonNullable'
interface NonNullable<T> {
  v: T;
}
function stubCollision(a: NonNullable<number>): number {
  // @skjs-expect-error Property 'v' does not exist on this type
  return a.v;
}
