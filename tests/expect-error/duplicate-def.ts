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

// @skjs-expect-error Duplicate class declaration 'I'
interface I {
  a: number;
}
// @skjs-expect-error Duplicate class declaration 'I'
// @skjs-expect-error Duplicate identifier 'I'
interface I {
  b: string;
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
