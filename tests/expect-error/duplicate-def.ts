// Same-space duplicates (should error)

const x: number = 1;
const x: number = 2;

type T = number;
type T = string;

// @skjs-expect-error Found multiple definitions for class A
class A {}
// @skjs-expect-error Found multiple definitions for class A
class A {}

function f(): void {}
function f(): void {}

// @skjs-expect-error Found multiple definitions for class I
interface I {
  a: number;
}
// @skjs-expect-error Found multiple definitions for class I
interface I {
  b: string;
}

// @skjs-expect-error Construction not supported: enum (ignored)
enum E {
  X,
}
// @skjs-expect-error Construction not supported: enum (ignored)
enum E {
  Y,
}

function g(): void {}
const g: number = 1;

type U = number;
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
class Ct {}

function Cf(): void {}
class Cf {}

type Et = number;
// @skjs-expect-error Construction not supported: enum (ignored)
enum Et {
  X,
}

function Ef(): void {}
// @skjs-expect-error Construction not supported: enum (ignored)
enum Ef {
  X,
}

const Ec: number = 1;
// @skjs-expect-error Construction not supported: enum (ignored)
enum Ec {
  X,
}
