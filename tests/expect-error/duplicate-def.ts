// Same-space duplicates (should error)

const x: number = 1;
// @skjs-expect-error x is already defined
const x: number = 2;

type T = number;
// @skjs-expect-error T is already defined
type T = string;

// @skjs-expect-error Found multiple definitions for class A
class A {}
// @skjs-expect-error Found multiple definitions for class A
// @skjs-expect-error A is already defined
class A {}

function f(): void {}
// @skjs-expect-error f is already defined
function f(): void {}

// @skjs-expect-error Found multiple definitions for class I
interface I {
  a: number;
}
// @skjs-expect-error Found multiple definitions for class I
// @skjs-expect-error I is already defined
interface I {
  b: string;
}

// @skjs-expect-error Construction not supported: enum (ignored)
enum E {
  X,
}
// @skjs-expect-error Construction not supported: enum (ignored)
// @skjs-expect-error E is already defined
enum E {
  Y,
}

function g(): void {}
// @skjs-expect-error g is already defined
const g: number = 1;

type U = number;
// @skjs-expect-error U is already defined
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
// @skjs-expect-error Ct is already defined
class Ct {}

function Cf(): void {}
// @skjs-expect-error Cf is already defined
class Cf {}

type Et = number;
// @skjs-expect-error Construction not supported: enum (ignored)
// @skjs-expect-error Et is already defined
enum Et {
  X,
}

function Ef(): void {}
// @skjs-expect-error Construction not supported: enum (ignored)
// @skjs-expect-error Ef is already defined
enum Ef {
  X,
}

const Ec: number = 1;
// @skjs-expect-error Construction not supported: enum (ignored)
// @skjs-expect-error Ec is already defined
enum Ec {
  X,
}
