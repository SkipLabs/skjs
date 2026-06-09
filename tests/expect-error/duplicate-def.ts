// Same-space duplicates (should error)

const x: number = 1;
// @skjs-expect-error x is already defined
const x: number = 2;

type T = number;
// @skjs-expect-error T is already defined
type T = string;

// @skjs-expect-error Duplicate class declaration 'A'
class A {}
// @skjs-expect-error A is already defined
// @skjs-expect-error Duplicate class declaration 'A'
class A {}

function f(): void {}
// @skjs-expect-error f is already defined
function f(): void {}

// @skjs-expect-error Duplicate class declaration 'I'
interface I {
  a: number;
}
// @skjs-expect-error I is already defined
// @skjs-expect-error Duplicate class declaration 'I'
interface I {
  b: string;
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum E {
  X,
}
// @skjs-expect-error E is already defined
// @skjs-expect-error enum is not supported by SKJS (ignored)
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
// @skjs-expect-error Et is already defined
// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Et {
  X,
}

function Ef(): void {}
// @skjs-expect-error Ef is already defined
// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Ef {
  X,
}

const Ec: number = 1;
// @skjs-expect-error Ec is already defined
// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Ec {
  X,
}
