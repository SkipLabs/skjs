const x: number = 1;
// @skjs-expect-error x is already defined
const x: number = 2;

type T = number;
// @skjs-expect-error T is already defined
type T = string;

// @skjs-expect-error Found multiple definitions for class A
class A {}
// @skjs-expect-error A is already defined
// @skjs-expect-error Found multiple definitions for class A
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
