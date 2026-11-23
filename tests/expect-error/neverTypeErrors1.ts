// @skjs-expect-error Function 'f1' must have an explicit return type annotation
function f1() {
  let x: never;
  x = 1;
  x = "abc";
  x = false;
  x = undefined;
  x = null;
  x = {};
  x();
}

function f2(): never {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return;
}

function f3(): never {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 1;
}

function f4(): never {}

// @skjs-expect-error Function 'f5' must have an explicit return type annotation
function f5() {
  let x: never[] = []; // Ok
}

// Repro from #46032

interface A {
  foo: "a";
}

interface B {
  foo: "b";
}

type Union = A & B;

function func(): { value: Union[] } {
  return {
    value: [],
  };
}
