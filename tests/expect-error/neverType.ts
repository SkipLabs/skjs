// @strictNullChecks: true
// @declaration: true

function error(message: string): never {
  throw new Error(message);
}

function fail(): never {
  return error("Something failed");
}

function failOrThrow(shouldFail: boolean): never {
  if (shouldFail) {
    return fail();
  }
  throw new Error();
}

function infiniteLoop1(): never {
  while (true) {}
}

function infiniteLoop2(): never {
  while (true) {}
}

function move1(direction: "up" | "down"): never {
  switch (direction) {
    case "up":
      // @skjs-expect-error Type of returned value is not assignable to the function's return type
      return 1;
    case "down":
      // @skjs-expect-error Type of returned value is not assignable to the function's return type
      return -1;
  }
  return error("Should never get here");
}

function move2(direction: "up" | "down"): never {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return direction === "up"
    ? 1
    : direction === "down"
      ? -1
      : error("Should never get here");
}

// @skjs-expect-error Function 'check' must have an explicit return type annotation
function check<T>(x: T | undefined) {
  return x || error("Undefined value");
}

class C {
  // @skjs-expect-error Function 'void1' must have an explicit return type annotation
  void1() {
    throw new Error();
  }
  void2() {
    while (true) {}
  }
  never1(): never {
    throw new Error();
  }
  never2(): never {
    while (true) {}
  }
}

// @skjs-expect-error Function 'f1' must have an explicit return type annotation
function f1(x: string | number) {
  if (typeof x === "boolean") {
    x; // never
  }
}

function f2(x: string | number): never {
  while (true) {
    if (typeof x === "boolean") {
      return x; // never
    }
  }
}

// @skjs-expect-error Function 'test' must have an explicit return type annotation
function test(cb: () => string) {
  let s = cb();
  return s;
}

test(() => "hello");
test(() => fail());
test(() => {
  throw new Error();
});

// Top-level `let` is not supported by SKJS; it must be the last line.
// @skjs-expect-error The type of a top-level constant must be a primitive type, not an object
// @skjs-expect-error toplevel let is not supported by SKJS (ignored)
let errorCallback = () => error("Error callback");
