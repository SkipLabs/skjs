// Tests for the Promise value surface: the constructor and the static
// methods resolve/reject/all.

function testConstructor(): Promise<number> {
  return new Promise<number>(
    (resolve: (value: number) => void, reject: (reason: unknown) => void) => {
      resolve(0);
    },
  );
}

// Error: the executor argument is required.
function testConstructorNoArgs(): Promise<number> {
  // @ts-expect-error Too few arguments for this call
  return new Promise<number>();
}

function testResolve(): Promise<number> {
  return Promise.resolve(42);
}

function testResolveMismatch(): Promise<string> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return Promise.resolve(42);
}

function testReject(): Promise<never> {
  return Promise.reject("boom");
}

function testAll(ps: Array<Promise<number>>): Promise<Array<number>> {
  return Promise.all(ps);
}
