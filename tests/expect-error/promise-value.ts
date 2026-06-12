// Tests for the Promise value surface: the constructor and the static
// methods resolve/reject/all.

// FIXME: tsc exposes the global Promise constructor value; SKJS does not yet.
function testConstructor(): Promise<number> {
  // @skjs-expect-error This constructor expects no arguments
  return new Promise<number>(
    (resolve: (value: number) => void, reject: (reason: unknown) => void) => {
      resolve(0);
    },
  );
}

// FIXME: tsc requires the executor argument (TS2554); SKJS synthesizes a
// no-argument constructor for every interface.
function testConstructorNoArgs(): Promise<number> {
  return new Promise<number>();
}

// FIXME: tsc exposes Promise.resolve/reject/all; SKJS does not yet.
function testResolve(): Promise<number> {
  // @skjs-expect-error Property 'resolve' does not exist on this type
  return Promise.resolve(42);
}

function testResolveMismatch(): Promise<string> {
  // @ts-expect-error Property 'resolve' does not exist on this type
  return Promise.resolve(42);
}

function testReject(): Promise<never> {
  // @skjs-expect-error Property 'reject' does not exist on this type
  return Promise.reject("boom");
}

function testAll(ps: Array<Promise<number>>): Promise<Array<number>> {
  // @skjs-expect-error Property 'all' does not exist on this type
  return Promise.all(ps);
}
