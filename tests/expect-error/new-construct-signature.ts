// `new` on a value whose only declaration is a `const` works when that value's
// type carries a construct signature (tsc accepts); a value without one is not
// constructable (tsc TS2351).

class C {
  a: number = 1;
}

function newClass(): C {
  return new C();
}

declare const Maker: { new (): { a: number } };

function newMaker(): { a: number } {
  return new Maker();
}

declare const Factory: { new (x: number): { a: number } };

function newFactory(): { a: number } {
  return new Factory(1);
}

declare const plain: { a: number };

function newPlain(): { a: number } {
  // @ts-expect-error This expression is not constructable
  return new plain();
}
