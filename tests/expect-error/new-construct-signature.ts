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
  // FIXME: tsc accepts (Maker's type has a construct signature); SKJS resolves
  // `new` in type space and cannot find the value-only binding (issue #698)
  // @skjs-expect-error Cannot find type 'Maker'
  return new Maker();
}

declare const Factory: { new (x: number): { a: number } };

function newFactory(): { a: number } {
  // FIXME: tsc accepts (Factory's type has a construct signature); SKJS resolves
  // `new` in type space and cannot find the value-only binding (issue #698)
  // @skjs-expect-error Cannot find type 'Factory'
  return new Factory(1);
}

declare const plain: { a: number };

function newPlain(): { a: number } {
  // FIXME: tsc rejects with TS2351 "has no construct signatures"; SKJS resolves
  // `new` in type space and cannot find the value-only binding (issue #698)
  // @skjs-expect-error Cannot find type 'plain'
  return new plain();
}
