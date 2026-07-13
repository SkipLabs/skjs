// Interface heritage over a type-alias base, two levels deep (#798).
// tsc accepts this; the constructor-lookup walk must skip alias bases (they
// cannot contribute a constructor) instead of resolving them as classes.
type PlainA = { a: number };

// TODO(#798): spurious fatal "Cannot find name 'PlainA'" — J's constructor
// lookup recurses into I's alias base and resolves it as a class. The error
// anchors here, at the alias reference in I's extends clause.
// @skjs-expect-error Cannot find name 'PlainA'
interface I extends PlainA {
  b: string;
}

interface J extends I {
  c: boolean;
}

function testTwoLevelAliasHeritage(x: J): number {
  return x.a;
}
