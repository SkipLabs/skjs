// Interface heritage over a type-alias base, two levels deep (#798).
// tsc accepts this; the constructor-lookup walk must skip alias bases (they
// cannot contribute a constructor) instead of resolving them as classes.
type PlainA = { a: number };

interface I extends PlainA {
  b: string;
}

interface J extends I {
  c: boolean;
}

function testTwoLevelAliasHeritage(x: J): number {
  return x.a;
}
