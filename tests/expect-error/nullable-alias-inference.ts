type Maybe<T> = T | null;

// Simple case: alias in direct parameter position
declare function unwrapInline<A>(value: A | null): A;
declare function unwrapAlias<A>(value: Maybe<A>): A;

declare const sn: string | null;

function testDirectParam(): string {
  const ok = unwrapInline(sn);
  const viaAlias = unwrapAlias(sn);
  return ok + viaAlias;
}

// Nested case: alias in contravariant position inside object type
declare function inferFromValueInline<A>(value: { f(input: A | null): A }): A;
declare function inferFromValueAlias<A>(value: { f(input: Maybe<A>): A }): A;

function f(input: string | null): string {
  return input ?? "";
}

function testNestedParam(): string {
  const ok = inferFromValueInline({ f });
  const viaAlias = inferFromValueAlias({ f });
  return ok + viaAlias;
}
