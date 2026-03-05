// FIXME: TypeScript accepts both calls, but SKJS rejects only the alias form.
// `A | null` works while `Maybe<A>` (alias of `A | null`) fails.

type Maybe<T> = T | null;

declare function inferFromValueInline<A>(value: { f(input: A | null): A }): A;
declare function inferFromValueAlias<A>(value: { f(input: Maybe<A>): A }): A;

function f(input: string | null): string {
  return input ?? "";
}

function testNullableAliasInferenceWithoutClassOrInterface(): string {
  const ok = inferFromValueInline({ f });
  // @skjs-expect-error Invalid call
  const bug = inferFromValueAlias({ f });

  return ok + bug;
}
