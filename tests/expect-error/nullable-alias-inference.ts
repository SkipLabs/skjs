// Type alias inference for nullable types. `Maybe<A>` (alias of `A | null`)
// should infer identically to inline `A | null` in every position.

type Maybe<T> = T | null;

declare function unwrapInline<A>(value: A | null): A;
declare function unwrapAlias<A>(value: Maybe<A>): A;

declare const sn: string | null;

// Simple case: alias in direct parameter position.
function testDirectParam(): string {
  const ok = unwrapInline(sn);
  // @skjs-expect-error Invalid call
  const viaAlias = unwrapAlias(sn);
  return ok + viaAlias;
}

declare function inferFromValueInline<A>(value: { f(input: A | null): A }): A;
declare function inferFromValueAlias<A>(value: { f(input: Maybe<A>): A }): A;

function f(input: string | null): string {
  return input ?? "";
}

// Nested case: alias in contravariant position inside object type.
function testNestedParam(): string {
  const ok = inferFromValueInline({ f });
  // @skjs-expect-error Invalid call
  const viaAlias = inferFromValueAlias({ f });
  return ok + viaAlias;
}

// Alias on the *argument* side, in direct parameter position.
declare const sm: Maybe<string>;

function testDirectArg(): string {
  return unwrapInline(sm);
}

// Alias on the argument side, nested inside a function-field
// contravariant slot.
declare const objWithAlias: { f(input: Maybe<string>): string };

function testNestedArg(): string {
  return inferFromValueInline(objWithAlias);
}

// Constructor-signature descent: A inside a `new (): ...` return type
// should infer identically whether the shape uses an alias or inline
// union, on either side.
declare function unboxCtorInline<A>(ctor: { new (): A | null }): A;
declare function unboxCtorAlias<A>(ctor: { new (): Maybe<A> }): A;

declare const CtorSN: { new (): string | null };
declare const CtorM: { new (): Maybe<string> };

function testConstructor(): string {
  const ok = unboxCtorInline(CtorSN);
  // @skjs-expect-error Invalid call
  const viaAliasParam = unboxCtorAlias(CtorSN);
  const viaAliasArg = unboxCtorInline(CtorM);
  return ok + viaAliasParam + viaAliasArg;
}
