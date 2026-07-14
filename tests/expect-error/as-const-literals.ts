// `as const` on object and array literals (#801): an object literal becomes
// a deeply-readonly CLOSED object (never string/symbol indexes — unnamed keys
// provably absent), an array literal a readonly tuple; nested literals freeze
// recursively, literal field types stay pinned.
type Json = number | string | boolean | null | { readonly [k: string]: Json };

// The marquee goal: an as-const config is Json-assignable.
function testAsConstIntoJson(): void {
  const x = { name: "app", nested: { debug: true } } as const;
  const j: Json = x;
}

// Field types stay literal-pinned and readonly; unnamed keys provably absent.
function testAsConstObjectShape(): void {
  const x = { a: 1 } as const;
  const one: 1 = x.a;
  // Rejected: the field is readonly (and literal-pinned).
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x.a = 2;
  // Rejected: the type is closed, the key provably absent.
  // @skjs-expect-error Property 'b' does not exist on this type
  const v = x.b;
}

// A let binding: as-const is the only way to get the frozen type (no
// "unnecessary" error).
function testAsConstInLet(): void {
  let x = { a: 1 } as const;
}

// Argument position.
function takeReadonlyA(v: { readonly a: number }): void {}
function testAsConstArgument(): void {
  takeReadonlyA({ a: 1 } as const);
}

// Array literal: a readonly tuple with literal-pinned elements.
function testAsConstArray(): void {
  const t = [1, "s"] as const;
  const first: 1 = t[0];
  // Rejected: the tuple is readonly (and literal-pinned).
  // @skjs-expect-error Type is not assignable to the assignment target's type
  t[0] = 2;
}

// Spread under as-const: unsupported (the source's hidden keys are unknown,
// so the result cannot be proven closed).
function testAsConstSpread(x: { b: number }): void {
  // @skjs-expect-error Spread is not supported with 'as const': the spread source may have unknown keys, so the result cannot be proven closed
  const y = { ...x } as const;
}

// Methods under as-const: unsupported for now.
function testAsConstMethod(): void {
  // @skjs-expect-error Methods are not yet supported with 'as const'
  const y = {
    m() {},
  } as const;
}

// Primitive as-const in a const binding is genuinely redundant (const
// bindings already pin literal types): the error stays.
function testAsConstPrimitiveRedundant(): void {
  // @skjs-expect-error This 'as const' is unnecessary
  const s = "s" as const;
}
