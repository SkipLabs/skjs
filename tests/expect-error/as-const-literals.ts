// `as const` on object and array literals (#801): deeply-readonly Closed
// types. BASELINE: pinned to current behavior — object/array literals under
// `as const` are rejected with TS1355 (and, in a const binding, an
// "unnecessary" error first); the feature commits flip these.
type Json = number | string | boolean | null | { readonly [k: string]: Json };

// The marquee goal: an as-const config is Json-assignable.
function testAsConstIntoJson(): void {
  // TODO(#801): accepted once as-const literals are closed.
  // @skjs-expect-error This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const x = { name: "app", nested: { debug: true } } as const;
  const j: Json = x;
}

// Field types stay literal-pinned and readonly; unnamed keys provably absent.
function testAsConstObjectShape(): void {
  // @skjs-expect-error This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const x = { a: 1 } as const;
  const one: 1 = x.a;
  // Already rejected today (const-pinned literal field type); stays rejected
  // once fields are readonly.
  // @skjs-expect-error Type is not assignable to the assignment target's type
  x.a = 2;
  // Already rejected today; stays rejected once the type is closed.
  // @skjs-expect-error Property 'b' does not exist on this type
  const v = x.b;
}

// A let binding: as-const is the only way to get the frozen type (no
// "unnecessary" error).
function testAsConstInLet(): void {
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  let x = { a: 1 } as const;
}

// Argument position.
function takeReadonlyA(v: { readonly a: number }): void {}
function testAsConstArgument(): void {
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  takeReadonlyA({ a: 1 } as const);
}

// Array literal: a readonly tuple with literal-pinned elements.
function testAsConstArray(): void {
  // @skjs-expect-error This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const t = [1, "s"] as const;
  const first: 1 = t[0];
  // Already rejected today (literal element type); stays rejected once the
  // tuple is readonly.
  // @skjs-expect-error Type is not assignable to the assignment target's type
  t[0] = 2;
}

// Spread under as-const: unsupported (the source's hidden keys are unknown,
// so the result cannot be proven closed).
function testAsConstSpread(x: { b: number }): void {
  // @skjs-expect-error This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const y = { ...x } as const;
}

// Methods under as-const: unsupported for now.
function testAsConstMethod(): void {
  // @skjs-expect-error This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const y = {
    // @skjs-expect-error Function 'm' must have an explicit return type annotation
    m() {},
  } as const;
}

// Primitive as-const in a const binding is genuinely redundant (const
// bindings already pin literal types): the error stays.
function testAsConstPrimitiveRedundant(): void {
  // @skjs-expect-error This 'as const' is unnecessary
  const s = "s" as const;
}
