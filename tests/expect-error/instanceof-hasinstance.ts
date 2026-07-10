// A class that declares a custom `static [Symbol.hasInstance]` decouples
// `x instanceof C` from the nominal class: the method decides membership and
// may return true for values that are not instances (or false for values that
// are). Narrowing `x` to `C` in the then-branch is therefore unsound, so SKJS
// suppresses `instanceof` narrowing for such classes. tsc narrows here anyway
// (TypeScript is unsound in this case too — see issue #776).
//
// Narrowing still applies to ordinary classes and to an instance-level
// `[Symbol.hasInstance]`, which does not affect the `instanceof` operator.

class WithHasInstance {
  a: number = 1;
  static [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}

function customHasInstance(x: unknown): number {
  if (x instanceof WithHasInstance) {
    // @skjs-expect-error Cannot access a property on type 'unknown'
    return x.a;
  }
  return 0;
}

// The symmetric case: a custom `[Symbol.hasInstance]` can return `false` for a
// real instance, so a `HasInstanceFalse` value can reach the `else` branch at
// runtime. SKJS never narrows the `instanceof` else-branch (for any class), so
// `x` keeps type `HasInstanceFalse` there and `x.a` is sound. tsc unsoundly
// narrows the else-branch to `never` and rejects `x.a`, so SKJS is soundly more
// permissive here (issue #776).
class HasInstanceFalse {
  a: number = 1;
  static [Symbol.hasInstance](_x: unknown): boolean {
    return false;
  }
}

function hasInstanceFalseElse(x: HasInstanceFalse): number {
  if (x instanceof HasInstanceFalse) {
    return x.a;
  }
  return x.a;
}

// A custom `static [Symbol.hasInstance]` inherited from a base class is used by
// `instanceof` on the subclass too, so narrowing is suppressed there as well.
class BaseHasInstance {
  static [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}
class DerivedHasInstance extends BaseHasInstance {
  b: number = 2;
}

function inheritedHasInstance(x: unknown): number {
  if (x instanceof DerivedHasInstance) {
    // @skjs-expect-error Cannot access a property on type 'unknown'
    return x.b;
  }
  return 0;
}

// An instance-level `[Symbol.hasInstance]` lives on the prototype, not on the
// constructor, so it does not affect `instanceof`; narrowing still applies.
class InstanceHasInstance {
  a: number = 1;
  [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}

function instanceLevelHasInstance(x: unknown): number {
  if (x instanceof InstanceHasInstance) {
    return x.a;
  }
  return 0;
}

// A plain class (default `instanceof`) narrows normally.
class Plain {
  a: number = 1;
}

function plainClass(x: unknown): number {
  if (x instanceof Plain) {
    return x.a;
  }
  return 0;
}
