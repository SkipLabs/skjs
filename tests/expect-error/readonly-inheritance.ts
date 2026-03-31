// Class and interface inheritance with readonly fields.
// SKJS is stricter than TypeScript: it rejects readonly-to-mutable
// subtyping via the contravariant set check (set=bottom <: set=T fails).

// ============================================================
// 1. Class: subclass makes field readonly
// ============================================================

class BaseClass {
  value: number = 1;
}

// SKJS rejects: readonly field not compatible with mutable parent
// @skjs-expect-error Invalid extension
class DerivedReadonly extends BaseClass {
  readonly value: number = 2;
}

// ============================================================
// 2. Interface: readonly extends mutable
// ============================================================

interface MutableIface {
  name: string;
}

// SKJS rejects: readonly field not compatible with mutable parent
// @skjs-expect-error Invalid extension
interface ReadonlyIface extends MutableIface {
  readonly name: string;
}

// ============================================================
// 3. Interface: mutable extends readonly (allowed)
// ============================================================

interface ReadonlyBase {
  readonly label: string;
}

// Mutable extends readonly: allowed (mutable is a subtype of readonly)
interface MutableDerived extends ReadonlyBase {
  label: string;
}
