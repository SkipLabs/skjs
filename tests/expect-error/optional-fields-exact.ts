// Exact optional-field semantics: `f?: T` means the key MAY BE ABSENT; if
// the key is present, its value is `T` — not `T | undefined`. To allow a
// present-but-undefined value, add undefined to the type: `f?: T | undefined`.
// This is the same contract as index signatures (present key => V) and
// matches tsc's --exactOptionalPropertyTypes (default tsc conflates absence
// with present-undefined and accepts the FIXME cases below).

// FIXME: must be rejected — the literal has `f` PRESENT with value
// undefined, violating present => number. tsc-exact rejects (TS2375).
function presentUndefinedLiteral(): void {
  const v: { f?: number } = { f: undefined };
}

// FIXME: must be rejected — `f` is always present and may hold undefined.
// tsc-exact rejects (TS2375).
function requiredUndefinedSource(x: { f: number | undefined }): { f?: number } {
  return x;
}

// FIXME: must be rejected — a present `f` may hold undefined.
// tsc-exact rejects (TS2375).
function optionalUndefinedSource(x: { f?: number | undefined }): {
  f?: number;
} {
  return x;
}

// Accepted: the target's type includes undefined explicitly.
function presentUndefinedAllowed(): void {
  const v: { f?: number | undefined } = { f: undefined };
}

// Accepted: presence implies the value is a number, so `in`-narrowing
// yields bare `number` (matches tsc-exact).
function inNarrowsToBareT(v: { f?: number }): number {
  if ("f" in v) {
    return v.f;
  }
  return 0;
}

// Reads still account for ABSENCE: without a presence check the type is
// `number | undefined`.
function readsIncludeAbsence(v: { f?: number }): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return v.f;
}

// Writing undefined into a present-`number` contract is rejected.
function writeUndefinedRejected(v: { f?: number }): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  v.f = undefined;
}

// Mutable optional fields stay invariant in the value type: a wider alias
// could write undefined that the narrow view reads as a number.
function mutableWideningRejected(x: { f?: number }): {
  f?: number | undefined;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// An index source must satisfy the bare value type: it can hold a PRESENT
// key with value undefined, which `f?: number` forbids. (tsc accepts this
// even under --exactOptionalPropertyTypes; that is unsound under the
// present => T contract, so SKJS does not follow it.)
function undefinedIndexSourceRejected(x: { [k: string]: number | undefined }): {
  f?: number;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// FIXME: must be rejected — unconditionally assigning an optional parameter
// to an optional field makes the field PRESENT with a possibly-undefined
// value (`"f" in obj` is true after an omitted argument), violating
// present => number. tsc-exact rejects the assignment (TS2412). Declare the
// field `f?: number | undefined` or assign conditionally.
class UnconditionalOptionalAssign {
  f?: number;
  constructor(f?: number) {
    this.f = f;
  }
}
