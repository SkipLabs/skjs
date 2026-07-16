// Boundary pins for the #765 used-before-assigned exemption (bindType,
// TypeCheckExpr.sk): a `let`/`var` with no initializer and a declared type
// that accepts `undefined` is exempt, since that's exactly what reading it
// before assignment observes at runtime. These pin that the exemption is
// scoped precisely to that condition, not wider.

// A declared type that does NOT accept `undefined` must still be flagged --
// this is the actual TS2454 case, unaffected by the #765 exemption.
export function nonUndefinedTypeStillFlagged(cond: boolean): number {
  let x: number;
  if (cond) x = 1;
  // @skjs-expect-error Variable 'x' is used before being assigned
  return x;
}

// `T | null` (no `undefined`) must NOT be exempted: an uninitialized let
// reads as `undefined` at runtime, never `null`, so this is still a genuine
// used-before-assigned case even though the declared type is nullable.
export function nullOnlyTypeStillFlagged(cond: boolean): number | null {
  let x: number | null;
  if (cond) x = 1;
  // @skjs-expect-error Variable 'x' is used before being assigned
  return x;
}

// The exemption only changes whether the read is flagged, not the type it
// reports: a read before any assignment is still T | undefined, not
// narrowed to T, so assigning it to a non-undefined-accepting binding is
// still an error.
export function exemptedReadStaysWidelyTyped(cond: boolean): number {
  let x: number | undefined;
  if (cond) {
    x = 1;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: number = x;
  return y;
}
