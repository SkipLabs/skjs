// Regression test for #683: a union whose members are split across the pretty-
// printer's clause group (e.g. `undefined`) and its named-instance group (e.g.
// `Array<number>`) must keep the " | " separator between the two groups.
// Before the fix the named instance ran straight onto the previous member, so
// `Array<number> | undefined` printed as `undefinedArray<number>`.
//
// Note: skjs normalizes union order — clause members are printed before named
// instances — so the union shows as `undefined | Array<number>`. That ordering
// is intentional and independent of the missing-separator bug pinned here.

function clauseThenNamedInst(x: Array<number> | undefined): void {
  __SKJS_show(x, "undefined | Array<number>");
}

// A union with no named instance was always separated correctly; it guards the
// fix against introducing a spurious leading separator on the clause-only path.
function clausesOnly(x: number | undefined): void {
  __SKJS_show(x, "number | undefined");
}
