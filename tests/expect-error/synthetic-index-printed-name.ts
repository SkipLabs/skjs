// Verifies that the synthetic index name used internally for object-literal
// subtyping (kSyntheticIndexName, "__SKJS_internal_index") does not leak into
// pretty-printed types shown to users.
//
// Object literals get fresh string and symbol indexes whose value types are
// TVars; this lets them be assignable to indexed targets via subtyping. The
// indexes carry an internal name that should never appear in printed output.

function emptyObject(): void {
  // FIXME: synthetic index name leaks via the pretty-printer; will be hidden
  // in a follow-up commit.
  __SKJS_show(
    {},
    `{
  [ __SKJS_internal_index: string ]: '0 (set: '1),
  [ __SKJS_internal_index: symbol ]: '2 (set: '3)
}
`,
  );
}

function objectWithField(): void {
  // FIXME: same leak; the synthetic index renders alongside named field 'x'.
  __SKJS_show(
    { x: 1 },
    `{
  x: '0,
  [ __SKJS_internal_index: string ]: '2 (set: '3),
  [ __SKJS_internal_index: symbol ]: '4 (set: '5)
}
`,
  );
}
