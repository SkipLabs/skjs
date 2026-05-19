// Verifies that the synthetic index name used internally for object-literal
// subtyping (kSyntheticIndexName, "__SKJS_internal_index") does not leak into
// pretty-printed types shown to users.
//
// Object literals get fresh string and symbol indexes whose value types are
// TVars; this lets them be assignable to indexed targets via subtyping. The
// indexes carry an internal name that should never appear in printed output.

function emptyObject(): void {
  __SKJS_show({}, `{  }`);
}

function objectWithField(): void {
  __SKJS_show({ x: 1 }, `{ x: '0 }`);
}
