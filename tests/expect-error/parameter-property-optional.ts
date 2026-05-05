// TS accepts optional parameter properties and creates an optional field
// (`public x?: string`). SKJS does not desugar them — the desugaring in
// ParserDefs.sk requires `optional => None()` — so the modifier survives
// to the parameter modifier check.
class OptionalParameterProperty {
  // @skjs-expect-error Forbidden modifier 'public' for a function parameter
  constructor(public x?: string) {}
}
