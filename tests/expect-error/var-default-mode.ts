// Default mode: `var` is rejected everywhere — in function bodies with the
// `no-var` lint error, and at the top level as not supported. Conformance
// mode (`"conformance": true`, see tests/projects/conformance-mode/) relaxes
// this; see skjs-rules.md "Conformance mode".

function f(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 1;
  x = 2;
}

// @skjs-expect-error toplevel var is not supported by SKJS (ignored)
// @skjs-expect-error Only 'const' members are supported in this position by SKJS
var topVar = 1;

// @skjs-expect-error toplevel let is not supported by SKJS (ignored)
let topLet = 2;

function g(): number {
  return topVar;
}
