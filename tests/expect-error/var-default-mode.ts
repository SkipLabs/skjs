// Default mode: `var` in function bodies is supported (function-scoped and
// hoisted, SkipLabs/skjs#841); top-level `var` and `let` remain rejected in
// default mode and are accepted in conformance mode (`"conformance": true`,
// see tests/projects/conformance-mode/ and skjs-rules.md "Conformance mode").

function f(): void {
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
