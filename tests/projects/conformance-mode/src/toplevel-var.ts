// Conformance mode: top-level `var`/`let` are accepted as real bindings (not
// "toplevel var is not supported") and can be assigned at the top level.
// Pinned below at the pre-feature behavior.

// @skjs-expect-error toplevel var is not supported by SKJS (ignored)
// @skjs-expect-error Only 'const' members are supported in this position by SKJS
var x = '';

// @skjs-expect-error Cannot find name 'x'
x = 'other';

// @skjs-expect-error toplevel let is not supported by SKJS (ignored)
let n = 1;

// @skjs-expect-error toplevel var is not supported by SKJS (ignored)
// @ts-expect-error Type of initializer is not assignable to the declared type annotation
var s: string = 1;

function readX(): string {
  return x;
}
