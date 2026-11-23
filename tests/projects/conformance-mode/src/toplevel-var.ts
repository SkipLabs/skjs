// Conformance mode: top-level `var`/`let` are accepted as real bindings (not
// "toplevel var is not supported") and can be assigned at the top level,
// checked against the binding's type. Reads resolve to the (widened)
// initializer type or the annotation.

var x = "";

x = "other";

let n = 1;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
var s: string = 1;

function readX(): string {
  return x;
}
