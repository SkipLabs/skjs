// Conformance mode (`"conformance": true`): `var` in a function body is
// accepted and checked like `let` (block-scoped, mutable; hoisting is not
// modeled, SkipLabs/skjs#841).

function f(): void {
  var x = 1;
  x = 2;
}

function g(): void {
  var s = "a";
  // @skjs-expect-error Type is not assignable to the variable's type
  s = 1;
}
