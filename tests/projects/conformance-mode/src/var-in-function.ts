// Conformance mode (`"conformance": true`): `var` in a function body is
// accepted and checked like `let` (block-scoped, mutable; hoisting is not
// modeled). Pinned below at the pre-feature behavior, where `var` is
// rejected with `no-var`.

function f(): void {
  // @skjs-expect-error Unexpected 'var'; use 'let' or 'const' instead
  var x = 1;
  x = 2;
}
