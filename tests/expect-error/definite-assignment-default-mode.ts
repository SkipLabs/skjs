// Default mode: the `foo!: T` definite assignment assertion on a class field
// parses, but is rejected with a non-fatal error. Conformance mode
// (`"conformance": true`, see
// tests/projects/conformance-mode/src/definite-assignment.ts) accepts it.

class C {
  // @skjs-expect-error Definite assignment assertion ('!') on a class field is not supported by SKJS
  foo!: string;
}
