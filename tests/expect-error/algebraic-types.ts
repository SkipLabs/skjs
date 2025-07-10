class C1 {
  // @ts-expect-error Forbidden field name 'kind' in a class
  kind: string;
}

class C2 {
  // @ts-expect-error Forbidden method name 'kind'
  kind(): void;
}

// @ts-expect-error Algebraic field kind was expected to be a constant string
function nonConstantStringKindType(): { kind: string } {
  return { kind: "a" };
}

function nonStringKind(): void {
  // @ts-expect-error Algebraic field kind was expected to be a constant string
  const obj = { kind: 42 };
}

// @ts-expect-error Field kind cannot be optional
function optionalKind(): { kind?: "a" } {
  return { kind: "a" };
}

// @ts-expect-error Duplicate field kind
function duplicateFieldKind(): { kind: "a"; kind: "b" } {
  return { kind: "a" };
}
