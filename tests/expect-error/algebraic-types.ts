// kind is now a normal field, so these are all valid
class C1 {
  kind: string = "a";
}

class C2 {
  kind(): void {}
}

function constStringKindType(): { kind: "a" } {
  return { kind: "a" };
}

function nonConstantStringKindType(): { kind: string } {
  return { kind: "a" };
}

function nonStringKind(): void {
  const obj = { kind: 42 };
}

function optionalKind(): { kind?: "a" } {
  return { kind: "a" };
}

function duplicateFieldKind(): { kind: "a"; kind: "b" } {
  // @skjs-expect-error Invalid return type
  return { kind: "a" };
}
