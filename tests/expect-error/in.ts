function literalInRecordAlwaysTrue(x: { f: number }): boolean {
  // @skjs-expect-error This condition is always true
  return "f" in x;
}

function refineLiteralInRecordAlwaysTrue(x: { f: number }): number {
  // @skjs-expect-error This condition is always true
  if ("f" in x) {
    return x.f;
  } else {
    return 0;
  }
}

function literalInRecordOpt(x: { f?: number }): boolean {
  return "f" in x;
}

function refineLiteralInRecordOpt(x: { f?: number }): number {
  if ("f" in x) {
    return x.f;
  } else {
    return 0;
  }
}

function refineLiteralInRecordOpt2(x: { f?: number }): number | undefined {
  if ("f" in x) {
    return x.f;
  } else {
    return 0;
  }
}

function literalInRecordNotAlwaysFalse(x: { f: number }): boolean {
  return "g" in x;
}

function refineLiteralInRecordNotAlwaysFalse(x: { f: number }): number {
  if ("g" in x) {
    // @skjs-expect-error Property 'g' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x.g;
  } else {
    return 0;
  }
}

function refineLiteralInRecordNotAlwaysFalse2(x: { f: number }): unknown {
  if ("g" in x) {
    // @skjs-expect-error Property 'g' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)
    return x.g;
  } else {
    return 0;
  }
}

function literalInRecordIndex(x: { [f: string]: number }): boolean {
  return "a" in x;
}

function refineLiteralInRecordIndex(x: { [f: string]: number }): number {
  if ("a" in x) {
    return x.a;
  } else {
    return 0;
  }
}

function literalInRecordUnion(x: { f: number } | { g: number }): boolean {
  return "f" in x;
}

function refineLiteralInRecordUnion(x: { f: number } | { g: number }): number {
  if ("f" in x) {
    // FIXME: TS narrows the union; SKJS can't soundly filter under structural typing
    // @skjs-expect-error Property 'f' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x.f;
  } else {
    return 0;
  }
}

function refineLiteralInRecordUnion2(
  x: { f: number } | { g: number },
): unknown {
  if ("f" in x) {
    // FIXME: TS narrows the union; SKJS can't soundly filter under structural typing
    // @skjs-expect-error Property 'f' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)
    return x.f;
  } else {
    return 0;
  }
}

function literalInRecordOptUnion(x: { f?: number } | { g: number }): boolean {
  return "f" in x;
}

function refineLiteralInRecordOptUnion(
  x: { f?: number } | { g: number },
): number {
  if ("f" in x) {
    // FIXME: TS narrows the union; SKJS can't soundly filter under structural typing
    // @skjs-expect-error Property 'f' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x.f;
  } else {
    return 0;
  }
}

function refineLiteralInRecordOptUnion2(
  x: { f?: number } | { g: number },
): number | undefined {
  if ("f" in x) {
    // FIXME: TS narrows the union; SKJS can't soundly filter under structural typing
    // @skjs-expect-error Property 'f' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x.f;
  } else {
    return 0;
  }
}

function unionInRecord(s: "f" | "g", x: { f: number }): boolean {
  return s in x;
}

function refineUnionInRecord(s: "f" | "g", x: { f: number }): number {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Property 'g' does not exist on this type
    return x[s];
  } else {
    return 0;
  }
}

function refineUnionInRecord2(s: "f" | "g", x: { f: number }): unknown {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Property 'g' does not exist on this type
    return x[s];
  } else {
    return 0;
  }
}

function unionInRecordOpt(s: "f" | "g", x: { f?: number }): boolean {
  return s in x;
}

function refineUnionInRecordOpt(s: "f" | "g", x: { f?: number }): number {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Property 'g' does not exist on this type
    return x[s];
  } else {
    return 0;
  }
}

function refineUnionInRecordOpt2(
  s: "f" | "g",
  x: { f?: number },
): number | undefined {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Property 'g' does not exist on this type
    return x[s];
  } else {
    return 0;
  }
}

function refineUnionInRecordOpt3(s: "f" | "g", x: { f?: number }): unknown {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Property 'g' does not exist on this type
    return x[s];
  } else {
    return 0;
  }
}

function unionInRecordAlwaysTrue(
  s: "f" | "g",
  x: { f: number; g: number },
): boolean {
  // @skjs-expect-error This condition is always true
  return s in x;
}

function refineUnionInRecordAlwaysTrue(
  s: "f" | "g",
  x: { f: number; g: number },
): number {
  // @skjs-expect-error This condition is always true
  if (s in x) {
    return x[s];
  } else {
    return 0;
  }
}

function unionInRecordOpt2(
  s: "f" | "g",
  x: { f?: number; g: number },
): boolean {
  return s in x;
}

function refineUnionInRecordOpt2_1(
  s: "f" | "g",
  x: { f?: number; g: number },
): number {
  if (s in x) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x[s];
  } else {
    return 0;
  }
}
function refineUnionInRecordOpt2_2(
  s: "f" | "g",
  x: { f?: number; g: number },
): number | undefined {
  if (s in x) {
    return x[s];
  } else {
    return 0;
  }
}

function unionInRecordOpt3(
  s: "f" | "g",
  x: { f?: number; g?: number },
): boolean {
  return s in x;
}

function refineUnionInRecordOpt3_1(
  s: "f" | "g",
  x: { f?: number; g?: number },
): number {
  if (s in x) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x[s];
  } else {
    return 0;
  }
}

function refineUnionInRecordOpt3_2(
  s: "f" | "g",
  x: { f?: number; g?: number },
): number | undefined {
  if (s in x) {
    return x[s];
  } else {
    return 0;
  }
}

function unionInRecordNotAlwaysFalse(s: "f" | "g", x: { h: number }): boolean {
  return s in x;
}

function refineUnionInRecordNotAlwaysFalse(
  s: "f" | "g",
  x: { h: number },
): number {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Property 'f | g' does not exist on this type
    return x[s];
  } else {
    return 0;
  }
}

function refineUnionInRecordNotAlwaysFalse2(
  s: "f" | "g",
  x: { h: number },
): unknown {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Property 'f | g' does not exist on this type
    return x[s];
  } else {
    return 0;
  }
}

function stringInRecord(s: string, x: { f: number }): boolean {
  return s in x;
}

function refineStringInRecord(s: string, x: { f: number }): number {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Cannot index this type with a non-literal key: it has no index signature
    return x[s];
  } else {
    return 0;
  }
}

function refineStringInRecord2(s: string, x: { f: number }): unknown {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Cannot index this type with a non-literal key: it has no index signature
    return x[s];
  } else {
    return 0;
  }
}

function literalInTupleAlwaysFalse(): boolean {
  return 0 in [];
}

function literalInTupleAlwaysTrue(): boolean {
  return 0 in [1];
}

function literalInTupleUnion(x: [number] | [number, number]): boolean {
  return 1 in x;
}

function literalInNonObject(x: number): boolean {
  // @skjs-expect-error The right-hand side of an 'in' expression must be an object
  return 0 in x;
}

function refineInMandatoryField(x: { f: string } | string): string {
  // @skjs-expect-error The right-hand side of an 'in' expression must be an object
  if ("f" in x) {
    return x.f;
  } else {
    return x;
  }
}

// A phantom field synthesized by `in` is invisible to subtyping toward
// the original type — a refined Foo is still assignable to Foo.
class FooWithPrivate {
  private p: number = 1;
}

function takesFoo(_: FooWithPrivate): void {}

function refinedClassStillAssignableToOriginal(obj: FooWithPrivate): void {
  if ("y" in obj) {
    takesFoo(obj);
  }
}

// A phantom field cannot satisfy a real declared field on the super.
function takesXY(_: { x: number; y: number }): void {}

function phantomDoesNotSatisfyRealField(obj: { x: number }): void {
  if ("y" in obj) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    takesXY(obj);
  }
}
