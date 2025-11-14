function literalInRecordAlwaysTrue(x: { f: number }): boolean {
  // @skjs-expect-error This expression is always true
  return "f" in x;
}

function refineLiteralInRecordAlwaysTrue(x: { f: number }): number {
  // @skjs-expect-error This expression is always true
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
    // @ts-expect-error Invalid return type
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
    // @ts-expect-error Invalid return type
    return x.g;
  } else {
    return 0;
  }
}

function refineLiteralInRecordNotAlwaysFalse2(x: { f: number }): unknown {
  if ("g" in x) {
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
    // FIXME
    // @skjs-expect-error Invalid return type
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
    // @skjs-expect-error Invalid return type
    return x.f;
  } else {
    return 0;
  }
}

function refineLiteralInRecordUnion2(
  x: { f: number } | { g: number },
): unknown {
  if ("f" in x) {
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
    // @ts-expect-error Invalid return type
    return x.f;
  } else {
    return 0;
  }
}

function refineLiteralInRecordOptUnion2(
  x: { f?: number } | { g: number },
): number | undefined {
  if ("f" in x) {
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
    // @skjs-expect-error Unbound field: g
    return x[s];
  } else {
    return 0;
  }
}

function refineUnionInRecord2(s: "f" | "g", x: { f: number }): unknown {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Unbound field: g
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
    // @skjs-expect-error Unbound field: g
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
    // @skjs-expect-error Unbound field: g
    return x[s];
  } else {
    return 0;
  }
}

function refineUnionInRecordOpt3(s: "f" | "g", x: { f?: number }): unknown {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Unbound field: g
    return x[s];
  } else {
    return 0;
  }
}

function unionInRecordAlwaysTrue(
  s: "f" | "g",
  x: { f: number; g: number },
): boolean {
  // @skjs-expect-error This expression is always true
  return s in x;
}

function refineUnionInRecordAlwaysTrue(
  s: "f" | "g",
  x: { f: number; g: number },
): number {
  // @skjs-expect-error This expression is always true
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
    // @ts-expect-error Invalid return type
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
    // @ts-expect-error Invalid return type
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
    // @skjs-expect-error Unbound field: f | g
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
    // @skjs-expect-error Unbound field: f | g
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
    // @skjs-expect-error Invalid access
    return x[s];
  } else {
    return 0;
  }
}

function refineStringInRecord2(s: string, x: { f: number }): unknown {
  if (s in x) {
    // FIXME
    // @skjs-expect-error Invalid access
    return x[s];
  } else {
    return 0;
  }
}

function literalInTupleAlwaysFalse(): boolean {
  // @skjs-expect-error TODO: in
  return 0 in [];
}

function literalInTupleAlwaysTrue(): boolean {
  // @skjs-expect-error TODO: in
  return 0 in [1];
}

function literalInTupleUnion(x: [number] | [number, number]): boolean {
  // @skjs-expect-error TODO: in
  return 1 in x;
}

function literalInNonObject(x: number): boolean {
  // @ts-expect-error Invalid in
  return 0 in x;
}
