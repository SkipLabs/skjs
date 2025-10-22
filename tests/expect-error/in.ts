function literalInRecordAlwaysTrue(x: { f: number }): boolean {
  // @ts-expect-error This expression is always true
  return "f" in x;
}

function literalInRecordOpt(x: { f?: number }): boolean {
  return "f" in x;
}

function literalInRecordNotAlwaysFalse(x: { f: number }): boolean {
  return "g" in x;
}

function literalInRecordIndex(x: { [f: string]: number }): boolean {
  return "a" in x;
}

function literalInRecordUnion(x: { f: number } | { g: number }): boolean {
  return "f" in x;
}

function literalInRecordOptUnion(x: { f?: number } | { g: number }): boolean {
  return "f" in x;
}

function unionInRecord(s: "f" | "g", x: { f: number }): boolean {
  return s in x;
}

function unionInRecordOpt(s: "f" | "g", x: { f?: number }): boolean {
  return s in x;
}

function unionInRecordAlwaysTrue(
  s: "f" | "g",
  x: { f: number; g: number },
): boolean {
  // @ts-expect-error This expression is always true
  return s in x;
}

function unionInRecordOpt2(
  s: "f" | "g",
  x: { f?: number; g: number },
): boolean {
  return s in x;
}

function unionInRecordOpt3(
  s: "f" | "g",
  x: { f?: number; g?: number },
): boolean {
  return s in x;
}

function unionInRecordNotAlwaysFalse(s: "f" | "g", x: { h: number }): boolean {
  return s in x;
}

function stringInRecord(s: string, x: { f: number }): boolean {
  return s in x;
}

function literalInTupleAlwaysFalse(): boolean {
  // @ts-expect-error TODO: in
  return 0 in [];
}

function literalInTupleAlwaysTrue(): boolean {
  // @ts-expect-error TODO: in
  return 0 in [1];
}

function literalInTupleUnion(x: [number] | [number, number]): boolean {
  // @ts-expect-error TODO: in
  return 1 in x;
}

function literalInNonObject(x: number): boolean {
  // @ts-expect-error Invalid in
  return 0 in x;
}
