// exemptConstantRechecks on (tsconfig "exemptConstantRechecks": true):
// re-checking a narrowed discriminant binding or field against a hoisted
// literal-initialized `const` or enum member is exempt from SKJS2074, while
// constant-vs-constant, unnarrowed singleton, mutable `let`, and non-literal
// `const` comparisons still warn. Default (flag off) behavior is tested in
// tests/expect-error/equality.ts.

const B = "b";

function namedConstantRecheck(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
  } else if (x === B) {
    return "second";
  }
  return "";
}

function localNamedConstantRecheck(x: "a" | "b"): string {
  const b = "b";
  if (x === "a") {
    return "first";
  } else if (x === b) {
    return "second";
  }
  return "";
}

type TaggedAB = { kind: "a"; n: number } | { kind: "b"; s: string };
function fieldNamedConstantRecheck(x: TaggedAB): string {
  if (x.kind === "a") {
    return "first";
  } else if (x.kind === B) {
    return "second";
  }
  return "";
}

enum Color {
  Red = "red",
  Blue = "blue",
}

function enumMemberRecheck(x: Color): string {
  if (x === Color.Red) {
    return "red";
  } else if (x === Color.Blue) {
    return "blue";
  }
  return "";
}

function enumBracketMemberRecheck(x: Color): string {
  if (x === Color.Red) {
    return "red";
  } else if (x === Color["Blue"]) {
    return "blue";
  }
  return "";
}

function namedConstantOnLeftRecheck(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
  } else if (B === x) {
    return "second";
  }
  return "";
}

// Negative cases: still warn even with exemptConstantRechecks on
const A1 = "a";
const A2 = "a";
function twoTopLevelConstants(): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return A1 === A2;
}

function twoLocalConstants(): boolean {
  const x = 1;
  const y = 1;
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

function twoEnumMembersSameValue(): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return Color.Red === Color.Red;
}

function singletonParamVsNamedConstant(x: "b"): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === B;
}

function singletonParamVsEnumMember(x: Color.Blue): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === Color.Blue;
}

function narrowedVsMutableLet(x: "a" | "b"): string {
  let b: "b" = "b" as const;
  if (x === "a") {
    return "first";
    // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  } else if (x === b) {
    return "second";
  }
  return "";
}

function getB(): "b" {
  return "b";
}
function narrowedVsNonLiteralConst(x: "a" | "b"): string {
  const b = getB();
  if (x === "a") {
    return "first";
    // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  } else if (x === b) {
    return "second";
  }
  return "";
}
