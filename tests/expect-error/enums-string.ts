// @skjs-expect-error enum is not supported by SKJS (ignored)
enum SE {
  A = "a",
  B = "b",
}

function memberToString(): string {
  // @skjs-expect-error Cannot find name
  return SE.A;
}

function memberToItsLiteral(): "a" {
  // @skjs-expect-error Cannot find name
  return SE.A;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function literalToStringEnum(): SE {
  return "a";
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function wrongLiteralToStringEnum(): SE {
  return "c";
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function stringToStringEnum(s: string): SE {
  return s;
}

function stringEnumHasNoReverseMapping(): string {
  // @skjs-expect-error Cannot find name
  return SE["a"];
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Het {
  N = 0,
  S = "s",
}

function heterogeneousNumericMember(): 0 {
  // @skjs-expect-error Cannot find name
  return Het.N;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function heterogeneousUnion(x: Het): 0 | "s" {
  return x;
}

function heterogeneousReverseOnlyNumeric(): "N" {
  // @skjs-expect-error Cannot find name
  return Het[0];
}
