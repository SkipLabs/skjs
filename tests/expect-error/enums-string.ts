enum SE {
  A = "a",
  B = "b",
}

function memberToString(): string {
  return SE.A;
}

function memberToItsLiteral(): "a" {
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
  // @skjs-expect-error Property 'a' does not exist on this type
  return SE["a"];
}

enum Het {
  N = 0,
  S = "s",
}

function heterogeneousNumericMember(): 0 {
  return Het.N;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function heterogeneousUnion(x: Het): 0 | "s" {
  return x;
}

function heterogeneousReverseOnlyNumeric(): "N" {
  return Het[0];
}
