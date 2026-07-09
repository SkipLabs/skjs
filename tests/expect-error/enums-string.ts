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

// tsc rejects literal -> string enum (nominal, outbound-only); SKJS
// accepts it: sound, "a" is SE.A's runtime value.
function literalToStringEnum(): SE {
  return "a";
}

function wrongLiteralToStringEnum(): SE {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "c";
}

function stringToStringEnum(s: string): SE {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
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

function heterogeneousUnion(x: Het): 0 | "s" {
  return x;
}

// tsc types Het[0] as plain string; SKJS gives the member-name literal.
function heterogeneousReverseOnlyNumeric(): "N" {
  return Het[0];
}
