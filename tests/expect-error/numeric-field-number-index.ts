// Tests that numeric field names are properly checked against number index signatures

function numericFieldIncompatibleWithNumberIndex(x: { 0: number }): {
  [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function numericFieldIncompatibleWithStringIndex(x: { 0: number }): {
  [arg: string]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function numericFieldCompatibleWithNumberIndex(x: { 0: string }): {
  [arg: number]: string;
} {
  return x;
}

function numericFieldCompatibleWithStringIndex(x: { 0: string }): {
  [arg: string]: string;
} {
  return x;
}

// Decimal field names should be checked against number index signatures
// FIXME: SKJS does not yet recognize "1.5" as numeric
function decimalFieldCompatibleWithNumberIndex(x: { "1.5": string }): {
  [arg: number]: string;
} {
  return x;
}

// FIXME: should error (value type mismatch) but "1.5" is not recognized as numeric
function decimalFieldIncompatibleWithNumberIndex(x: { "1.5": number }): {
  [arg: number]: string;
} {
  return x;
}

// Negative field names should be checked against number index signatures
function negativeFieldCompatibleWithNumberIndex(x: { "-1": string }): {
  [arg: number]: string;
} {
  return x;
}

// Non-canonical numeric strings: toIntOption() wrongly recognizes "01" and "-0"
// FIXME: "01" should NOT be checked against number index (non-canonical)
function nonCanonicalLeadingZero(x: { "01": number }): {
  [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function nonCanonicalTrailingDecimalZero(x: { "1.50": number }): {
  [arg: number]: string;
} {
  return x;
}

// FIXME: "-0" should NOT be checked against number index (non-canonical)
function nonCanonicalNegativeZero(x: { "-0": number }): {
  [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

// Non-numeric field names should not be checked against number index signatures
function stringFieldNotCheckedAgainstNumberIndex(x: { foo: number }): {
  [arg: number]: string;
} {
  return x;
}
