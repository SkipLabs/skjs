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

// Decimal field names match number index signatures
function decimalFieldCompatibleWithNumberIndex(x: { "1.5": string }): {
  [arg: number]: string;
} {
  return x;
}

function decimalFieldIncompatibleWithNumberIndex(x: { "1.5": number }): {
  [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

// Negative field names match number index signatures
function negativeFieldCompatibleWithNumberIndex(x: { "-1": string }): {
  [arg: number]: string;
} {
  return x;
}

// Non-canonical numeric strings are NOT checked against number index signatures
function nonCanonicalLeadingZero(x: { "01": number }): {
  [arg: number]: string;
} {
  return x;
}

function nonCanonicalTrailingDecimalZero(x: { "1.50": number }): {
  [arg: number]: string;
} {
  return x;
}

function nonCanonicalNegativeZero(x: { "-0": number }): {
  [arg: number]: string;
} {
  return x;
}

// Non-numeric field names should not be checked against number index signatures
function stringFieldNotCheckedAgainstNumberIndex(x: { foo: number }): {
  [arg: number]: string;
} {
  return x;
}
