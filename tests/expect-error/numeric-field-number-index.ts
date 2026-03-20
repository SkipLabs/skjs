// Tests that numeric field names are properly checked against number index signatures

function numericFieldIncompatibleWithNumberIndex(x: { readonly 0: number }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function numericFieldIncompatibleWithStringIndex(x: { readonly 0: number }): {
  readonly [arg: string]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function numericFieldCompatibleWithNumberIndex(x: { readonly 0: string }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function numericFieldCompatibleWithStringIndex(x: { readonly 0: string }): {
  readonly [arg: string]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

// Decimal field names match number index signatures
function decimalFieldCompatibleWithNumberIndex(x: { readonly "1.5": string }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function decimalFieldIncompatibleWithNumberIndex(x: {
  readonly "1.5": number;
}): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

// Negative field names match number index signatures
function negativeFieldCompatibleWithNumberIndex(x: { readonly "-1": string }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

// Non-canonical numeric strings are NOT checked against number index signatures
function nonCanonicalLeadingZero(x: { readonly "01": number }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function nonCanonicalTrailingDecimalZero(x: { readonly "1.50": number }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

function nonCanonicalNegativeZero(x: { readonly "-0": number }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}

// Non-numeric field names should not be checked against number index signatures
function stringFieldNotCheckedAgainstNumberIndex(x: { readonly foo: number }): {
  readonly [arg: number]: string;
} {
  // @skjs-expect-error Invalid return type
  return x;
}
