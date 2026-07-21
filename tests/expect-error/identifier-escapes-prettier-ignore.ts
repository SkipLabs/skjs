// An identifier character may be written as a Unicode escape, and the name is
// the decoded text -- so an escaped spelling and its literal twin are the same
// name. Each function below declares with one spelling and reads with the
// other, which is the property decoding exists for.
//
// Prettier-exempt on purpose: prettier decodes an identifier's escapes to the
// characters they denote, which would make both spellings literal and leave
// every case here comparing a name with itself.

export function escapedThenLiteral(): number {
  const caf\u00e9 = 1;
  return café;
}

export function literalThenEscaped(): number {
  const café = 2;
  return caf\u00e9;
}

export function bracedThenLiteral(): number {
  const caf\u{e9} = 3;
  return café;
}

// A digit cannot start a name but may continue one, so this names `a1b`.
export function escapedDigitContinues(): number {
  const a\u0031b = 4;
  return a1b;
}

// The escape may spell the first character too.
export function escapedStart(): number {
  const \u00e9x = 5;
  return éx;
}

// Property names are identifiers, and decode the same way.
export function escapedProperty(): number {
  const o = { caf\u00e9: 6 };
  return o.café;
}
