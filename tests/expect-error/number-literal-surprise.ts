// Number literals that JS reads as a different value than the exact decimal
// written are unexpected: they overflow to Infinity, underflow to 0, or lose
// precision (including denormal rounding). SKJS warns on each of them; the
// warning annotations below are added together with the warning itself.
// Cosmetic respellings of the same value (1e3, 0x10, 1.0, 1_000, .5, 5.)
// and exactly representable values (0.1, 1e21, 5e-324, -0) stay silent.

// --- precision loss: the double rounds to different digits ---
function precisionLoss(): void {
  // @skjs-expect-warning Number literal '9007199254740993' is rounded to 9007199254740992 by IEEE-754 double precision
  const roundsInt = 9007199254740993;
  // @skjs-expect-warning Number literal '0.300000000000000044' is rounded to 0.30000000000000004 by IEEE-754 double precision
  const roundsDecimal = 0.300000000000000044;
  // @skjs-expect-warning Number literal '0x20000000000001' is rounded to 9007199254740992 by IEEE-754 double precision
  const roundsHex = 0x20000000000001;
  // @skjs-expect-warning Number literal '123456789012345678901' is rounded to 123456789012345680000 by IEEE-754 double precision
  const roundsLong = 123456789012345678901;
  // a radix literal past 2^53
  // @skjs-expect-warning Number literal '0x10000000000000000' is rounded to 18446744073709552000 by IEEE-754 double precision
  const roundsRadixHuge = 0x10000000000000000;
  // denormal rounding
  // @skjs-expect-warning Number literal '9e-324' is rounded to 1e-323 by IEEE-754 double precision
  const roundsDenormal = 9e-324;
  // @skjs-expect-warning Number literal '3e-324' is rounded to 5e-324 by IEEE-754 double precision
  const roundsToDenormal = 3e-324;
}

// --- overflow to Infinity ---
function overflow(): void {
  // @skjs-expect-warning Number literal '1e309' overflows to Infinity
  const over = 1e309;
  // @skjs-expect-warning Number literal '2e309' overflows to Infinity
  const overNeg = -2e309;
}

// --- underflow to 0 ---
function underflow(): void {
  // @skjs-expect-warning Number literal '1e-400' underflows to 0
  const under = 1e-400;
  // @skjs-expect-warning Number literal '1e-400' underflows to 0
  const underNeg = -1e-400;
  // @skjs-expect-warning Number literal '2e-324' underflows to 0
  const underDenormal = 2e-324;
}

// in other literal positions: type annotation, property name, enum member,
// template hole
// @skjs-expect-warning Number literal '9007199254740993' is rounded to 9007199254740992 by IEEE-754 double precision
function takesType(x: 9007199254740993): void {}
function propName(): void {
  // @skjs-expect-warning Number literal '9007199254740993' is rounded to 9007199254740992 by IEEE-754 double precision
  const obj = { 9007199254740993: 1 };
}
enum Surprise {
  // @skjs-expect-warning Number literal '1e309' overflows to Infinity
  A = 1e309,
  // @skjs-expect-warning Number literal '9007199254740993' is rounded to 9007199254740992 by IEEE-754 double precision
  B = 9007199254740993,
}
function tmpl(): void {
  // @skjs-expect-warning Number literal '9007199254740993' is rounded to 9007199254740992 by IEEE-754 double precision
  const t = `${9007199254740993}`;
}

// --- controls: no warning, same value or exactly representable ---
function controls(): void {
  const ok1 = 1e3;
  const ok2 = 0x10;
  const ok3 = 1.0;
  const ok4 = 1_000;
  const ok5 = 0.1;
  const ok6 = 1e21;
  const ok7 = 5e-324;
  const ok8 = -0;
  const ok9 = 9007199254740992;
  const ok10 = 0.5;
  const ok11 = 5;
  const ok12 = 0.30000000000000004;
}
