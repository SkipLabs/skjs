// Number literals that JS reads as a different value than the exact decimal
// written are unexpected: they overflow to Infinity, underflow to 0, or lose
// precision (including denormal rounding). SKJS warns on each of them; the
// warning annotations below are added together with the warning itself.
// Cosmetic respellings of the same value (1e3, 0x10, 1.0, 1_000, .5, 5.)
// and exactly representable values (0.1, 1e21, 5e-324, -0) stay silent.

// --- precision loss: the double rounds to different digits ---
function precisionLoss(): void {
  const roundsInt = 9007199254740993;
  const roundsDecimal = 0.300000000000000044;
  const roundsHex = 0x20000000000001;
  const roundsLong = 123456789012345678901;
  // denormal rounding
  const roundsDenormal = 9e-324;
  const roundsToDenormal = 3e-324;
}

// --- overflow to Infinity ---
function overflow(): void {
  const over = 1e309;
  const overNeg = -2e309;
  const overHex = 0x10000000000000000;
}

// --- underflow to 0 ---
function underflow(): void {
  const under = 1e-400;
  const underNeg = -1e-400;
  const underDenormal = 2e-324;
}

// in other literal positions: type annotation, property name, enum member,
// template hole
function takesType(x: 9007199254740993): void {}
function propName(): void {
  const obj = { 9007199254740993: 1 };
}
enum Surprise {
  A = 1e309,
  B = 9007199254740993,
}
function tmpl(): void {
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
  const ok10 = .5;
  const ok11 = 5.;
  const ok12 = 0.30000000000000004;
}
