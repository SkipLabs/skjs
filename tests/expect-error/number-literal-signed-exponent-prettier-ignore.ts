// ES exponent parts may carry a sign: 1e+3 is the literal 1000.
// (prettier rewrites 1e+3 to 1e3, hence the file name)

function signedExponentPlus(): void {
  const a: 1000 = 1e+3;
}
