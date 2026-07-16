// A type referenced twice must be expanded once, not once per mention.
//
// Each alias here doubles the length of the one before it, so if every mention
// re-expands its referent, N aliases cost 2^N: this file took 13.8 GB and 23 s
// at N=18 and exhausted memory at N=22, where tsc, which caches instantiation,
// stays flat. It is checked as a template literal type because reduction is the
// only thing that forces a type to be expanded eagerly enough to compound.
//
// Kept at a size that is instant when the expansion cache hits and hopeless
// when it does not, so a regression here fails the suite by timing out rather
// than by a wrong diagnostic.
type D0 = "ab";
type D1 = `${D0}${D0}`;
type D2 = `${D1}${D1}`;
type D3 = `${D2}${D2}`;
type D4 = `${D3}${D3}`;
type D5 = `${D4}${D4}`;
type D6 = `${D5}${D5}`;
type D7 = `${D6}${D6}`;
type D8 = `${D7}${D7}`;
type D9 = `${D8}${D8}`;
type D10 = `${D9}${D9}`;
type D11 = `${D10}${D10}`;
type D12 = `${D11}${D11}`;
type D13 = `${D12}${D12}`;
type D14 = `${D13}${D13}`;
type D15 = `${D14}${D14}`;
type D16 = `${D15}${D15}`;
type D17 = `${D16}${D16}`;
type D18 = `${D17}${D17}`;
type D19 = `${D18}${D18}`;
type D20 = `${D19}${D19}`;

// D20 is 2^21 characters: only reachable if each mention is expanded once.
function doubling(x: D20): D20 {
  return x;
}
