/**
 * An `in` test of a key every object inherits from `Object.prototype`, which
 * the model does not hold: its own-key test would answer `false` where
 * JavaScript answers `true` (DESIGN.md, "Guards").
 */
function describe(x: { name: string }): string {
  if ("toString" in x) {
    return "printable";
  }
  return "never";
}
