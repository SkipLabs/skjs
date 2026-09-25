// A symbol in a template throws a TypeError: refused.
function show(s: symbol): string {
  return `s=${s}`;
}
