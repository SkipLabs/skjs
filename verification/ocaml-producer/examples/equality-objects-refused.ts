// Two functions carry no field, and so no identity the model can compare.
function sameFunction(f: () => number, g: () => number): boolean {
  return f === g;
}
