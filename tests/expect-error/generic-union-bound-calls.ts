// A generic function bounded by a union can be called at multiple branches
// of the union within a single expression, with each call typed at the
// instantiation chosen by its argument.
function adHocId<T extends number | string>(x: T): T {
  return x;
}

function main(): number {
  return adHocId("foo").length + (adHocId(2) - 1);
}
