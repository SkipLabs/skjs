// Parameter property on a body-less constructor overload must error (TS2369),
// not silently desugar into a class field.
// (prettier-ignore filename: prettier rejects parameter properties on
// body-less constructor declarations at parse time.)
class CtorSigParamProp {
  // Currently silent: parser desugars `public x` into a field even on FDBNone.
  constructor(public x: string);
  constructor(x: string | number) {
    this.x = "hi";
  }
}
