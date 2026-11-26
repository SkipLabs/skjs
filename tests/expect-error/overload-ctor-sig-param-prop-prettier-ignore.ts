// Parameter property on a body-less constructor overload must error,
// not silently desugar into a class field.
// (prettier-ignore filename: prettier rejects parameter properties on
// body-less constructor declarations at parse time.)
class CtorSigParamProp {
  // @skjs-expect-error Modifier 'public' is not allowed on a function parameter
  constructor(public x: string);
  constructor(x: string | number) {}
}

