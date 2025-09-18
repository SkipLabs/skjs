type TGen<X> = X;

// @ts-expect-error Invalid number of type arguments: given 0, expected 1
function notEnoughTypeParameters(x: TGen): void {}

// @ts-expect-error Invalid number of type arguments: given 2, expected 1
function tooManyTypeParameters(x: TGen<boolean, number>): void {}

type TDefault<X = boolean> = X;

function takeTDefault(x: TDefault): boolean {
  return x;
}

type TDefaultUsePreviousParam<X, Y = X> = (x: X) => Y;

function applyTDefaultUsePreviousParam<X>(
  f: TDefaultUsePreviousParam<X>,
  x: X,
): X {
  return f(x);
}

function applyTDefaultUsePreviousParamError<X, Y>(
  f: TDefaultUsePreviousParam<X>,
  x: X,
): Y {
  // @ts-expect-error Invalid return type
  return f(x);
}

// @ts-expect-error Required type parameters may not follow optional type parameters.
type TNonLastDefault<X = boolean, Y> = X | Y;

// @ts-expect-error Required type parameters may not follow optional type parameters.
function fNonLastDefault1<X = boolean, Y>(x: X | Y): void {}

// @ts-expect-error Required type parameters may not follow optional type parameters.
function fNonLastDefault2(f: <X = boolean, Y>(x: X | Y) => void): void {}

// @ts-expect-error Required type parameters may not follow optional type parameters.
class cNonLastDefault<X = boolean, Y> {}
