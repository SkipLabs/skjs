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
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return f(x);
}

// @ts-expect-error Required type parameters may not follow optional type parameters.
type TNonLastDefault<X = boolean, Y> = X | Y;

// @ts-expect-error Optional type parameters are not supported for classes and functions
// @ts-expect-error Required type parameters may not follow optional type parameters.
function fNonLastDefault1<X = boolean, Y>(x: X | Y): void {}

// @ts-expect-error Optional type parameters are not supported for classes and functions
// @ts-expect-error Required type parameters may not follow optional type parameters.
function fNonLastDefault2(f: <X = boolean, Y>(x: X | Y) => void): void {}

// @ts-expect-error Optional type parameters are not supported for classes and functions
// @ts-expect-error Required type parameters may not follow optional type parameters.
class cNonLastDefault<X = boolean, Y> {}

/*
    We don't support defaults for type parameters of functions
    This is actually tricky because inference is used for missing type parameters
    (when none are provided or when they have a default value).
    The default value is used only if the inference fails, i.e. the type variable
    is unconstrained.

    Same thing for classes.
*/

// @skjs-expect-error Optional type parameters are not supported for classes and functions
function pair<X, Y = X>(x: X, y: Y): { x: X; y: Y } {
  return { x, y };
}

function callpair1(): { x: 1; y: boolean } {
  const one: 1 = 1;
  return pair(one, true);
}

// function callpair2(): { x: 1 | boolean; y: 1 | boolean } {
//   const one: 1 = 1;
//   return pair(one, true);
// }

// function callpair3(): { x: 1; y: boolean } {
//   const one: 1 = 1;
//   return pair<1, boolean>(one, true);
// }

// function callpair4(): { x: number; y: number } {
//   const one: 1 = 1;
//   return pair<number>(one, 2);
// }

// function callpair5(): { x: 1; y: 1 } {
//   const one: 1 = 1;
//   return pair<1>(one, 2);
// }

// @skjs-expect-error Optional type parameters are not supported for classes and functions
class ClassWithOptionalTypeParam<X = boolean> {}
