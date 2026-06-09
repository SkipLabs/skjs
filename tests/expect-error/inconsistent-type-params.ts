// @skjs-expect-error Optional type parameters are not supported for classes and functions
class A<Y, X = boolean> {}

// @ts-expect-error Optional type parameters are not supported for classes and functions
// @ts-expect-error Required type parameters may not follow optional type parameters.
class B<X = boolean, Y> {}
