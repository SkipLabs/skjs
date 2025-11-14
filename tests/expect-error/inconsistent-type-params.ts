// @skjs-expect-error Optional type parameters are not supported for classes
class A<Y, X = boolean> {}

// @ts-expect-error Required type parameters may not follow optional type parameters.
class B<X = boolean, Y> {}
