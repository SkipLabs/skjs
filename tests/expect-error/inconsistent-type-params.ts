// @skjs-expect-error Optional type parameters are not supported for classes and functions
class A<Y, X = boolean> {}

// @ts-expect-error Optional type parameters are not supported for classes and functions
class B<X = boolean, Y> {}
