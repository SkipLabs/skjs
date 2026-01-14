// Test that T & U is covered by T when inferring type parameters.
// When a method uses an outer type parameter T in a union with
// an inferred parameter V, passing T & U should not over-constrain V.

class Helper<T> {
  f<V>(a: T | V, b: V): V {
    return b;
  }
}

// Verify explicit type args work
function testExplicit<T, U>(x: T & U, h: Helper<T>): string {
  return h.f<string>(x, "hello");
}

// When checking (T & U) <: (T | V), the T branch covers T & U,
// so V remains unconstrained and can be inferred from the second arg.
function testInference<T, U>(x: T & U, h: Helper<T>): string {
  return h.f(x, "hello");
}
