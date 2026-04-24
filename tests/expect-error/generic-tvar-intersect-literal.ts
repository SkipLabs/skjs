// A type parameter T that appears both bare and intersected with a literal
// type in the same signature is inferred from both positions. Here, x
// contributes "hi" to T and y (typed `T & "fixed"`) contributes "fixed", so
// T is inferred as `"hi" | "fixed"`.
function tag<T>(x: T, y: T & "fixed"): T {
  return x;
}

function main(): string {
  return tag("hi", "fixed");
}
