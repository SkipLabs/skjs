// A rest parameter typed by a type parameter binds the array a call collects
// at that parameter, which only an instance fixes: no allocation rule gives
// a function definition's body that array.
export function bare<T extends readonly number[]>(...args: T): number {
  return args.length;
}
