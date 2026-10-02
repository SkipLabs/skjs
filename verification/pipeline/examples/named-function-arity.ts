// A module function is its annotated signature: where a signature binding
// more parameters is expected, it is refused by name (a closure literal is
// offered the longer signature instead).
function one(_x: number): string {
  return "one";
}
export function widen(): (a: number, b: string) => string {
  return one;
}
