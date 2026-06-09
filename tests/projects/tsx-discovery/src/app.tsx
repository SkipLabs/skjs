function greet(name: number): string {
  // @skjs-expect-error Right operand of '+' is not assignable to the left operand's type
  return "Hello, " + name;
}
