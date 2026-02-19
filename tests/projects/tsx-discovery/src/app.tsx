function greet(name: number): string {
  // @skjs-expect-error Invalid + operand
  return "Hello, " + name;
}
