function add(a: number, b: number): number {
  const sum = a + b;
  let doubled = sum * 2;
  doubled = doubled + 1;
  return doubled;
}

function greet(name: string): string {
  const message = "hello, " + name;
  return message;
}
