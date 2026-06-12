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

// Exercises effective param types: optional adds undefined, destructuring
// params keep their pattern shape (SKJS rejects rest after optional)
function describe({ x, y }: { x: number; y: number }, label?: string): number {
  const sum = x + y;
  return sum;
}

// Rest param's effective type is a readonly array
function count(first: number, ...rest: number[]): number {
  return rest.length + 1;
}
