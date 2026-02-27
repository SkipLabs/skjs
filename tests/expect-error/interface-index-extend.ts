interface A {
  [key: string]: number;
}

interface B {
  [key: string]: number;
}

interface C extends A, B {}

function testInterfaceIndexExtend(): void {
  const c: C = { x: 1, y: 2 };
  const n: number | undefined = c.x;
}
