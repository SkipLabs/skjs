function greet(name: string = "World"): string {
  return "Hello, " + name + "!";
}

function add(a: number, b: number = 10): number {
  return a + b;
}

type DatabaseRow = { [key: string]: number };
export const convertToSkipFormat = <T extends DatabaseRow>(
  rows: T[],
  idField: keyof T = "id",
): Array<[number, [T]]> => {
  return new Array<[number, [T]]>();
};

function main(): void {
  let result1: string = greet();
  let result2: string = greet("Alice");
  let result3: number = add(5);
  let result4: number = add(3, 7);
}
