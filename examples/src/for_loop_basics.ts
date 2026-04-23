// Basic for-in and for-of loop examples

function demonstrateForIn(): Array<string> {
  const obj = { firstName: "John", lastName: "Doe", age: 30 };
  const keys: Array<string> = new Array();

  for (const key in obj) {
    keys.push(key); // key is string
  }

  return keys;
}

function demonstrateForOf(): number {
  const numbers = [1, 2, 3, 4, 5];
  let sum = 0;

  for (const num of numbers) {
    sum += num; // num is number
  }

  return sum;
}

function demonstrateArrayIndexIteration(): Array<string> {
  const colors = ["red", "green", "blue"];
  const indices: Array<string> = new Array();

  for (const index in colors) {
    indices.push(index); // index is "0" | "1" | "2"
  }

  return indices;
}

function demonstrateTupleIteration(): string {
  // @skjs-expect-error Invalid annotation
  const info: [string, number, boolean] = ["Alice", 25, true];
  let result = "";

  for (const item of info) {
    if (typeof item === "string") {
      result += item;
    } else if (typeof item === "number") {
      result += item.toString();
    } else {
      result += item.toString();
    }
  }

  return result;
}
