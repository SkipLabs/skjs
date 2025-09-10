// Comprehensive tests for for-in and for-of loops

function testForInWithObjects(): void {
  // Test for-in with object - should iterate over property names
  const person = { name: "John", age: 30, city: "NYC" };
  for (const prop in person) {
    const key: "name" | "age" | "city" = prop;
  }

  // Test with empty object
  const empty = {};
  for (const key in empty) {
    const k: string = key;
  }
}

function testForInWithArrays(): void {
  // Test for-in with array - should iterate over indices as strings
  const numbers = [10, 20, 30, 40];
  for (const index in numbers) {
    const idx: "0" | "1" | "2" | "3" = index;
  }

  // Test with string array
  const words = ["hello", "world"];
  for (const i in words) {
    const index: "0" | "1" = i;
  }
}

function testForInWithTuples(): void {
  // Test for-in with tuple - should iterate over indices
  const coord: [number, number] = [10, 20];
  for (const index in coord) {
    const idx: "0" | "1" = index;
  }

  // Test with mixed tuple
  const mixed: [string, number, boolean] = ["test", 42, true];
  for (const i in mixed) {
    const index: "0" | "1" | "2" = i;
  }
}

function testForOfWithArrays(): void {
  // Test for-of with number array - should iterate over values
  const numbers = [1, 2, 3, 4, 5];
  for (const num of numbers) {
    const value: number = num;
  }

  // Test with string array
  const words = ["apple", "banana", "cherry"];
  for (const word of words) {
    const text: string = word;
  }

  // Test with boolean array
  const flags = [true, false, true];
  for (const flag of flags) {
    const bool: boolean = flag;
  }
}

function testForOfWithTuples(): void {
  // Test for-of with homogeneous tuple
  const coords: [number, number, number] = [1, 2, 3];
  for (const coord of coords) {
    const value: number = coord;
  }

  // Test for-of with heterogeneous tuple - should create union type
  const mixed: [string, number, boolean] = ["hello", 42, true];
  for (const item of mixed) {
    // item should be string | number | boolean
    if (typeof item === "string") {
      const s: string = item;
    } else if (typeof item === "number") {
      const n: number = item;
    } else {
      const b: boolean = item;
    }
  }
}

function testNestedForLoops(): void {
  // Test nested for-in and for-of
  const data = {
    section1: [1, 2, 3],
    section2: [4, 5, 6],
  };

  for (const sectionName in data) {
    const name: "section1" | "section2" = sectionName;
    for (const value of data[sectionName]) {
      const num: number = value;
    }
  }
}

function testForLoopsWithControlFlow(): void {
  // Test for-of with continue
  const items = [1, 2, 3, 4, 5];
  for (const item of items) {
    if (item === 3) {
      continue;
    }
    const num: number = item;
  }

  // Test for-in with break
  const obj = { a: 1, b: 2, c: 3, d: 4 };
  for (const key in obj) {
    if (key === "c") {
      break;
    }
    const k: string = key;
  }
}

function testForLoopsWithDifferentDeclarations(): void {
  const arr = [1, 2, 3];
  const obj = { x: 10, y: 20 };

  // Test with let
  for (let value of arr) {
    const v: number = value;
  }

  for (let key in obj) {
    const k: string = key;
  }

  // Test with const
  for (const value of arr) {
    const v: number = value;
  }

  for (const key in obj) {
    const k: string = key;
  }
}
