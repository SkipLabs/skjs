function compare<T>(a: T, b: T): number {
  if (a === b) return 0;
  if (a === null || b === null) return a === null ? -1 : 1;
  if (typeof a !== typeof b) return typeof a < typeof b ? -1 : 1;

  if (typeof a === "number" && typeof b === "number") {
    return a < b ? -1 : 1;
  }

  if (typeof a === "boolean" && typeof b === "boolean") {
    return a < b ? -1 : 1;
  }

  if (typeof a === "string" && typeof b === "string") {
    return a < b ? -1 : 1;
  }

  if (a instanceof Array && b instanceof Array) {
    return compareArrays(a, b);
  }

  if (typeof a === "object" && typeof b === "object") {
    // @skjs-expect-error Invalid call
    return compareObjects(a, b);
  }

  throw "Unsupported types";
}

function compareArrays<T>(a: Array<T>, b: Array<T>): number {
  if (a.length !== b.length) return a.length < b.length ? -1 : 1;
  for (let i = 0; i < a.length; i++) {
    const result = compare(a[i], b[i]);
    if (result !== 0) return result;
  }
  return 0;
}

function compareObjects(a: object, b: object): number {
  const keysA = Object.keys(a).sort();
  const keysB = Object.keys(b).sort();

  let i = 0;
  let j = 0;
  while (i < keysA.length && i < keysB.length) {
    const keyA = keysA[i];
    const keyB = keysB[j];
    if (keyA === undefined || keyB === undefined) {
      // This shouldn't happen in normal cases since we check array bounds
      return keyA === undefined ? -1 : 1;
    }
    if (keyA < keyB) {
      return -1;
    }
    if (keyA > keyB) {
      return 1;
    }
    const valueA = a[keyA];
    const valueB = b[keyB];
    if (valueA === undefined && valueB === undefined) {
      // Both undefined, continue
    } else if (valueA === undefined) {
      return -1;
    } else if (valueB === undefined) {
      return 1;
    } else {
      const result = compare(valueA, valueB);
      if (result !== 0) return result;
    }
    i++;
    j++;
  }

  if (j < keysB.length) return -1;
  if (i < keysA.length) return 1;
  return 0;
}

// Example usage:
console.log(compare(1, 2)); // -1
console.log(compare(2, 2)); // 0
console.log(compare(3, 2)); // 1
console.log(compare({ a: 1 }, { a: 2 })); // -1
console.log(compare({ a: 2 }, { a: 2 })); // 0
console.log(compare({ a: 3 }, { a: 2 })); // 1
console.log(compare([1, 2, 3], [1, 2, 4])); // -1
console.log(compare([1, 2, 3], [1, 2, 3])); // 0
console.log(compare([1, 2, 3], [1, 2, 2])); // 1
