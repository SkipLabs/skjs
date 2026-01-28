function badRecordIteration(): void {
  const record = { a: 1, b: 2 };
  // @skjs-expect-error for-of loop requires an array, string, or iterable type
  for (const value of record) {
    console.log(value);
  }
}

function dictionaryIteration(): number {
  const dictionary: { [key: string]: number } = { a: 1, b: 2 };
  let sum = 0;
  // @skjs-expect-error for-of loop requires an array, string, or iterable type
  for (const value of dictionary) {
    sum += value;
  }
  return sum;
}
