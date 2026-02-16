function badRecordIteration(): void {
  const record = { a: 1, b: 2 };
  // @ts-expect-error Invalid iterable type for for-of loop
  for (const value of record) {
    console.log(value);
  }
}

function dictionaryIteration(): number {
  const dictionary: { [key: string]: number } = { a: 1, b: 2 };
  let sum = 0;
  // @skjs-expect-error Invalid iterable type for for-of loop
  for (const value of dictionary) {
    sum += value;
  }
  return sum;
}
