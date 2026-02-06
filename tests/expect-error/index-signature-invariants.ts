function checkInvalidFieldAgainstStringIndex(): void {
  // @skjs-expect-error Field a is incompatible with index signature
  const bad: { [k: string]: number; a: string } = { a: "x" };
  console.log(bad);
}
checkInvalidFieldAgainstStringIndex();

// @skjs-expect-error Field x is incompatible with index signature
class InvalidClassFieldAgainstIndex {
  [k: string]: number;
  x: string;

  constructor(x: string) {
    this.x = x;
  }
}

function checkInvalidFieldWriteAgainstStringIndex(): void {
  // Read channel is compatible (`number` <: `number | string`) but write
  // channel is not (`number | string` not <: `number`).
  // @skjs-expect-error Field a is incompatible with index signature writes
  const bad: { [k: string]: number | string; a: number } = { a: 1 };
  console.log(bad);
}
checkInvalidFieldWriteAgainstStringIndex();

function checkReadonlyMismatchAgainstIndex(): void {
  // @skjs-expect-error Field a and overlapping index signature disagree on readonly
  const bad1: { readonly [k: string]: number; a: number } = { a: 1 };
  console.log(bad1);

  // @skjs-expect-error Field a and overlapping index signature disagree on readonly
  const bad2: { [k: string]: number; readonly a: number } = { a: 1 };
  console.log(bad2);
}
checkReadonlyMismatchAgainstIndex();

function checkInvalidIndexKeyType(): void {
  // @skjs-expect-error Invalid index signature key type
  const bad: { [k: boolean]: number } = { true: 1 };
  console.log(bad);
}
checkInvalidIndexKeyType();
