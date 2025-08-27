function expectsIndexedObject(_x: { [f: string]: number }): void {}

function correctIndexReturnTypeGet(x: {
  [f: string]: number;
}): number | undefined {
  return x["a"];
}

function correctIndexReturnTypeDot(x: {
  [f: string]: number;
}): number | undefined {
  return x.a;
}
