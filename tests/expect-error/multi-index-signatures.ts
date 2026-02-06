type MultiIndex = { [k: string]: number } & { [k: number]: 1 };

function multiIndexRead(m: MultiIndex): number | undefined {
  return m[0];
}

function multiIndexWriteOneOk(m: MultiIndex): void {
  const one: 1 = 1;
  m[0] = one;
}

function multiIndexWriteTwoShouldFail(m: MultiIndex): void {
  const two: 2 = 2;
  // @skjs-expect-error Invalid assignment
  m[0] = two;
}

type UnionMultiIndex = { [k: string]: number } | { [k: number]: 1 };

function unionMultiIndexRead(u: UnionMultiIndex): number | undefined {
  return u[0];
}

function unionMultiIndexWriteShouldFail(u: UnionMultiIndex): void {
  const one: 1 = 1;
  // @skjs-expect-error Invalid assignment
  u[0] = one;
}

type UnionSameIndex = { [k: string]: number } | { [name: string]: number };

function unionSameIndexWriteOk(u: UnionSameIndex): void {
  const one: 1 = 1;
  u["x"] = one;
}

type InterSameIndex = { [k: string]: number } & { [name: string]: number };

function interSameIndexWriteOk(i: InterSameIndex): void {
  const two: 2 = 2;
  i["y"] = two;
}
