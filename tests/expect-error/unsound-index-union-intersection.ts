function intersectionIndexAssignShouldFail(): void {
  const one: 1 = 1;
  // @skjs-expect-error Invalid annotation
  const v: { [k: string]: 1 } & { [k: string]: 2 } = { x: one };
  console.log(v);
}

function intersectionIndexWriteOneShouldFail(
  v: { [k: string]: 1 } & { [k: string]: 2 },
): void {
  const one: 1 = 1;
  // @skjs-expect-error Invalid assignment
  v["x"] = one;
}

function intersectionIndexWriteTwoShouldFail(
  v: { [k: string]: 1 } & { [k: string]: 2 },
): void {
  const two: 2 = 2;
  // @skjs-expect-error Invalid assignment
  v["x"] = two;
}

function unionIndexWriteShouldFail(v: { [k: string]: 1 } | { [k: string]: 2 }): void {
  const one: 1 = 1;
  // @skjs-expect-error Invalid assignment
  v["x"] = one;
}

function fieldAndIndexIntersectionWriteShouldFail(v: { a: 1 } & { [k: string]: 2 }): void {
  const one: 1 = 1;
  // @skjs-expect-error Invalid assignment
  v["a"] = one;
}

function unionFieldAndIndexOverlapWriteOneShouldFail(
  v: { a: 1 } | { [k: string]: 2 },
): void {
  const one: 1 = 1;
  // @skjs-expect-error Invalid assignment
  v["a"] = one;
}

function unionFieldAndIndexOverlapWriteTwoShouldFail(
  v: { a: 1 } | { [k: string]: 2 },
): void {
  const two: 2 = 2;
  // @skjs-expect-error Invalid assignment
  v["a"] = two;
}

function unionFieldAndIndexOverlapRead(
  v: { a: 1 } | { [k: string]: 2 },
): 1 | 2 {
  return v["a"];
}
