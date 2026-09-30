// A key found present stays present: the object's records have it from then
// on, as a field of the optional key's contract, `T | undefined`.

// A passed `in` test, then a read other than `undefined`.
function inTest(x: { f?: number }): number {
  if ("f" in x && x.f !== undefined) {
    return x.f;
  }
  return 0;
}

// A read found something other than `undefined`, which an absent key reads.
function notUndefined(obj: { val?: number }): number {
  if (obj.val !== undefined) {
    const n: number = obj.val;
    return n;
  }
  return 0;
}

// The same in a conditional's arm.
function inArm(obj: { readonly val?: number }): number {
  const r: number = obj.val !== undefined ? obj.val : 0;
  return r;
}

// A truthy read of an object-typed optional key.
function truthy(x: { f?: { a: number } }): number {
  if (x.f) {
    const present: { a: number } = x.f;
    return present.a;
  }
  return 0;
}

// Presence is fixed at allocation: a call after the test does not undo it,
// and the object meets a required field of the key's contract.
function afterCall(
  x: { f?: number },
  g: () => void,
): { f: number | undefined } {
  if ("f" in x) {
    g();
    return x;
  }
  return { f: 0 };
}

// A read of an optional key keeps what is known of other fields.
function keepsFacts(
  x: { f: number | null },
  input: { item?: { f: number } },
): number {
  if (x.f !== null) {
    const { item: y = x } = input;
    const z: number = x.f;
    if (y.f !== null) return y.f + z;
  }
  return 0;
}
