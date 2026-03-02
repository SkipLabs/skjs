// Array destructuring uses precise integer-indexed field types when available
// for Array subclasses, but uses iterator element type for non-arrays.

class Pair extends Array<string | number> {
  0: string = "";
  1: number = 0;
}

function testDestructureIntegerFields(): void {
  let [x, y] = new Pair();
  __SKJS_show(x, "string");
  __SKJS_show(y, "number");
}

// Non-array classes with numeric fields should use iterator element type,
// not the numeric field type.
declare const notAnArray: {
  0: number;
  [Symbol.iterator](): { next(): { value: string; done: boolean } };
};

function testNotAnArray(): void {
  let [x] = notAnArray;
  __SKJS_show(x, "string | undefined");
}
