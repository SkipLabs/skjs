// Array destructuring uses precise integer-indexed field types when available.

class Pair extends Array<string | number> {
  0: string = "";
  1: number = 0;
}

function testDestructureIntegerFields(): void {
  let [x, y] = new Pair();
  __SKJS_show(x, "string");
  __SKJS_show(y, "number");
}
