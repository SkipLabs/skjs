// @skjs-callgraph
// fn:factorial: fn:factorial
// fn:isEven: fn:isOdd
// fn:isOdd: fn:isEven

function factorial(n: number): number {
  return n <= 1 ? 1 : n * factorial(n - 1);
}

function isEven(n: number): boolean {
  return n === 0 ? true : isOdd(n - 1);
}
function isOdd(n: number): boolean {
  return n === 0 ? false : isEven(n - 1);
}
