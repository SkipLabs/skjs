// @skjs-callgraph
// method:Calc.double: method:Calc.add

class Calc {
  add(a: number, b: number): number {
    return a + b;
  }
  double(x: number): number {
    return this.add(x, x);
  }
}
