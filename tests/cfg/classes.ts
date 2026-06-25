// Constructors get a CFG with return type void (a return type annotation on
// a constructor is rejected, TS1093); methods get CFGs like functions
class Counter {
  count: number;
  step: number;
  constructor(start: number, step?: number) {
    this.count = start;
    if (step === undefined) {
      this.step = 1;
    } else {
      this.step = step;
    }
  }
  increment(): number {
    this.count = this.count + this.step;
    return this.count;
  }
}
