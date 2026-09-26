// A constructor parameter with a default: construct code is a term over plain
// parameters, with no default schedule as a closure has.
class Counter {
  constructor(public start: number = 0) {}
}
export function make(): number {
  return new Counter().start;
}
