class RestRunner<T extends readonly unknown[]> {
  args: T;
  callback: (...args: T) => number;
  constructor(args: T, callback: (...args: T) => number) {
    this.args = args;
    this.callback = callback;
  }
  set(args: T): void {
    this.args = args;
  }
  run(): number {
    return this.callback(...this.args);
  }
}
function loseArgument(seed: number): number {
  // @skjs-expect-warning This 'as const' is unnecessary
  const runner = new RestRunner([seed] as const, (x: number): number => x);
  // @ts-expect-error Argument is not assignable to the parameter's type
  runner.set([] as const);
  return runner.run();
}
function keepArgument(seed: number): number {
  // @skjs-expect-warning This 'as const' is unnecessary
  const runner = new RestRunner([seed] as const, (x: number): number => x);
  runner.set([seed] as const);
  return runner.run();
}
function changeArgument(seed: number): number {
  // @skjs-expect-warning This 'as const' is unnecessary
  const runner = new RestRunner([seed] as const, (x: number): number => x);
  // @ts-expect-error Argument is not assignable to the parameter's type
  runner.set(["changed"] as const);
  return runner.run();
}
