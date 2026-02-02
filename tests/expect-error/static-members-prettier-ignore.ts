// prettier-ignore
// Test static fields in interface (not allowed even in TypeScript)
interface IWithStatic {
  // @skjs-expect-error Missing definition
  static readonly x: number;
}
