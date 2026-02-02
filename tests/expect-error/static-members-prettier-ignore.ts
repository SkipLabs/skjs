// prettier-ignore
// Test static fields in interface (not allowed even in TypeScript)
interface IWithStatic {
  // @ts-expect-error static fields are forbidden
  static readonly x: number;
}
