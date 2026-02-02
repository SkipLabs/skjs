// prettier-ignore
// Test static fields in interface (TS#1070 - not allowed even in TypeScript)
interface IWithStatic {
  // @skjs-expect-error 'static' modifier cannot appear on a type member.
  static readonly x: number;
}
