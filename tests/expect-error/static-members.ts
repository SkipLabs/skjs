class C1 {
  // @ts-expect-error static fields are forbidden
  static x: string = "a";
}
