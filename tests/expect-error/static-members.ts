class C1 {
  // @ts-expect-error TODO: field modifier 'static' (TypeChecker#class_)
  static x: string = "a";
}
