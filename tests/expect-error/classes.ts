class FieldInitializationSubTyping {
  x: number = 1;
}

class FieldInitializationUsePreciseTyping {
  x: 1 | 2 = 1;
}

class TwoConstructors {
  constructor() {}

  // @ts-expect-error Multiple constructor implementations are not allowed.
  constructor() {}
}

class ClassWithParameterProperty {
  // FIXME
  // @ts-expect-error TODO: field modifier 'public' (TypeChecker#class_)
  constructor(public f: string) {}

  accessParameterProperty(): string {
    return this.f;
  }
}

class ClassWithPrivateParameterProperty {
  // FIXME
  // @ts-expect-error TODO: field modifier 'private' (TypeChecker#class_)
  constructor(private f: string) {}

  accessParameterProperty(): string {
    return this.f;
  }
}
