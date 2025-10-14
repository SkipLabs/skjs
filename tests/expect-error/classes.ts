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
  constructor(public f: string) {}

  accessParameterProperty(): string {
    return this.f;
  }
}

class ClassWithPrivateParameterProperty {
  constructor(private f: string) {}

  accessParameterProperty(): string {
    return this.f;
  }
}
