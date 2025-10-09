class FieldInitializationSubTyping {
  x: number = 1;
}

class FieldInitializationUsePreciseTyping {
  x: 1 | 2 = 1;
}

class TwoConstructors {
  constructor() {}

  // TODO: error!
  constructor() {}
}

class ClassWithParameterProperty {
  constructor(public f: string) {}

  accessParameterProperty(): string {
    // FIXME
    // @ts-expect-error Unbound field: f
    return this.f;
  }
}
