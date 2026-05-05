// SKJS desugars optional parameter properties to an optional class field
// plus a `this.x = x` initializer, matching TypeScript.
class OptionalParameterProperty {
  constructor(public x?: string) {}

  read(): string | undefined {
    return this.x;
  }
}

function buildWithArg(): OptionalParameterProperty {
  return new OptionalParameterProperty("hello");
}

function buildWithoutArg(): OptionalParameterProperty {
  return new OptionalParameterProperty();
}
