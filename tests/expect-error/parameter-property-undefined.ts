// An optional parameter property assigns `undefined` to the property when
// the argument is omitted, so its translation to a field must add undefined
// to the field's type (optional fields are exact: present => declared type).
class WithOptionalParamProp {
  constructor(public y?: string) {}
}

// Accepted: the translated field's type includes undefined — the field
// already holds undefined whenever the constructor argument is omitted.
function writeUndefinedToTranslatedField(): void {
  const b = new WithOptionalParamProp("s");
  b.y = undefined;
}

function readTranslatedField(): string | undefined {
  const b = new WithOptionalParamProp();
  return b.y;
}
