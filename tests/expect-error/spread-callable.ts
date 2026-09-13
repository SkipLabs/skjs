// Spreading a callable or constructable object. Object spread copies only own
// enumerable properties, so the call/construct signature is dropped (it is not
// a property) and the object's own properties are kept — as in TypeScript and
// JavaScript.

// Callable object with a property: the property is kept, the call signature
// dropped, so the result is `{ tag: string }` and not callable.
function spreadCallableWithProp(fn: (() => number) & { tag: string }): {
  tag: string;
} {
  return { ...fn };
}

// A plain function has no own enumerable properties, so the spread is empty.
function spreadPlainFunction(fn: () => number): {} {
  return { ...fn };
}

// A constructor's construct signature is likewise dropped.
function spreadConstructor(c: new () => object): {} {
  return { ...c };
}

class PrototypeReader {
  value: number = 1;
  read(): number {
    return this.value;
  }
}

function spreadPrototypeMethod(source: PrototypeReader): number {
  const copy = { ...source };
  // @ts-expect-error This expression is not callable
  return copy.read();
}

function restPrototypeMethod(source: PrototypeReader): number {
  const { value, ...copy } = source;
  // @ts-expect-error This expression is not callable
  return copy.read();
}

// A function-valued instance field is an own property and must survive copying.
class OwnReader {
  read: () => number = () => 1;
}

function spreadOwnFunction(source: OwnReader): number {
  const copy = { ...source };
  return copy.read();
}

function spreadClassData(source: PrototypeReader): number {
  const copy = { ...source };
  return copy.value;
}

// A readonly property annotation can hide a method's declaration provenance.
function annotatedPrototypeCopy(source: PrototypeReader): number {
  const alias: { readonly read: (this: PrototypeReader) => number } = source;
  const copy = { ...alias };
  // FIXME: the annotation erases the fact that copying may omit this method.
  return copy.read.call(source);
}

function annotatedOwnCopy(source: OwnReader): number {
  const alias: { readonly read: () => number } = source;
  const copy = { ...alias };
  return copy.read();
}
