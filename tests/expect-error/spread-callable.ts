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
