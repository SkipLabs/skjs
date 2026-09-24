class AccessorBox {
  // @skjs-expect-error Get and set accessors are not supported by SKJS; use an ordinary method or data field
  get value(): number {
    return 1;
  }
}
function classAccessorCall(x: AccessorBox): number {
  return x.value();
}
function objectAccessorCall(): number {
  const x = {
    // @skjs-expect-error Get and set accessors are not supported by SKJS; use an ordinary method or data field
    get value(): number {
      return 1;
    },
  };
  return x.value();
}
// @skjs-expect-error Get and set accessors are not supported by SKJS; use an ordinary method or data field
type AccessorShape = { get value(): number };
function shapeAccessorCall(x: AccessorShape): number {
  return x.value();
}
function objectSetter(): void {
  // @skjs-expect-error Get and set accessors are not supported by SKJS; use an ordinary method or data field
  const x = { set value(v: number) {} };
}
function ordinaryMethods(): number {
  const x = {
    get(): number {
      return 1;
    },
    set(v: number): number {
      return v;
    },
  };
  return x.set(x.get());
}
