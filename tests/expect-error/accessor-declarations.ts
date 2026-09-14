class AccessorBox {
  get value(): number {
    return 1;
  }
}
function classAccessorCall(x: AccessorBox): number {
  return x.value();
}
function objectAccessorCall(): number {
  const x = {
    get value(): number {
      return 1;
    },
  };
  return x.value();
}
type AccessorShape = { get value(): number };
function shapeAccessorCall(x: AccessorShape): number {
  return x.value();
}
function objectSetter(): void {
  // @skjs-expect-error Function 'value' must have an explicit return type annotation
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
