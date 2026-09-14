// FIXME: writes currently ignore the binding's const flag.
function assignConstant(): number {
  const value: number = 0;
  value = 1;
  return value;
}

function updateConstant(): number {
  const value: number = 0;
  return value++;
}

function destructureConstant(): number {
  const value: number = 0;
  [value] = [1];
  return value;
}

function captureConstant(): () => void {
  const value: number = 0;
  return () => {
    value += 1;
  };
}

// A const binding does not freeze the object it refers to.
function mutateConstantObject(): number {
  const box: { value: number } = { value: 0 };
  box.value++;
  return box.value;
}
