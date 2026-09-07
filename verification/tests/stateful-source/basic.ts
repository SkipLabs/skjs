function copyTrue(): boolean {
  const x: true = true;
  const y: boolean = x;
  return y;
}

function copyFalse(): false {
  const x = false;
  return x;
}

function nullOrBoolean(): null | boolean {
  const x: null | boolean = null;
  return x;
}

function keepOlderBinding(): true {
  const x: true = true;
  const y: false = false;
  return x;
}
