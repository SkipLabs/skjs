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

function mergeWithLocals(): true {
  const outer: true = true;
  if (true) {
    const local: false = false;
    const another: null = null;
  } else {
    const local: null = null;
  }
  return outer;
}

function bothReturn(): boolean {
  if (false) {
    return true;
  } else {
    return false;
  }
}

function nestedMerge(): null {
  const outer: null = null;
  if (true) {
    const local: boolean = false;
    if (false) {
      const inner: true = true;
    }
  }
  return outer;
}

function earlyArm(): boolean {
  const outer: false = false;
  if (false) {
    return true;
  }
  return outer;
}
