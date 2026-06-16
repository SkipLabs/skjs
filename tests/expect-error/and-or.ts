function f(x: 1 | 2 | 3): 1 | 2 {
  if (x !== 1 && x !== 2) {
    return 1;
  } else {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
}
