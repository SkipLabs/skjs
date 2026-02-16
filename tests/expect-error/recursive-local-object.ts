type L = null | { tail: L };

function f(): L {
  let x = null;
  while (true) {
    x = { tail: x };
    break;
  }
  return x;
}
