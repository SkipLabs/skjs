function f(x: 1 | 2 | 3): 1 | 2 {
  if (x !== 1 && x !== 2) {
    return 1;
  } else {
    return x;
  }
}

function g(x: 1 | 2 | 3): 1 | 2 {
  if (x === 1 || x === 2) {
    return x;
  } else {
    return 1;
  }
}
