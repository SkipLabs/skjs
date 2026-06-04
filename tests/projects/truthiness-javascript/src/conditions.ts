// truthiness mode "javascript": every type is accepted in a condition, with no
// diagnostics. Narrowing still applies (JavaScript semantics). None of these
// produce an error.

function anyNumber(n: number): void {
  if (n) {
  }
}

function anyVoid(rv: () => void): void {
  if (rv()) {
  }
}

function anyFunctionRef(fn: () => void): void {
  if (fn) {
  }
}

function anyGeneric<T>(t: T): void {
  if (t) {
  }
}

// Narrowing is unaffected by the mode.
function narrows(o: { a: number } | undefined): void {
  if (o) {
    const present: { a: number } = o;
  } else {
    const absent: undefined = o;
  }
}
