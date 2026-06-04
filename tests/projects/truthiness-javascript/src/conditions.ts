// truthiness mode "javascript": every type is accepted in a condition, with no
// diagnostics. Narrowing still applies (JavaScript semantics). None of these
// produce an error.

function anyNumber(n: number): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (n) {
  }
}

function anyVoid(rv: () => void): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (rv()) {
  }
}

function anyFunctionRef(fn: () => void): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (fn) {
  }
}

function anyGeneric<T>(t: T): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (t) {
  }
}

// Narrowing is unaffected by the mode.
function narrows(o: { a: number } | undefined): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (o) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const present: { a: number } = o;
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const absent: undefined = o;
  }
}
