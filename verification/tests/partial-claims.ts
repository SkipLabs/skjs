/**
 * Deliberately give false a true annotation. Normal collection retains claims
 * before the error; optional keep-going may collect later statements. This is
 * a real invalid annotation, not an incompleteness witness.
 */
function annotationFailure(): boolean {
  const before: boolean = true;
  const bad: true = false;
  const after: boolean = true;
  return after;
}

/**
 * Stop collection at an unbound identifier. The fixture distinguishes a
 * visited expression with no usable claim from code that was never visited.
 */
function expressionFailure(): boolean {
  const before: boolean = true;
  const bad: boolean = missing;
  return before;
}

/**
 * Provide a valid definition after rejected ones. Its complete claims show
 * that collection can continue across function boundaries.
 */
function complete(): boolean {
  return true;
}
