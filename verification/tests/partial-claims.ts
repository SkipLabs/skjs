// Deliberately rejected: ordinary checking must retain the prefix without recovery.
function annotationFailure(): boolean {
  const before: boolean = true;
  const bad: true = false;
  const after: boolean = true;
  return after;
}

function expressionFailure(): boolean {
  const before: boolean = true;
  const bad: boolean = missing;
  return before;
}

function complete(): boolean {
  return true;
}
