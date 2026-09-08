/**
 * Future source-coverage example: narrow a nullable string and choose a
 * fallback. Strings and null equality are outside the current source verifier,
 * so this fixture tests an explicit boundary.
 */
function label(x: string | null): string {
  const fallback: string = "missing";
  if (x === null) {
    return fallback;
  }
  const found = x;
  return found;
}

/**
 * Call the preceding top-level function and return its result. This records a
 * future call-lowering case rather than a currently verified example.
 */
function shout(x: string | null): string {
  const s = label(x);
  return s;
}
