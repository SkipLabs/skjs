/**
 * Future source-coverage example: narrow a nullable string and choose a
 * fallback. Null equality is supported, but strings remain outside the source
 * verifier, so this fixture still tests a type boundary.
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
