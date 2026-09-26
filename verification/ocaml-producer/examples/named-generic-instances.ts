// Two instances of a declaration with generic methods are related through
// those methods, which the positive checker relates only by identity.
export function widen(p: Promise<number>): Promise<number | string> {
  return p;
}
