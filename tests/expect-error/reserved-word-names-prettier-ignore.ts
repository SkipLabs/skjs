// A reserved word is a perfectly good property name, so these all typecheck --
// the check that rejects a reserved binding must leave property positions alone.

export function reservedProperties(): number {
  const o = { if: 1, class: 2, return: 3 };
  return o.if + o.class + o.return;
}

export function reservedMemberAndKey(o: { switch: number }): number {
  const { switch: s } = o;
  return s;
}

export class ReservedMembers {
  if(): number {
    return 1;
  }
  static class(): number {
    return 2;
  }
}

export enum ReservedEnumMembers {
  if,
  else,
  for,
}

// A reserved word may not name a binding. The error stops parsing, so it ends
// the file (the harness requires a parse error on the last non-empty line); the
// positive cases above show these same words used as properties.
// @skjs-expect-error Identifier expected: 'if' is a reserved word that cannot be used here
export const if = 1;
