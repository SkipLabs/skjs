// A class declared in a .ts file is nominal (skjs-rules.md rule 35): only its
// instances inhabit it, so they are provably neither arrays nor callable and
// both branches narrow to never.
export class Local {
  a: number = 0;
}

export function localNotArray(c: Local): string {
  if (Array.isArray(c)) {
    const n: never = c;
    return n;
  }
  return "";
}

export function localNotCallable(c: Local): string {
  if (typeof c === "function") {
    const n: never = c;
    return n;
  }
  return "";
}
