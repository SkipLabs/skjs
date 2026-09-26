// A spread of a function copies whatever was assigned to it, which its type
// does not bound: refused by that reason.
export function copy(f: () => number): object {
  return { ...f };
}
