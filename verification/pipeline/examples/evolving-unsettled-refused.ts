// Each cell consed onto `result` holds the one before it: the union of what
// is written into it grows with every step, and no evolved type settles.
type List = null | { head: number; tail: List };
export function build(n: number): List {
  let result = null;
  for (let i = 0; i !== n; i++) {
    result = { head: i, tail: result };
  }
  return result;
}
