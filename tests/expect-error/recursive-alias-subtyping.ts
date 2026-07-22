// Structural subtyping of a growing recursive alias terminates (issue #997).
//
// Comparing two instances of a recursive alias whose type arguments grow at
// each level — `MA<string>` against `MB<string>`, descending through
// `MA<MB<string>>` and on — never repeats a pair, so the co-inductive cache
// that stops an ordinary cycle never fires, and the descent branches at every
// level. It used to run until it exhausted the stack, then, once bounded on one
// path, the heap. A path is now assumed related past a shallow depth, the way
// tsc treats a deeply nested type: the finite obligations at each level are
// checked first, so a real mismatch is still caught, and only the growing
// recursive part is assumed.

type MutualA<T> = { v: MutualA<MutualB<T>>; w: T };
type MutualB<T> = { v: MutualB<MutualA<T>>; w: T };

// The two instances are structurally equal, so the assignment is accepted, as
// it is by tsc. Before the bound, checking it never terminated.
function acceptMutual(x: MutualA<string>): MutualB<string> {
  return x;
}

// The `w` field differs at the first level, so the mismatch is caught before
// the depth bound assumes anything — the recursive part being assumed related
// never masks a shallow difference.
function rejectMutual(x: MutualA<number>): MutualB<string> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// The difference is behind an invariant field (a setter), reached at the first
// level, so it too is caught rather than assumed away.
type InvA<T> = { v: InvA<Wrapped<T>>; set: (x: T) => void };
type Wrapped<T> = { inner: T };

function rejectInvariant(x: InvA<string>): InvA<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}
