// Structural subtyping of a growing recursive alias (issue #997).
//
// Comparing two instances of a recursive alias whose type arguments grow at
// each level — `MutualA<string>` against `MutualB<string>`, descending through
// `MutualA<MutualB<string>>` and on — never repeats a pair, so the co-inductive
// `seenSub` cache that stops an ordinary cycle never fires, and the descent
// branches at every level. It used to run until it exhausted the stack, then
// the heap. It now revisits the same pair of type constructors only a bounded
// number of times before the recursion is refused as excessively deep — a
// conservative rejection, rather than assuming the pair related, which would let
// an unsound program through.

// @skjs-expect-error Type instantiation is excessively deep and possibly infinite
type MutualA<T> = { v: MutualA<MutualB<T>>; w: T };
type MutualB<T> = { v: MutualB<MutualA<T>>; w: T };

function useMutual(x: MutualA<string>): MutualB<string> {
  return x;
}

/////////////////////////////////////////////////////////////////////////////
// A finite recursion is left alone: it reaches any constructor pair only a few
// times, and the co-inductive cache stops it at the repeated pair.
/////////////////////////////////////////////////////////////////////////////

type List<T> = null | { head: T; tail: List<T> };

function acceptList(x: List<string>): List<string> {
  return x;
}

// A real difference is still reported, not swallowed by the bound.
function rejectList(x: List<string>): List<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}
