// Filling a circular type-parameter default terminates (issue #1000).
//
// A reference to a generic alias with a missing argument fills that argument
// from the parameter's default. When the default leads back to an alias whose
// argument is again missing, filling it needs filling it — a cycle. Until it
// was cut, resolving one of these never terminated and the checker crashed.
//
// A cut default resolves to `unknown`, so nothing is lost soundly: the alias
// denotes nothing, and `unknown` keeps a value out of it rather than letting
// one through as the empty type would. tsc reports these as circular defaults
// (TS2716); SKJS reports a default that reaches its own alias directly, but not
// one that runs through another alias's default, so the mutual cycles below are
// accepted rather than reported — the point here is only that they terminate.

// Two aliases, each defaulting to the other. Using one fills its default from
// the other, which fills its default from the first.
type MutualA<T = MutualB> = T;
type MutualB<X = MutualA> = X;

function useMutual(x: MutualA): void {}

// A longer default cycle through three aliases.
type RingA<T = RingB> = T;
type RingB<T = RingC> = T;
type RingC<T = RingA> = T;

function useRing(x: RingA): void {}

/////////////////////////////////////////////////////////////////////////////
// Legal: a well-founded default still resolves and is still checked.
/////////////////////////////////////////////////////////////////////////////

// A plain default is filled and used normally.
type Optional<T = string> = T | null;

function useOptional(x: Optional): string | null {
  return x;
}

// A constraint on a well-founded default is still enforced: `number` does not
// satisfy `string`.
type Bounded<T extends string = string> = T;
// @skjs-expect-error Type argument does not satisfy the constraint
type BadBound = Bounded<number>;
