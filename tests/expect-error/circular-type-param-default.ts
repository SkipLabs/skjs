// Circular type-parameter defaults and self-referential constraints
// (issues #886, #1000).
//
// A type parameter's default fills the parameter when a reference omits it.
// When the default names the alias it belongs to — with too few arguments to
// break the recursion — filling it would require the alias's own instantiation,
// the very one being computed: a cycle with no fixed point. An explicit
// argument breaks it: `type A<T = A<string>>` is well-founded.
//
// The immediate positions inside a default are WIDER than inside a body: an
// array element, a tuple element, the operand of `keyof`, and the arguments of
// any reference — a class or interface included — all reach the alias here,
// though the same shapes are legal as an alias body (see circular-type-alias.ts).
// Only object members and function signatures defer.
//
// This file pins the current handling of these aliases; the reporting,
// resolution, and refusal they now receive are added by the fixes for #886 and
// #1000.

/////////////////////////////////////////////////////////////////////////////
// A default that reaches its own alias through an immediate position.
/////////////////////////////////////////////////////////////////////////////

// Direct self-reference in the default.
type SelfDefault<T = SelfDefault> = T;

// An array element of a default is immediate, unlike `type Arr = Arr[]`, a
// legal alias body.
type ArrayDefault<T = ArrayDefault[]> = T;

// A tuple element likewise, unlike the legal body `type Tup = [Tup]`.
type TupleDefault<T = [TupleDefault]> = T;

// A union member.
type UnionDefault<T = UnionDefault | string> = T;

// The operand of `keyof`.
type KeyofDefault<T = keyof KeyofDefault> = T;

// The arguments of an interface reference are immediate in a default, unlike
// `type ArrInst = Array<ArrInst>`, a legal alias body.
type RefArgDefault<T = Array<RefArgDefault>> = T;

/////////////////////////////////////////////////////////////////////////////
// A default that supplies enough arguments is well-founded, not circular.
/////////////////////////////////////////////////////////////////////////////

// A self-reference that supplies every argument needs no default-filling:
// `FullArgs<string>` is `string`, so `FullArgs` (no arguments) is just `string`.
type FullArgs<T = FullArgs<string>> = T;

function useFullArgs(x: FullArgs): string {
  return x;
}

// The same holds when the parameter carries a constraint the argument
// satisfies: filling `Constrained<string>` binds `T` to `string` and stops.
type Constrained<T extends string = Constrained<string>> = T;

function useConstrained(x: Constrained): string {
  return x;
}

// An object member of a default defers, so this names the alias without
// requiring it.
type ObjectMemberDefault<T = { x: ObjectMemberDefault }> = T;

// A function signature defers likewise.
type FnDefault<T = () => FnDefault> = T;

/////////////////////////////////////////////////////////////////////////////
// Cycles that only close through a second alias's default.
/////////////////////////////////////////////////////////////////////////////

// `MutualA`'s default is `MutualB`, whose default is `MutualA`: filling either
// requires the other. Neither default names its own alias, so the cycle is not
// visible at a single declaration.
type MutualA<T = MutualB> = T;
type MutualB<X = MutualA> = X;

// A longer cycle through three aliases.
type RingA<T = RingB> = T;
type RingB<T = RingC> = T;
type RingC<T = RingA> = T;

/////////////////////////////////////////////////////////////////////////////
// Ordinary type-parameter defaults and constraints are unaffected.
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

// A default that names an earlier parameter, not the alias, is well-founded.
type Pair<A, B = A> = [A, B];

function usePair(x: Pair<string>): [string, string] {
  return x;
}

// Recursion through a deferred position (an object member) is legal, with or
// without a default in play.
type List<T> = null | { head: T; tail: List<T> };

function useList(x: List<string>): List<string> {
  return x;
}
