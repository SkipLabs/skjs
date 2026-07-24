// Circular type-parameter defaults and self-referential constraints
// (issues #886, #1000).
//
// A type parameter's default fills the parameter when a reference omits it.
// When the default names the alias it belongs to — with too few arguments to
// break the recursion — filling it would require the alias's own instantiation,
// the very one being computed: a cycle with no fixed point. Such a default
// denotes nothing, so the parameter resolves to `unknown`. `unknown` is sound:
// a value declared at the alias is caught the moment it is used at a concrete
// type, rather than laundered into it as the empty type would be. A cycle the
// analysis can see at the declaration is reported there and resolved; one that
// only emerges by running through a second alias's default, or through a
// self-referential constraint, surfaces as an excessively deep instantiation
// and is refused. Before this, every such reference either resolved to the
// empty type and laundered, or crashed the checker outright.
//
// The immediate positions inside a default are WIDER than inside a body: an
// array element, a tuple element, the operand of `keyof`, and the arguments of
// any reference — a class or interface included — all reach the alias here,
// though the same shapes are legal as an alias body (see circular-type-alias.ts).
// Only object members and function signatures defer.

/////////////////////////////////////////////////////////////////////////////
// A circular default is reported at its declaration and resolves to `unknown`.
/////////////////////////////////////////////////////////////////////////////

// Direct self-reference in the default.
// @skjs-expect-error Type parameter 'T' has a circular default
type SelfDefault<T = SelfDefault> = T;

// An array element of a default is immediate, unlike `type Arr = Arr[]`, a
// legal alias body.
// @skjs-expect-error Type parameter 'T' has a circular default
type ArrayDefault<T = ArrayDefault[]> = T;

// A tuple element likewise, unlike the legal body `type Tup = [Tup]`.
// @skjs-expect-error Type parameter 'T' has a circular default
type TupleDefault<T = [TupleDefault]> = T;

// A union member.
// @skjs-expect-error Type parameter 'T' has a circular default
type UnionDefault<T = UnionDefault | string> = T;

// The operand of `keyof`.
// @skjs-expect-error Type parameter 'T' has a circular default
type KeyofDefault<T = keyof KeyofDefault> = T;

// The arguments of an interface reference are immediate in a default, unlike
// `type ArrInst = Array<ArrInst>`, a legal alias body.
// @skjs-expect-error Type parameter 'T' has a circular default
type RefArgDefault<T = Array<RefArgDefault>> = T;

/////////////////////////////////////////////////////////////////////////////
// The alias resolves to `unknown`: a value cannot be drawn out of it.
/////////////////////////////////////////////////////////////////////////////

// Assigning a value *into* the alias is fine — everything is `unknown`.
function intoSelf(): SelfDefault {
  return 5;
}

declare const selfValue: SelfDefault;

// But the value cannot be used at a concrete type: `unknown` is not `string`.
function drainSelf(): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return selfValue;
}

// Nor cast out of, unlike the empty type, which would satisfy any cast.
function castSelf(): string {
  // @skjs-expect-error This 'as' cast is unsound: the source type is not assignable to the target type
  return selfValue as SelfDefault as string;
}

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
// Cycles that only close through a second alias's default are refused.
/////////////////////////////////////////////////////////////////////////////

// `MutualA`'s default is `MutualB`, whose default is `MutualA`: filling either
// requires the other. Neither default names its own alias, so the cycle is not
// visible at a single declaration and stays silent until a reference forces the
// defaults to be filled — `useMutual` below. The instantiation that closes the
// cycle is refused, reported at the alias it reaches back to. tsc instead
// reports a circular default at `MutualB`'s declaration; both are sound.
// @skjs-expect-error Type instantiation is excessively deep and possibly infinite
type MutualA<T = MutualB> = T;
type MutualB<X = MutualA> = X;

function useMutual(x: MutualA): void {}

// A longer cycle is refused the same way, reported at its entry alias.
// @skjs-expect-error Type instantiation is excessively deep and possibly infinite
type RingA<T = RingB> = T;
type RingB<T = RingC> = T;
type RingC<T = RingA> = T;

function useRing(x: RingA): void {}

/////////////////////////////////////////////////////////////////////////////
// A self-referential constraint is refused.
/////////////////////////////////////////////////////////////////////////////

// The constraint of `Fbound` names `Fbound` itself, so satisfying it requires
// instantiating the alias again — a check the analysis cannot discharge. Every
// instantiation is refused, including the well-typed `Fbound<string>`. tsc
// accepts `Fbound<string>`; SKJS refuses it — a sound over-refusal, not a wrong
// answer about a value.
// @skjs-expect-error Type instantiation is excessively deep and possibly infinite
type Fbound<T extends Fbound<string>> = T;

function useFbound(x: Fbound<string>): void {}

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
