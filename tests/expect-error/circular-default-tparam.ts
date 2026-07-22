// Circular type-parameter defaults (issue #886).
//
// A type parameter default with no explicit argument for one of the alias's own
// parameters falls back to that parameter's default, so `type A<T = A>` needs
// A's default to compute A's default — a cycle, and the alias denotes nothing.
// An explicit argument breaks it: `type A<T = A<string>>` is well-founded.
//
// The immediate positions inside a default are WIDER than inside a body: an
// array element, a tuple element, and the arguments of any reference — a class
// or interface included — are all immediate here, so the shapes below are
// circular even though the same shapes are legal as an alias body (see
// circular-type-alias.ts). Only object members and function signatures defer.
//
// These are all declared but never used: a use of any of them still crashes the
// checker (unbounded default-filling), which is filed separately.

// Direct self-reference in the default.
type SelfDefault<T = SelfDefault> = T;

// An array element of a default is immediate, unlike `type Arr = Arr[]`, which
// is a legal alias body.
type ArrayDefault<T = ArrayDefault[]> = T;

// A tuple element likewise, unlike the legal body `type Tup = [Tup]`.
type TupleDefault<T = [TupleDefault]> = T;

// A union member.
type UnionDefault<T = UnionDefault | string> = T;

// The operand of `keyof`.
type KeyofDefault<T = keyof KeyofDefault> = T;

// The arguments of an interface reference are immediate in a default, unlike
// `type ArrInst = Array<ArrInst>`, which is a legal alias body.
type RefArgDefault<T = Array<RefArgDefault>> = T;

// A cycle that runs through a second alias's default rather than back to this
// one directly is not reported yet (a documented gap); tsc reports it.
type MutualDefaultA<T = MutualDefaultB> = T;
type MutualDefaultB<X = MutualDefaultA> = X;

/////////////////////////////////////////////////////////////////////////////
// Legal: a well-founded default is not circular.
/////////////////////////////////////////////////////////////////////////////

// A self-reference that supplies every argument needs no default-filling.
type FullArgs<T = FullArgs<string>> = T;

// An object member of a default defers, so this names the alias without
// requiring it.
type ObjectMemberDefault<T = { x: ObjectMemberDefault }> = T;

// A function signature defers likewise.
type FnDefault<T = () => FnDefault> = T;

// A default that references an earlier type parameter, not the alias.
type PrevParam<A, B = A> = [A, B];

// A circular *constraint* is legal in tsc and is not a circular default — the
// constraint is checked, not filled. It is left out of this file because it
// crashes the checker even without a use (a pre-existing non-termination,
// filed separately): `type C<T extends C<string>> = T`. This check must not
// report it, since it inspects only defaults.
