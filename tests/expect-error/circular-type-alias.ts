// Circular type aliases (issue #874).
//
// A type alias whose own definition requires resolving itself denotes
// nothing. A reference is *immediate* when computing the alias's type forces
// the referenced type to be computed too: the body itself, either side of a
// union or intersection, the operand of `keyof`, and the type arguments of a
// reference to another alias (instantiating an alias substitutes its
// arguments eagerly). Every other position is *deferred* — an object member,
// array element, tuple element, or function parameter/return names the alias
// without resolving it — which is what keeps the recursive shapes at the
// bottom of this file legal.

// Direct self-reference.
// @skjs-expect-error Type alias 'R' circularly references itself
type R = R;

// Mutual recursion through bare references.
// @skjs-expect-error Type alias 'A' circularly references itself
type A = B;
// @skjs-expect-error Type alias 'B' circularly references itself
type B = A;

// Union and intersection members are immediate.
// @skjs-expect-error Type alias 'U' circularly references itself
type U = U | string;
// @skjs-expect-error Type alias 'I' circularly references itself
type I = I & { a: string };

// `keyof` forces its operand to resolve.
// @skjs-expect-error Type alias 'K' circularly references itself
type K = keyof K;

// Every edge of this cycle is a bare union member, so all three are circular.
// @skjs-expect-error Type alias 'C1' circularly references itself
type C1 = C2 | string;
// @skjs-expect-error Type alias 'C2' circularly references itself
type C2 = C3 | string;
// @skjs-expect-error Type alias 'C3' circularly references itself
type C3 = C1 | string;

// A cycle that does not pass through the alias under test does not make it
// circular: resolving `X` reaches the circular `Y`, but `X` is not itself on
// the cycle. tsc reports `Y` and `Z` here and leaves `X` alone.
type X = Y;
// @skjs-expect-error Type alias 'Y' circularly references itself
type Y = Z;
// @skjs-expect-error Type alias 'Z' circularly references itself
type Z = Y;

// The type arguments of an alias reference are immediate even when the alias
// ignores them, because instantiating an alias resolves its arguments first.
type Ignore<T> = number;
// @skjs-expect-error Type alias 'ArgCycle' circularly references itself
type ArgCycle = Ignore<ArgCycle>;

// The alias is reported once at its declaration; uses of it are not reported
// again. tsc accepts this too — a circular alias resolves to an error type
// there, so it satisfies any annotation just as the empty type does here.
function useR(x: R): number {
  return x;
}

/////////////////////////////////////////////////////////////////////////////
// Legal recursion: every cycle below passes through a deferred position.
/////////////////////////////////////////////////////////////////////////////

// An array element is deferred.
type Arr = Arr[];

// An object member is deferred.
type Obj = { next: Obj };

// A function return is deferred.
type Fn = () => Fn;

// A tuple element is deferred.
type Tup = [Tup];

// The type arguments of an *interface* reference are deferred, unlike those
// of an alias reference, so a self-reference under `Array` stays legal.
type ArrInst = Array<ArrInst>;

// `Box<Deferred>` sits behind an object member, so resolving `Deferred` never
// reaches the argument.
type Box<T> = { v: T };
type Deferred = { next: Box<Deferred> };

// `keyof` resolves its operand, but not the operand's members, so the object
// below defers and this names `KeyOfObj` without requiring it.
type KeyOfObj = keyof { a: KeyOfObj };

// A type parameter hides an alias of the same name: the body of `Shadowed` is
// its own parameter, not the alias `Target`. `Target` is just `string`.
type Target = Shadowed<string>;
type Shadowed<Target> = Target;

// A name declared as both an interface and an alias is a duplicate identifier,
// and the reference resolves to the first declaration — the interface — just
// as it does everywhere else. The body of `Dup` is therefore that interface, a
// deferred reference, so the alias is not circular on top of being a
// duplicate.
interface Dup {
  a: string;
}
// @skjs-expect-error Duplicate identifier 'Dup'
type Dup = Dup;

// The recursion runs through the object member, not the union itself.
type List<T> = null | { head: T; tail: List<T> };

function useList(x: List<number>): null | { head: number; tail: List<number> } {
  return x;
}
