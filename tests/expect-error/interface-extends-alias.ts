// An interface may extend a type alias as long as the alias resolves to an
// object type (or an intersection of object types with statically known
// members). tsc accepts this; the alias's members are inherited as if the
// alias were intersected with the interface body. Resolving the heritage-clause
// name only against classes/interfaces would wrongly report "Cannot find name".

// Object-typed alias with an index signature: the named field and the index
// signature are both inherited.
type AliasBound = { readonly [k: string]: number };
interface ViaAlias extends AliasBound {
  readonly x: number;
}

function viaAliasMembers(v: ViaAlias): void {
  const _x: number = v.x;
  const _idx: number | undefined = v.anything;
}

// Intersection of object-typed aliases: every branch's members are inherited.
type A = { readonly a: number };
type B = { readonly b: string };
type AB = A & B;
interface ViaInter extends AB {
  readonly c: boolean;
}

function viaInterMembers(w: ViaInter): void {
  const _a: number = w.a;
  const _b: string = w.b;
  const _c: boolean = w.c;
}

// An alias that does not resolve to an object type cannot be extended (tsc
// TS2312): a union has no statically known member set, and a primitive is not
// an object.
type UnionAlias = { a: number } | { b: string };
// @skjs-expect-error An interface can only extend an object type or intersection of object types with statically known members.
interface ViaUnion extends UnionAlias {
  c: boolean;
}

type PrimAlias = string;
// @skjs-expect-error An interface can only extend an object type or intersection of object types with statically known members.
interface ViaPrim extends PrimAlias {
  c: boolean;
}

// A member redeclared incompatibly with the inherited one is rejected the same
// way as for an interface base (tsc TS2430).
type NumX = { readonly x: number };
// @skjs-expect-error This interface incorrectly extends its base type
interface BadOverride extends NumX {
  readonly x: string;
}

// A type alias is type-only, so a class cannot extend it as a value (tsc
// TS2693) — the name exists, so "Cannot find name" would be the wrong error.
type ClassBase = { readonly x: number };
// @skjs-expect-error 'ClassBase' only refers to a type, but is being used as a value here.
class ExtendsAlias extends ClassBase {
  y: number = 1;
}

// A generic interface propagates its own type parameter through the alias: the
// alias is normalized after the interface's type parameters are bound, so `T`
// resolves to the supplied argument.
type Wrap<T> = { readonly w: T };
interface IBox<T> extends Wrap<T> {
  readonly tag: string;
}

function genericPropagation(b: IBox<number>): void {
  const _w: number = b.w;
  const _t: string = b.tag;
}

// The alias may itself resolve to a nominal type (here a generic interface
// instantiation); its members are inherited by structure.
interface NominalBase<T> {
  readonly v: T;
}
type AliasOfNominal = NominalBase<number>;
interface ViaNominal extends AliasOfNominal {
  readonly k: string;
}

function viaNominalMembers(i: ViaNominal): void {
  const _v: number = i.v;
  const _k: string = i.k;
}

// An empty-object alias contributes no members.
type Empty = {};
interface ViaEmpty extends Empty {
  readonly e: number;
}

function viaEmptyMembers(i: ViaEmpty): void {
  const _e: number = i.e;
}

// A call/construct signature on the aliased base cannot flow through the
// field-accumulation maps, so it is reported as unsupported rather than
// silently dropped (tsc would accept and inherit the signature). The base-
// compatibility check is skipped for such a base, so this is the only error.
type Callable = { (): number; readonly prop: string };
// @skjs-expect-error extending a type alias that has a call or construct signature is not supported by SKJS (ignored)
interface ViaCallable extends Callable {
  readonly extra: boolean;
}

// A type alias that cycles back through the extending interface terminates with
// an error rather than recursing forever (the alias path is outside the class-
// cycle guard, so this pins that expansion's own cycle handling).
type AliasCycle = ICycle;
// @skjs-expect-error An interface can only extend an object type or intersection of object types with statically known members.
interface ICycle extends AliasCycle {
  readonly x: number;
}
