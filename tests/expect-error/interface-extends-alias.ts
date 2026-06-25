// An interface may extend a type alias as long as the alias resolves to an
// object type (or an intersection of object types with statically known
// members). tsc accepts this; the alias's members are inherited as if the
// alias were intersected with the interface body.
//
// skjs currently resolves the heritage-clause name only against classes and
// interfaces, so every `extends <alias>` below is wrongly rejected with
// "Cannot find name" — even the cases tsc accepts. A plain annotation use of
// the same alias works fine; only the heritage clause is broken.

// Object-typed alias with an index signature.
type AliasBound = { readonly [k: string]: number };
// @skjs-expect-error Cannot find name 'AliasBound'
interface ViaAlias extends AliasBound {
  readonly x: number;
}

function viaAliasMembers(v: ViaAlias): void {
  const _x: number = v.x;
}

// Intersection of object-typed aliases.
type A = { readonly a: number };
type B = { readonly b: string };
type AB = A & B;
// @skjs-expect-error Cannot find name 'AB'
interface ViaInter extends AB {
  readonly c: boolean;
}

function viaInterMembers(w: ViaInter): void {
  const _c: boolean = w.c;
}

// A union alias has no statically known member set (tsc rejects with TS2312),
// but skjs cannot even resolve the name in the heritage clause.
type UnionAlias = { a: number } | { b: string };
// @skjs-expect-error Cannot find name 'UnionAlias'
interface ViaUnion extends UnionAlias {
  c: boolean;
}

// A primitive alias is not an object (tsc TS2312).
type PrimAlias = string;
// @skjs-expect-error Cannot find name 'PrimAlias'
interface ViaPrim extends PrimAlias {
  c: boolean;
}

// An incompatible member override (tsc TS2430).
type NumX = { readonly x: number };
// @skjs-expect-error Cannot find name 'NumX'
interface BadOverride extends NumX {
  readonly x: string;
}

// A type alias is type-only, so a class extending it uses a type as a value
// (tsc TS2693).
type ClassBase = { readonly x: number };
// @skjs-expect-error Cannot find name 'ClassBase'
class ExtendsAlias extends ClassBase {
  y: number = 1;
}

// A generic interface propagates its own type parameter through the alias: the
// alias is normalized after the interface's type parameters are bound, so `T`
// resolves to the supplied argument.
type Wrap<T> = { readonly w: T };
// @skjs-expect-error Cannot find name 'Wrap'
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
// @skjs-expect-error Cannot find name 'AliasOfNominal'
interface ViaNominal extends AliasOfNominal {
  readonly k: string;
}

function viaNominalMembers(i: ViaNominal): void {
  const _v: number = i.v;
  const _k: string = i.k;
}

// An empty-object alias contributes no members.
type Empty = {};
// @skjs-expect-error Cannot find name 'Empty'
interface ViaEmpty extends Empty {
  readonly e: number;
}

function viaEmptyMembers(i: ViaEmpty): void {
  const _e: number = i.e;
}

// A call/construct signature on the aliased base cannot flow through the
// field-accumulation maps, so it is reported as unsupported rather than
// silently dropped (tsc would accept and inherit the signature). Because the
// merge omits the call signature, the base-compatibility check then also fails
// spuriously — a second, redundant error on the same clause.
type Callable = { (): number; readonly prop: string };
// @skjs-expect-error Cannot find name 'Callable'
interface ViaCallable extends Callable {
  readonly extra: boolean;
}

// A type alias that cycles back through the extending interface terminates with
// an error rather than recursing forever (the alias path is outside the class-
// cycle guard, so this pins that expansion's own cycle handling).
type AliasCycle = ICycle;
// @skjs-expect-error Cannot find name 'AliasCycle'
interface ICycle extends AliasCycle {
  readonly x: number;
}
