// Interface declaration merging: multiple `interface Foo` declarations with
// the same name merge their members, like tsc — within one file (below), and
// across files / against the import-stub interfaces (see
// tests/projects/interface-merging/).

// Same-file merging: members of both declarations are visible.
interface SameFile {
  a(): string;
}
interface SameFile {
  b(): number;
}
function useSameFile(f: SameFile): void {
  const s: string = f.a();
  const n: number = f.b();
}

// A re-declared member with the same type is fine.
interface SameType {
  x: string;
}
interface SameType {
  x: string;
  y: number;
}
function useSameType(v: SameType): void {
  const s: string = v.x;
  const n: number = v.y;
}

// Generic interfaces merge too, with the type parameters shared.
interface Box<T> {
  value: T;
}
interface Box<T> {
  wrap(x: T): Box<T>;
}
function useBox(b: Box<number>): void {
  const n: number = b.value;
  const w: Box<number> = b.wrap(1);
}

// A re-declared method accumulates as an overload in tsc. SKJS cannot
// represent overloads (a TFuns holds a single signature) and keeps the later
// declaration, which is sound: dropping an overload only rejects programs tsc
// accepts, never accepts one tsc rejects.
interface Overloaded {
  m(x: string): void;
}
interface Overloaded {
  m(x: number): void;
}
function useOverloaded(o: Overloaded): void {
  o.m(1);
}

// An interface extending a merged interface inherits the union of all
// declarations' members.
interface Base {
  x: string;
}
interface Derived extends Base {
  y: number;
}
interface Base {
  z: boolean;
}
function useDerived(d: Derived, b: Base): void {
  const s: string = d.x;
  const n: number = d.y;
  const t: boolean = d.z;
  const u: boolean = b.z;
}

// tsc TS2717: a re-declared property must have the same type.
interface Conflict {
  x: string;
}
interface Conflict {
  // @ts-expect-error Subsequent property declarations must have the same type. Property 'x' must be of type 'string', but here has type 'number'.
  x: number;
}

// tsc TS2717: a method and a property with the same name conflict.
interface MethodVsProperty {
  m(): void;
}
interface MethodVsProperty {
  // @ts-expect-error Subsequent property declarations must have the same type. Property 'm' must be of type '(this: MethodVsProperty) => void', but here has type 'number'.
  m: number;
}

// tsc TS2687: re-declared members must have identical modifiers.
interface Modifiers {
  readonly x: string;
}
interface Modifiers {
  // @ts-expect-error All declarations of 'x' must have identical modifiers.
  x: string;
}

// tsc TS2687 also covers the access modifier: a 'private' member re-declared
// without it must not silently become public in the merged interface.
interface Access {
  private x: number;
}
interface Access {
  // @skjs-expect-error All declarations of 'x' must have identical modifiers.
  x: number;
}

// tsc TS2374: an index signature may not be repeated across merged
// declarations, even with the same value type.
interface IndexSig {
  [k: string]: number;
}
interface IndexSig {
  // @ts-expect-error Duplicate index signature for type 'string'.
  [k: string]: number;
}

// tsc TS2428: all declarations of a merged interface must declare identical
// type parameters (reported on each declaration).
// @ts-expect-error All declarations of 'TParams' must have identical type parameters.
interface TParams<T> {
  x: T;
}
// @ts-expect-error All declarations of 'TParams' must have identical type parameters.
interface TParams<U> {}
function useTParams(v: TParams<number>): void {
  const n: number = v.x;
}
