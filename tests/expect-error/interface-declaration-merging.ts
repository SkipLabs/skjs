// Interface declaration merging: multiple `interface Foo` declarations with
// the same name merge their members, like tsc — within one file (below), and
// across files / against the import-stub interfaces (see
// tests/projects/interface-merging/).

// Same-file merging: members of both declarations are visible.
// @skjs-expect-error Duplicate class declaration 'SameFile'
interface SameFile {
  a(): string;
}
// @skjs-expect-error Duplicate class declaration 'SameFile'
// @skjs-expect-error Duplicate identifier 'SameFile'
interface SameFile {
  b(): number;
}
// @skjs-expect-error Duplicate class declaration 'SameFile'
function useSameFile(f: SameFile): void {
  // @skjs-expect-error Property 'a' does not exist on this type
  const s: string = f.a();
  const n: number = f.b();
}

// A re-declared member with the same type is fine.
// @skjs-expect-error Duplicate class declaration 'SameType'
interface SameType {
  x: string;
}
// @skjs-expect-error Duplicate class declaration 'SameType'
// @skjs-expect-error Duplicate identifier 'SameType'
interface SameType {
  x: string;
  y: number;
}
// @skjs-expect-error Duplicate class declaration 'SameType'
function useSameType(v: SameType): void {
  const s: string = v.x;
  // @skjs-expect-error Property 'y' does not exist on this type
  const n: number = v.y;
}

// Generic interfaces merge too, with the type parameters shared.
// @skjs-expect-error Duplicate class declaration 'Box'
interface Box<T> {
  value: T;
}
// @skjs-expect-error Duplicate class declaration 'Box'
// @skjs-expect-error Duplicate identifier 'Box'
interface Box<T> {
  wrap(x: T): Box<T>;
}
// @skjs-expect-error Duplicate class declaration 'Box'
function useBox(b: Box<number>): void {
  // @skjs-expect-error Property 'value' does not exist on this type
  const n: number = b.value;
  const w: Box<number> = b.wrap(1);
}

// A re-declared method accumulates as an overload in tsc. SKJS cannot
// represent overloads (a TFuns holds a single signature) and keeps the later
// declaration, which is sound: dropping an overload only rejects programs tsc
// accepts, never accepts one tsc rejects.
// @skjs-expect-error Duplicate class declaration 'Overloaded'
interface Overloaded {
  m(x: string): void;
}
// @skjs-expect-error Duplicate class declaration 'Overloaded'
// @skjs-expect-error Duplicate identifier 'Overloaded'
interface Overloaded {
  m(x: number): void;
}
// @skjs-expect-error Duplicate class declaration 'Overloaded'
function useOverloaded(o: Overloaded): void {
  o.m(1);
}

// An interface extending a merged interface inherits the union of all
// declarations' members.
// @skjs-expect-error Duplicate class declaration 'Base'
interface Base {
  x: string;
}
// @skjs-expect-error Duplicate class declaration 'Base'
interface Derived extends Base {
  y: number;
}
// @skjs-expect-error Duplicate class declaration 'Base'
// @skjs-expect-error Duplicate identifier 'Base'
interface Base {
  z: boolean;
}
function useDerived(d: Derived, b: Base): void {
  // @skjs-expect-error Property 'x' does not exist on this type
  const s: string = d.x;
  const n: number = d.y;
  const t: boolean = d.z;
  const u: boolean = b.z;
}

// tsc TS2717: a re-declared property must have the same type.
// @skjs-expect-error Duplicate class declaration 'Conflict'
interface Conflict {
  x: string;
}
// @skjs-expect-error Duplicate class declaration 'Conflict'
// @skjs-expect-error Duplicate identifier 'Conflict'
interface Conflict {
  x: number;
}

// tsc TS2717: a method and a property with the same name conflict.
// @skjs-expect-error Duplicate class declaration 'MethodVsProperty'
interface MethodVsProperty {
  m(): void;
}
// @skjs-expect-error Duplicate class declaration 'MethodVsProperty'
// @skjs-expect-error Duplicate identifier 'MethodVsProperty'
interface MethodVsProperty {
  m: number;
}

// tsc TS2687: re-declared members must have identical modifiers.
// @skjs-expect-error Duplicate class declaration 'Modifiers'
interface Modifiers {
  readonly x: string;
}
// @skjs-expect-error Duplicate class declaration 'Modifiers'
// @skjs-expect-error Duplicate identifier 'Modifiers'
interface Modifiers {
  x: string;
}

// tsc TS2374: an index signature may not be repeated across merged
// declarations, even with the same value type.
// @skjs-expect-error Duplicate class declaration 'IndexSig'
interface IndexSig {
  [k: string]: number;
}
// @skjs-expect-error Duplicate class declaration 'IndexSig'
// @skjs-expect-error Duplicate identifier 'IndexSig'
interface IndexSig {
  [k: string]: number;
}

// tsc TS2428: all declarations of a merged interface must declare identical
// type parameters (reported on each declaration).
// @skjs-expect-error Duplicate class declaration 'TParams'
interface TParams<T> {
  x: T;
}
// @skjs-expect-error Duplicate class declaration 'TParams'
// @skjs-expect-error Duplicate identifier 'TParams'
interface TParams<U> {}
// @skjs-expect-error Duplicate class declaration 'TParams'
function useTParams(v: TParams<number>): void {
  const n: number = v.x;
}
