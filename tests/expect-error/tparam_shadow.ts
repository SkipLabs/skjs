// Regression test for #606: a method-local type parameter whose name
// matches one of the containing class's type parameters must not be
// captured by the class tparam binding during instantiation.

declare interface Base<T> {
  map<U>(f: (item: T) => U): Base<U>;
}

declare interface Child<A, B, U> extends Base<A | B | U> {
  readonly a: A;
  readonly b: B;
  readonly u: U;
}

// The inherited `map<U>` is alpha-equivalent to the rename below, so the
// subtype check must succeed.
function acrossInheritance(
  t: Child<1, "x", true>,
): Child<number, string, boolean> {
  // @skjs-expect-error Invalid return type
  return t;
}

// Rename control: replacing the method tparam name `U` with `V` avoids
// the collision. Must pass both before and after the fix.
declare interface BaseRenamed<T> {
  map<V>(f: (item: T) => V): BaseRenamed<V>;
}

declare interface ChildRenamed<A, B, U> extends BaseRenamed<A | B | U> {
  readonly a: A;
  readonly b: B;
  readonly u: U;
}

function acrossInheritanceRenamed(
  t: ChildRenamed<1, "x", true>,
): ChildRenamed<number, string, boolean> {
  return t;
}

// Direct shadowing without inheritance: the method-local `U` reuses the
// interface's tparam name. Identity on `U` must remain polymorphic.
declare interface Direct<U> {
  m<U>(x: U): U;
}

function directShadow(c: Direct<string>): Direct<number> {
  // @skjs-expect-error Invalid return type
  return c;
}
