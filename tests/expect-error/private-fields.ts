// Tests for private class field access enforcement.
// `protected` is silently accepted but treated as `public` — SKJS does
// not enforce subclass-only visibility.

class WithPrivate {
  private px: number = 1;

  inSameClass(): number {
    return this.px;
  }
}

class TwoInstancesOfSameClass {
  private px: number = 0;

  copyFrom(other: TwoInstancesOfSameClass): number {
    return other.px;
  }
}

// `protected` accepted but not enforced; reachable like `public`.
class WithProtectedTreatedAsPublic {
  protected pp: number = 2;
}

function readProtectedFromOutside(c: WithProtectedTreatedAsPublic): number {
  return c.pp;
}

function readPrivateFromOutside(c: WithPrivate): number {
  // @skjs-expect-error Property 'px' is private and only accessible within class 'WithPrivate'
  return c.px;
}

class WithParentPrivate extends WithPrivate {
  readParentPrivate(): number {
    // @skjs-expect-error Property 'px' is private and only accessible within class 'WithPrivate'
    return this.px;
  }
}

class WriteToPrivate {
  private px: number = 0;
  bumpSelf(): void {
    this.px = this.px + 1;
  }
}

function writeToPrivateFromOutside(c: WriteToPrivate): void {
  // @skjs-expect-error Property 'px' is private and only accessible within class 'WriteToPrivate'
  c.px = 5;
}

class WithPrivateMethod {
  private helper(): number {
    return 42;
  }

  exposed(): number {
    return this.helper();
  }
}

function callPrivateMethodFromOutside(w: WithPrivateMethod): number {
  // @skjs-expect-error Property 'helper' is private and only accessible within class 'WithPrivateMethod'
  return w.helper();
}

class PublicParent {
  x: number = 1;
}

// @skjs-expect-error Invalid extension
class NarrowsToPrivate extends PublicParent {
  private x: number = 2;
}

class PrivateParent {
  private y: number = 1;
}

// @skjs-expect-error Invalid extension
class WidensToPublic extends PrivateParent {
  y: number = 2;
}

class HasPrivateForInTest {
  private px?: number;
}

function inDoesNotLaunderPrivate(c: HasPrivateForInTest): void {
  if ("px" in c) {
    // @skjs-expect-error Property 'px' is private and only accessible within class 'HasPrivateForInTest'
    const _ = c.px;
  }
}

class UnionPrivateA {
  private z: number = 1;
}

class UnionPublicB {
  z: number = 2;
}

function readUnionPrivatePublic(o: UnionPrivateA | UnionPublicB): number {
  // @skjs-expect-error Property 'z' is private and only accessible within class 'UnionPrivateA'
  return o.z;
}

class UnionPrivateC {
  private w: number = 1;
}

class UnionPrivateD {
  private w: number = 2;
}

function readUnionTwoPrivates(o: UnionPrivateC | UnionPrivateD): number {
  // @skjs-expect-error Property 'w' has incompatible private declarations across the union and is not accessible
  return o.w;
}

class StructLeak {
  private q: number = 1;
}

function structuralLaunder(c: StructLeak): { q: number } {
  // @skjs-expect-error Invalid return type
  return c;
}

function genericLaunder<T extends { q: number }>(t: T): number {
  return t.q;
}

function callGeneric(c: StructLeak): number {
  // @skjs-expect-error Invalid call
  return genericLaunder(c);
}

class HasPrivateForSpread {
  private spx: number = 1;
  pub: number = 2;
}

function spreadFromOutside(c: HasPrivateForSpread): {
  spx: number;
  pub: number;
} {
  // @skjs-expect-error Cannot spread an object with non-public field 'spx'
  return { ...c };
}

class SpreadFromInsideTest {
  private spx: number = 1;

  copy(): { spx: number } {
    // @skjs-expect-error Cannot spread an object with non-public field 'spx'
    return { ...this };
  }
}
