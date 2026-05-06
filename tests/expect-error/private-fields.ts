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

class NarrowsToPrivate extends PublicParent {
  // @skjs-expect-error Property 'x' must have the same access modifier as in the parent class
  private x: number = 2;
}

class PrivateParent {
  private y: number = 1;
}

class WidensToPublic extends PrivateParent {
  // @skjs-expect-error Property 'y' must have the same access modifier as in the parent class
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
