// Class methods without an explicit `this: T` still have an implicit this
// type (the enclosing class). Detaching them and calling without a receiver
// must be rejected, since the body references class fields via `this`.
//
// Staged: until implicit class `this` lands, the detached-call rejections are
// documented with // TODO: markers and become live error assertions later.

class C {
  value: number = 1;
  m(x: number): void {
    let _ = this.value;
  }
}

declare const c: C;

function callOk(): void {
  c.m(1);
}

function detachedCall(): void {
  const g = c.m;
  // TODO: reject — `g(1)` uses this: void, not this: C.
  g(1);
}

// Inherited methods also carry the parent class as their implicit this.
class Base {
  tag: string = "base";
  greet(): void {
    let _ = this.tag;
  }
}
class Derived extends Base {}

declare const d: Derived;

function derivedCallOk(): void {
  d.greet();
}

function derivedDetached(): void {
  const g = d.greet;
  // TODO: reject — detached inherited method uses this: void, not this: Base.
  g();
}
