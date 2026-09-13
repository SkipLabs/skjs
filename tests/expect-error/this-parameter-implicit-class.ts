// Class methods without an explicit `this: T` still have an implicit this
// type (the enclosing class). Detaching them and calling without a receiver
// must be rejected, since the body references class fields via `this`.

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
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
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
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  g();
}

class OtherReceiver {
  text: string = "ok";
  m(x: number): void {
    const length = this.text.length;
  }
}

// Extracted methods must not borrow a different class's receiver contract.
function retypedMethod(source: C, other: OtherReceiver): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const method: typeof source.m = other.m;
  const carrier = { value: 1, m: method };
  carrier.m(0);
}

// Reattachment without an annotation must also validate the actual carrier.
function reattachedMethod(other: OtherReceiver): void {
  const carrier = { value: 1, m: other.m };
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  carrier.m(0);
}

function compatibleReattachment(other: OtherReceiver): void {
  const carrier = { text: "ok", m: other.m };
  carrier.m(0);
}

// Declaration-level typeof must preserve extraction requirements too.
type ExtractedCMethod = typeof c.m;
function reattachmentThroughTypeof(other: C): void {
  const method: ExtractedCMethod = other.m;
  const carrier = { m: method };
  // @skjs-expect-error The 'this' context is not assignable to method's 'this' type
  carrier.m(0);
}
