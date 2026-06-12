// Interfaces are type-only: they have no value binding at runtime, so using
// an interface name as a value is rejected by tsc with TS2693 "'X' only
// refers to a type, but is being used as a value here".

interface Local {
  a: number;
}

function newOnInterface(): Local {
  // FIXME: tsc rejects with TS2693; SKJS synthesizes a no-arg constructor (issue #684)
  return new Local();
}

function newOnInterfaceWithArgs(): Local {
  // FIXME: tsc rejects with TS2693; SKJS reports the synthesized no-arg constructor instead (issue #684)
  // @skjs-expect-error This constructor expects no arguments
  return new Local(1);
}

function interfaceAsValue(): void {
  // FIXME: tsc rejects with TS2693; SKJS resolves the interface name to a value (issue #684)
  const x = Local;
  const _y = x;
}

// FIXME: tsc rejects with TS2693; SKJS accepts typeof on an interface name (issue #684)
function typeofInterface(x: typeof Local): void {
  const _x = x;
}

class Dog {
  a: number = 1;
}

function instanceofInterface(x: Dog | Local): void {
  // FIXME: tsc rejects with TS2693; SKJS accepts instanceof on an interface name (issue #684)
  if (x instanceof Local) {
    const _y = x;
  }
}

// Declaration merging: a value declaration with the same name provides the
// value binding, so value uses of the name are legal in tsc.
interface Merged {
  a: number;
}
declare const Merged: { new (x: number): Merged };

function newMerged(): Merged {
  // FIXME: tsc accepts (the const Merged provides a construct signature); SKJS resolves `new` through the interface instead (issue #684)
  // @skjs-expect-error This constructor expects no arguments
  return new Merged(1);
}

interface PropMerged {
  a: number;
}
declare const PropMerged: { x: number };

function mergedPropertyAccess(): number {
  // FIXME: tsc accepts (the const PropMerged provides the value); SKJS resolves the name to the interface instead (issue #684)
  // @skjs-expect-error Property 'x' does not exist on this type
  return PropMerged.x;
}

function typeofMerged(v: typeof PropMerged): number {
  // FIXME: tsc accepts (typeof PropMerged is the const's type); SKJS resolves the name to the interface instead (issue #684)
  // @skjs-expect-error Property 'x' does not exist on this type
  return v.x;
}

interface Unann {
  a: number;
}
declare const Unann = 3;

declare class UsesTypeofUnann {
  f: typeof Unann;
}

function readsUnannField(c: UsesTypeofUnann): number {
  // FIXME: tsc accepts (typeof Unann is the const's literal type 3); SKJS resolves the name to the interface instead (issue #684)
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return c.f;
}

// FIXME: tsc rejects with TS2689 "Cannot extend an interface 'Local'. Did you
// mean 'implements'?"; SKJS accepts extending an interface (issue #684)
class Sub extends Local {
  b: number = 2;
}

function newSub(): Sub {
  return new Sub();
}
