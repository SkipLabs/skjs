// Interfaces are type-only: they have no value binding at runtime, so using
// an interface name as a value is rejected (tsc TS2693).

interface Local {
  a: number;
}

function newOnInterface(): Local {
  // @ts-expect-error 'Local' only refers to a type, but is being used as a value here
  return new Local();
}

function newOnInterfaceWithArgs(): Local {
  // @ts-expect-error 'Local' only refers to a type, but is being used as a value here
  // @skjs-expect-error This constructor expects no arguments
  return new Local(1);
}

function interfaceAsValue(): void {
  // @ts-expect-error 'Local' only refers to a type, but is being used as a value here
  const x = Local;
  const _y = x;
}

// @ts-expect-error 'Local' only refers to a type, but is being used as a value here
function typeofInterface(x: typeof Local): void {
  const _x = x;
}

class Dog {
  a: number = 1;
}

function instanceofInterface(x: Dog | Local): void {
  // @ts-expect-error 'Local' only refers to a type, but is being used as a value here
  if (x instanceof Local) {
    const _y = x;
  }
}

// Declaration merging: a value declaration with the same name provides the
// value binding, so value uses of the name are legal.
interface Merged {
  a: number;
}
declare const Merged: { new (x: number): Merged };

function newMerged(): Merged {
  return new Merged(1);
}

interface PropMerged {
  a: number;
}
declare const PropMerged: { x: number };

function mergedPropertyAccess(): number {
  return PropMerged.x;
}

function typeofMerged(v: typeof PropMerged): number {
  return v.x;
}

interface Unann {
  a: number;
}
declare const Unann = 3;

declare class UsesTypeofUnann {
  // FIXME: tsc accepts (Unann has a value binding); SKJS does not resolve an
  // unannotated const in this typeof position
  // @skjs-expect-error Cannot find name 'Unann'
  f: typeof Unann;
}

function readsUnannField(c: UsesTypeofUnann): number {
  return c.f;
}

// FIXME: tsc rejects with TS2689 "Cannot extend an interface 'Local'. Did you
// mean 'implements'?"; SKJS accepts extending an interface
class Sub extends Local {
  b: number = 2;
}

function newSub(): Sub {
  return new Sub();
}
