// A computed key in an object literal: an allocation's keys are the names
// the literal spells, and a symbol is none of them.
const key: unique symbol = Symbol();
export function make(): object {
  return { [key]: 1 };
}
