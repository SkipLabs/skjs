// The well-known symbols of the global `Symbol`, read at `symbol` through the
// reviewed overlay: which symbol each is, is not read.
function wellKnown(): symbol[] {
  const iterator: symbol = Symbol.iterator;
  return [
    iterator,
    Symbol.asyncIterator,
    Symbol.hasInstance,
    Symbol.toPrimitive,
    Symbol.toStringTag,
  ];
}
