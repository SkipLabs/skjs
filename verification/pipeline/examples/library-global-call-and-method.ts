// A global both called and read through a method in one module is a callable
// object with methods, which the graph has no clause for yet.
function both(key: string): symbol {
  const local: symbol = Symbol("local");
  return Symbol.for(key);
}
