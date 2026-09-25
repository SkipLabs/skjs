// A spread of a value copies its own enumerable properties, which the heap
// model does not tell from a class instance's prototype methods: refused.
function copy(o: { a: number }): { a: number } {
  return { ...o };
}
