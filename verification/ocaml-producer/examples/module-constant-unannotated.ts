// A function reads a module constant at its annotation; one with no
// annotation gives the function nothing to assume.
const on = true;
export function read(): boolean {
  return on;
}
