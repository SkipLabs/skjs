// Writing a writable optional field adds the key where the object was
// allocated without it, which the model's objects, their keys fixed at
// allocation, cannot state.
type WithOptional = { opt?: number };
export function set(x: WithOptional): void {
  x.opt = 3;
}
