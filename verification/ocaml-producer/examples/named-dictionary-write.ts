// A write at a key a dictionary may lack adds it, and an object's keys are
// fixed at its allocation.
export function add(d: { [k: string]: number }): void {
  d["fresh"] = 1;
}
