// An object's keys are fixed where it is allocated: a write adding one is
// refused by name (SKJS grows a local `{}`; TypeScript refuses it too).
export function grow(): { x: number } {
  let obj = {};
  obj.x = 5;
  return obj;
}
