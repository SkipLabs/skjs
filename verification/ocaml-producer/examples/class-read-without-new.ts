// Calling a class without `new` throws; the class is read only by `new`.
class Flag {
  on: boolean = true;
}
export function leak(): null {
  const make = Flag;
  return null;
}
