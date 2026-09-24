// A generic class's method has its instance as receiver: a generic
// application, whose method rows are not yet derived.
import { Keeper } from "@fixture/lib";
export function keep(flag: boolean): boolean {
  return new Keeper<boolean>(flag).get();
}
