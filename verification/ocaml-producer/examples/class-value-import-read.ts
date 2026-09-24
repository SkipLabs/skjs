// An imported class, like a local one, is read only by `new`.
import { Counter } from "@fixture/lib";
export function leak(): null {
  const make = Counter;
  return null;
}
