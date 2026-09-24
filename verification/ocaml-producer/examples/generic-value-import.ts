// A generic imported function needs its scheme at the call.
import { generic } from "@fixture/lib";
export function use(x: number): number {
  return generic(x);
}
